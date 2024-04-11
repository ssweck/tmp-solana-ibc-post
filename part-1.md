# Creating the Solana IBC Bridge

Solana’s speed has been at the forefront of the blockchain’s design.  The [Solana white paper](https://solana.com/solana-whitepaper.pdf) talks about sub-second finality times in its abstract and the [Solana website](https://solana.com/) advertises a 400-millisecond block time.

To achieve such impressive speeds, the blockchain had to introduce various limits ranging from about a kilobyte transaction size limit through maximum account size to a relatively small heap during smart contract execution.  For a majority of programs on the blockchain, those limits aren’t a problem.  For example, an NFT contract needs only a couple hundred bytes of transaction data and fits easily within the ‘relatively small’ heap.

Implementing [the Inter-Blockchain Communication (IBC) protocol](https://www.ibcprotocol.dev/) is however not a trivial task.  With all the encapsulation, block header signatures, state proofs etc. that the IBC core needs to handle, the contract can easily surpass those limits.  In this post, I go through some of the work we had to do to overcome various challenges and successfully bring IBC onto Solana.

# The Guest blockchain and scope of the present article

Fist of all, Solana doesn’t meet each of IBC’s host requirements listed in the [ICS 24 document](https://github.com/cosmos/ibc/blob/main/spec/core/ics-024-host-requirements/README.md).  Specifically, it offers neither state proofs nor introspection.  The former is required to create membership and non-membership proofs.  The latter is needed to perform an IBC handshake when establishing an IBC connection.  This is why we’ve ended up creating [the guest blockchain](https://docs.picasso.network/technology/ibc/solana/#ibc-requirements--the-need-for-a-guest-blockchain) which runs atop Solana.  While an interesting topic by itself, this post is not about the guest blockchain, as it has already [been detailed elsewhere](https://research.composable.finance/t/crossing-the-cross-blockchain-interoperability-chasm/33).

Instead, this post describes the technical difficulties of a complex smart contract on Solana.  IBC is as complex as it gets.  This is especially true when considering IBC originated as a standard within [the Cosmos ecosystem](https://cosmos.network/).  Many of the design constraints of the standard which make sense for Cosmos introduce challenges when working with a completely different ledger like Solana.

In fact, because the topic is so long, this post is split into two parts.  This one touches on memory management and the next one will touch on transaction size limit.

# Logging

Quite early in our development process, we ran into memory problems.  32 KiB may have been enough to code Super Mario Bros., but nowadays, a heap this size is quite limiting.  This is especially true when using frameworks not necessarily designed with such a limit in mind.

When writing software, a common quick way to troubleshoot issues is to add some logging.  Logs offer some visibility into a program’s internal state, alleviating the need to use debuggers.  Beware—in Solana, logging is a trap.

Solana smart contracts can generate messages via [`solana_program::msg` macro](https://docs.rs/solana-program/latest/solana_program/macro.msg.html).  It supports normal Rust formatting but its behaviour is radically different depending on the number of arguments passed to it.  When invoked with a single argument, it is logged directly with no formatting; otherwise arguments are passed to Rust’s `format` macro and the result is logged.  This means that the following code won’t do what one might expect:


```rust
let name = "Mark";
solana_program::msg!("Oh, hi {name}.");
```

That’s not the part that is a trap.

The default Solana allocator (the one declared by [Solana’s `entrypoint`](https://docs.rs/solana-program/latest/solana_program/macro.entrypoint.html) or [Anchor’s `program`](https://docs.rs/anchor-lang/latest/anchor_lang/attr.program.html) macro) doesn’t free memory.  When logging a formatted message, the text is allocated on the heap and that memory is lost.  When working at the edge of the heap size limit, one should therefore fight the urge to log large formatted messages.


## Anchor events

As an aside, we’ve also faced allocation failures when using Anchor’s event emitting infrastructure.  The problem turned out to be unnecessary temporary buffers which leak memory.

In the end, even though we’re using Anchor for our Solana IBC implementation, we’re using a simpler event format with a single `Event` enum and straightforward Borsh serialisation.

Eventually [my improvement to memory usage](https://github.com/coral-xyz/anchor/pull/2691) was merged into Anchor¹, but at that point we’d already moved on and Solana IBC continues to uses plain Borsh serialisation.


# Custom allocator

While it feels repulsive to leak memory, that behaviour is not a bug; it’s a feature that makes sense in the context of Solana.  Smart contract execution is often short and rarely uses anywhere close to 32 KiB of heap space.  Once the program terminates, all the resources are freed, so there’s no harm in temporary ‘wastage’.  It’s not unreasonable for a platform which puts speed at the forefront to opt for a fast allocator even if it leaks memory.

Specifically, Solana went with [a bump allocator](https://docs.rs/solana-program/latest/solana_program/entrypoint/struct.BumpAllocator.html) which maintains just two pointers: one to the start of heap and the other to the end of unallocated space.  Each allocation request is served from the end of the region and updates the end pointer.  Deallocations are simply ignored.

For cases where a more sophisticated memory management strategy is necessary, Solana respects Rust’s way of defining allocators.  For example, the code below adds *some* intelligence to the bump allocator.  While it makes the allocator consume marginally more computation time, it does handle some cases of memory deallocation.  Depending on the use case, it may be sufficient to get a smart contract working.

```rust
#[cfg(all(target_os = "solana", not(feature = "no-entrypoint")))]
mod alloc {
    use solana_program::entrypoint::{HEAP_LENGTH, HEAP_START_ADDRESS};

    #[global_allocator]
    static ALLOC: BumpAllocator = BumpAllocator;

    /// The bump allocator with opportunistic freeing.
    struct BumpAllocator;

    unsafe impl core::alloc::GlobalAlloc for BumpAllocator {
        unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
            // Read stored address of end of free region or initialise to
            // the end of heap if this is the first time we’re called.
            let mut addr = self.free_end().unwrap_or(self.heap_end());

            // Reserve the memory from the end of the unallocated region.
            addr = addr.saturating_sub(layout.size());
            addr &= !(layout.align().wrapping_sub(1));

            if addr < self.free_start() {
                core::ptr::null_mut()
            } else {
                self.set_free_end(addr);
                addr as *mut u8
            }
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
            let ptr = ptr as usize;
            let end = self.free_end().unwrap_or(0);
            if cfg!(debug_assertions) {
                if end as usize == 0 {
                    panic!("freeing {ptr:?} from uninitialised allocator");
                } else ptr < self.free_start() || ptr >= self.heap_end() {
                    panic!("freeing {ptr:?} from outside of heap");
                } else if ptr < self.free_end() {
                    panic!("double free of {ptr:?}");
                } else if ptr.saturating_add(layout.size()) > self.free_end() {
                    panic!("region at {ptr:?} of size {} overflows heap",
                            layout.size());
                }
            }
            // Free the memory if the allocation is adjacent to the unallocated
            // range.  This will handle freeing the last performed allocation as
            // well as freeing memory in LIFO order so long as each allocation
            // size matches its alignment.  If we cannot perform the match than
            // just leak memory.
            if ptr == end {
                self.set_free_end(ptr + layout.size());
            }
        }
    }

    impl BumpAllocator {
        /// Returns address of the start of the free memory range.
        const fn free_start(&self) -> usize {
            // We’re storing end pointer at the beginning of heap so the actual
            // start of the heap is HEAP_START_ADDRESS + sizeof(end).
            HEAP_START_ADDRESS as usize + core::mem::size_of::<usize>()
        }

        /// Returns address of the end of the free memory range or None if we
        /// have’t been initialised yet.
        fn free_end(&self) -> Option<usize> {
            // SAFETY: On Solana location at address HEAP_START_ADDRESS is
            // guaranteed to be zero-initialised and aligned to 4 GiB.
            let addr = unsafe { *(HEAP_START_ADDRESS as *const usize) };
            (addr != 0).then_some(addr)
        }

        /// Sets address of the end of the free memory range.
        fn set_free_end(&self, addr: usize) -> usize {
            debug_assert_ne!(0, addr);
            // SAFETY: On Solana location at address HEAP_START_ADDRESS is
            // guaranteed to be zero-initialised, aligned to 4 GiB and writable.
            unsafe { *(HEAP_START_ADDRESS as *mut usize) = addr }
        }

        /// Returns address of the end of the heap.
        const fn heap_end(&self) -> usize {
            HEAP_START_ADDRESS as usize + HEAP_LENGTH
        }
    }
}
```

(Implementation of `realloc` is left as an exercise to the reader).

Note that the `solana_program::entrypoint` and `anchor_lang::program` macros declare global allocator as well.  Pasting the above code fragment into a typical Solana contract will likely cause compilation failure due to duplicate allocator definition.  To fix that, the `custom-heap` Cargo feature needs to be enabled in a program’s crate.  The following snippet included in the project’s `Cargo.toml` file does that:

```toml
[features]
default = ["custom-heap"]
custom-heap = []
no-entrypoint = []
```


# Increased heap size

In the end, a naïve opportunistic deallocation algorithm as presented above wasn’t sufficient for Solana IBC.  We had to bring in the big guns, i.e. [`ComputeBudgetInstruction::RequestHeapFrame`](https://docs.rs/solana-sdk/latest/solana_sdk/compute_budget/enum.ComputeBudgetInstruction.html#variant.RequestHeapFrame).

The initial instructions of a Solana transaction may call the [Compute Budget program](https://solana.com/docs/core/runtime#compute-budget).  They act as a configuration of the limits taking effect while execution of the smart contracts is called in that transaction.  `RequestHeapFrame` is exactly what the doctor ordered for one with higher heap size requirements.

Consider the following Solana program:

```rust
solana_program::entrypoint!(process_instruction);
pub fn process_instruction(
    program_id: &solana_program::pubkey::Pubkey,
    accounts: &[solana_program::account_info::AccountInfo],
    instruction_data: &[u8],
) -> solana_program::entrypoint::ProgramResult {
    let _ = alloc::vec::Vec::with_capacity(40_000);
    Ok(())
}
```

What this does is allocate a 40 KB buffer, which is larger than the default heap size.  Therefore, executing it in a transaction fails.  However, when executing a transaction consisting of two instructions, the first calling the Compute Budget program with `RequestHeapFrame(102400)` operation and the second calling the above test program, the program… fails just as before.

Even though a higher heap is requested, the Solana program will have access to the first 32 KiB only.  Well, sort of.  It turns out the default allocator *assumes* that the heap is 32 KiB.  Even though the virtual machine allots more space, [the default allocator will use the first
32 KiB only](https://docs.rs/solana-program/1.18.9/src/solana_program/entrypoint.rs.html#168).  In the `BumpAllocator` presented above, this corresponds to the use of the `HEAP_LENGTH` constant.


## <a name="getting-heap-size"></a> Getting heap size

Eliminating the hard-coded heap size shouldn’t be a big problem.  Right?  One would hope to simply figure out the size of the heap and use that in the allocator instead of assuming the `HEAP_LENGTH` constant.  In their infinite wisdom, Solana maintainers [decided not to offer a syscall to get that information](https://github.com/solana-labs/solana/issues/32607#issuecomment-1818049307).  Instead, the smart contract author is expected to use [instruction introspection](https://docs.solanalabs.com/implemented-proposals/instruction_introspection) to find the instruction with the `RequestHeapFrame` call and get the heap size from that.

For this purpose, instruction introspection in Solana would work as follows:
1. The caller of the smart contract (i.e. the sender of the transaction), includes [the Instructions SysVar](https://docs.solanalabs.com/runtime/sysvars#instructions) account in the instruction, invoking it to the smart contract.
2. The smart contract identifies that account in the set of accounts it has been given.
3. The smart contract iterates over instructions to look for a call to the Compute Budget program.
4. Once this is found, the smart contract parses the instruction data of the call to extract the `RequestHeapFrame` instruction and the heap size located there.

A seasoned Solana developer will recognise this pattern.  While this is annoying (and also breaks the contract’s ABI - but let’s ignore that), it is doable.

Except to initialise the allocator, all of this has to be done without making any allocations.  This means `solana_program::entrypoint` cannot be used (since it allocates a vector of `AccountInfo` objects).  Neither can [`load_instruction_at_checked`](https://docs.rs/solana-program/1.18.9/solana_program/sysvar/instructions/fn.load_instruction_at_checked.html) (since it copies instruction into a vector).  To get the size of the heap, a smart contract author needs to implement:
1. the `entrypoint` function directly,
2. parsing of the account data of the Instructions SysVar and
3. parsing of the calls to the Compute Budget program.

All that with zero help from the `solana_program` crate, since all provided functions which deal with that data perform allocations.  Only a masochist would do something like that.

[And so I went ahead and did it.](https://gist.github.com/mina86/377bcae147aec1dfb0ad127b3f82e191) Sadly, I’m now a *Senior* Software Engineer.  While it doesn’t grant me reduced fares in public transport, it apparently means I have to think about the long-term health of a project rather than just writing fun wacky code.  In the end, we ended up with a simpler solution.


## Heap-size ‘aware’ allocator

The solution is to switch the bump allocator implementation from allocating memory from the end of the heap (which requires a priori knowledge of the size of the heap) to one which allocates memory from the start of the heap.²

How would the allocator know if there’s enough free space left on the heap?  Well…

```rust
#[cfg(all(target_os = "solana", not(feature = "no-entrypoint")))]
mod alloc {
    use solana_program::entrypoint::HEAP_START_ADDRESS;

    #[global_allocator]
    static ALLOC: BumpAllocator = BumpAllocator;

    /// The bump allocator with opportunistic freeing which works with increased
    /// heap size.
    struct BumpAllocator;

    unsafe impl core::alloc::GlobalAlloc for BumpAllocator {
        unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
            let mut addr = self.free_start().unwrap_or(self.heap_start());

            // Align up
            let mask = layout.align() - 1;
            let addr = match addr.checked_add(mask) {
                None => return core::ptr::null_mut(),
                Some(addr) => addr & !mask,
            };
            let end = match addr.checked_add(layout.size()) {
                None => return core::ptr::null_mut();
                Some(end) => end,
            };

            // Check if we have enough free space left on heap.
            // SAFETY: This is unsound but it will only execute on Solana
            // where accessing memory beyond heap results in segfault which
            // is what we want.
            let _ = unsafe { ((end - 1) as *mut u8).read_volatile() };

            self.set_free_start(end);
            addr as *mut u8
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
            // Left as excercise to the read.
            // Or just leave empty.
        }
    }

    impl BumpAllocator {
        /// Returns address of the end of the heap excluding region at the start
        /// reserved for the allocator.
        const fn heap_start(&self) -> usize {
            // We’re storing end pointer at the beginning of heap so the actual
            // start of the heap is HEAP_START_ADDRESS + sizeof(end).
            HEAP_START_ADDRESS as usize + core::mem::size_of::<usize>()
        }

        /// Returns address of the start of the free memory range or None if we
        /// haven’t been initialised yet.
        fn free_start(&self) -> Option<usize> {
            // SAFETY: On Solana location at address HEAP_START_ADDRESS is
            // guaranteed to be zero-initialised and aligned to 4 GiB.
            let addr = unsafe { *(HEAP_START_ADDRESS as *const usize) };
            (addr != 0).then_some(addr)
        }

        /// Sets address of the end of the free memory range.
        fn set_free_start(&self, addr: usize) -> usize {
            // SAFETY: On Solana location at address HEAP_START_ADDRESS is
            // guaranteed to be zero-initialised, aligned to 4 GiB and writable.
            unsafe { *(HEAP_START_ADDRESS as *mut usize) = addr }
        }
    }
}
```

Yes.  The idea is that on each allocation, the allocator tries to read the last byte of the block.  If there’s enough space on the heap, the read succeeds.  If there isn’t, the program segfaults.

While this is hardly a clean solution, the Solana runtime will handle the segfault gracefully so there’s no need to worry about catastrophic failures.  Unless Solana offers a syscall for getting the heap size, this is actually the cleanest solution to the problem.


# Global state

Another problem we had to face is [Solana’s lack of support for mutable global variables](https://solana.com/docs/programs/limitations#static-writable-data).  Any `static mut` variables or `static` variables with interior mutability cause Solana smart contracts to fail to compile.  We’ve run into this issue twice.

The first time was fairly straightforward to address.  Through a few levels of indirect dependencies, Solana IBC pulls in the `tendermint` crate, which enabled `flex-error`’s feature which included the mutable `HOOK` global variable.  Long story short, [one pull request to `tendermint-rs` later](https://github.com/informalsystems/tendermint-rs/pull/1371) and this is now resolved.

## Signature verification done in transaction

The second time this problem arose was related to signature verification.  The Solana contract runtime is Turing complete so it’s possible to compile cryptography functions into the Solana program.  However, executing them is a sure way to run out of compute units.  The proper way to verify Ed25519 signatures is to call the [Ed25519 native program](https://docs.solanalabs.com/runtime/programs#ed25519-program).  This cannot be done via Cross-Program Invocation (CPI), a mechanism where one smart contract can call another.  Instead the call is done by the sender of the transaction as described [above in ‘Getting heap size’ section](#getting-heap-size).  Specifically:

1. The sender of the transaction includes multiple instructions in the transaction.  One of them is call to the Ed25519 program, requesting verification of the signatures.  Some later instruction calls the smart contract that the client is actually interested in calling.

2. Further, when calling the smart contract, the sender includes the Instructions SysVar account in the instruction invoking to the smart contract.

3. The smart contract grabs the Instructions account and uses it to search through the previous instructions in the transaction to look for a call to the Ed25519 program.

4. Once this is located, the smart contract parses the instruction sent to the Ed25519 program to verify that the signatures it cares about have been verified.

Importantly, to perform the verification, the code needs the Instructions account.  Unfortunately, a Tendermint light client effectively assumes that signature verification code is stateless (specifically the assumption is in [`Verifier` trait](https://docs.rs/tendermint/0.34.1/tendermint/crypto/signature/trait.Verifier.html)).  There’s no way to pass that Instructions account down to the place where the light client needs to perform the verification.

The obvious solution is to use global variables: you figure out the data needed for signature verification at the start of the smart contract, save it in a static variable and add custom `Verifier` implementation which accesses that global state.  Except, of course, this is not possible on Solana because a mutable global state is not allowed.  Fortunately, since we’ve already used our own global allocator, the solution to this problem turned out to be relatively simple.

## Using a global allocator to store a mutable global state

We didn’t have to worry about external libraries declaring mutable global variables.  We know exactly what kind of state we need to keep and how large it is.  Since we control heap allocations, we simply reserve a portion of the heap for any mutable global object we need.

The allocator was already doing this with its own state.  Extending that mechanism to hold more arbitrary data was relatively simple.  Since we didn’t want to hard-code things, we’ve implemented the feature by adding a generic argument to the `BumpAllocator` we were using.  In effect, we had something like:

```rust
#[cfg(all(target_os = "solana", not(feature = "no-entrypoint")))]
mod alloc {
    use solana_program::entrypoint::{HEAP_LENGTH, HEAP_START_ADDRESS};

    pub(super) struct BumpAllocator<G> {
        _ph: core::marker::PhantomData<G>,
    }

    struct Header<G = ()> {
        end_addr: core::cell::Cell<usize>,
        global: G,
    }

    impl<G: bytemuck::Zeroable> BumpAllocator<G> {
        /// Returns reference to global state `G` reserved on the heap.
        ///
        /// This is meant as a poor man’s mutable statics which are not
        /// supported on Solana.  With it, one may use a `Cell<T>` as global
        /// state and access it from different parts of Solana program.
        pub fn global(&self) -> &G { &self.header().global }
    }

    unsafe<G> impl core::alloc::GlobalAlloc for BumpAllocator<G> {
        /* ... implementation as before ... */
    }

    impl<G: bytemuck::Zeroable> BumpAllocator<G> {
        /// Returns address of the end of the heap excluding region at the start
        /// reserved for the allocator.
        const fn heap_start(&self) -> usize {
            // We’re storing end pointer at the beginning of heap so the actual
            // start of the heap is offset by the header we’re using.
            HEAP_START_ADDRESS as usize + core::mem::size_of::<Header<G>>()
        }

        fn header(&self) -> &Header<G> {
            assert!(core::mem::size_of::<Header<G>>() <= HEAP_LENGTH);
            // SAFETY: Firstly, on Solana location at address HEAP_START_ADDRESS
            // is guaranteed to be at least HEAP_LENGTH-byte long, aligned to 4
            // GiB, writeable.  Secondly, all-zero bits represents valid value
            // of Header<G> since Cell<usize> and G are both bytemuck::Zeroable.
            unsafe { &*(HEAP_START_ADDRESS as *const Header<G>) }
        }

        /// Returns address of the start of the free memory range or None if we
        /// haven’t been initialised yet.
        fn free_start(&self) -> Option<usize> {
            let addr = self.header().end_pos.get();
            (addr != 0).then_some(addr)
        }

        /// Sets address of the end of the free memory range.
        fn set_free_start(&self, addr: usize) -> usize {
            self.header().end_pos.set(addr)
        }
    }
}
```

To take advantage of this new feature of the allocator, a user needs to define a [zeroable](https://docs.rs/bytemuck/latest/bytemuck/trait.Zeroable.html) type with a static lifetime.  Primitive types as well as an `Option<&'static T>` fit that description.  [`Box::leak`](https://doc.rust-lang.org/alloc/boxed/struct.Box.html#method.leak) can be used to obtain a static reference.  Lastly, to make the global state mutable, the values can be wrapped in a [`Cell`](https://doc.rust-lang.org/core/cell/struct.Cell.html).  All of that looks something like:

```rust
#[cfg(all(target_os = "solana", not(feature = "no-entrypoint")))]
mod global_alloc {
    use core::cell::Cell;

    struct Verifier { /* ... */ }

    #[derive(bytemuck::Zeroable)]
    struct Global {
        verifier: Cell<Option<&'static Verifier>>,
    }

    // SAFETY: Solana is single-threaded so we don’t need to worry about thread
    // safety.  Note that this is build when target_os = "solana" only.
    unsafe impl core::marker::Sync for Global {}

    #[global_allocator]
    static ALLOCATOR: alloc::BumpAllocator<Global> =
        alloc::BumpAllocator { _ph: core::marker::PhantomData };

    pub(super) fn global_verifier() -> Option<&'static Verifier> {
        ALLOCATOR.global().verifier.get()
    }

    pub(super) fn set_global_verifier(verifier: Verifier) {
        let verifier = Box::leak(Box::new(verifier));
        ALLOCATOR.global().verifier.set(verifier);
    }
}

use global_alloc::{global_verifier, set_global_verifier};
```

Since the Solana runtime is single-threaded, no consideration for thread-safety is necessary.  Paradoxically, this may make things more complicated by forcing another version of the code for non-Solana builds (e.g. tests).  Another aspect which makes things interesting is Solana’s lack of support for atomic operations (e.g. [`AtomicPtr` type](https://doc.rust-lang.org/core/sync/atomic/struct.AtomicPtr.html)).  The mere existence of them in the smart contract, even if they are dead code, causes the smart contract to fail validation before uploading to the blockchain.

Fortunately, all of this can be ignored if the global state isn’t used by any of the unit tests or code exposed to reverse dependencies (e.g. when some crate depends on us to facilitate CPI).  [This is our approach](https://github.com/ComposableFi/emulated-light-client/blob/master/solana/solana-ibc/programs/solana-ibc/src/allocator.rs) with code panicking when trying to access the global state in unit tests when code was built as part of another smart contract.

[Code of the allocator can be found in our repository](https://github.com/ComposableFi/emulated-light-client/tree/master/solana/allocator).  It’s a separate crate, which makes it easy to be incorporated in other Solana programs.  It is a bit different from the implementation presented above in that it tracks pointer provenance, improving test coverage when verifying with Miri.

# Conclusion



________________

¹ There’s still some memory ‘wasted’ each time event is emitted.  But, now it’s usually just 257 bytes rather than over 1 KB.

² It’s perhaps worth noting that bump allocators are more efficient if they hand out blocks from the end rather than front.  The difference is minuscule but the alignment calculation is simpler when rounding down rather than rounding up.

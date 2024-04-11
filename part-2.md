[The previous post](XXX) described complications we’ve faced when dealing with memory management in the smart contract.  That wasn’t the end of problems that Solana has thrown at us.  This post continues the story and picks up with issues rising from the limitations of the Solana transaction size.


# <a name="sigverify"></a> Limit on number of signature verifications

While using global state is not the cleanest approach, it gets the job done.  Indeed, when all we need is to verify a single signature, the aforementioned approach is completely sufficient.  However, Solana always finds a way to make things… engaging.

Solana transactions are limited to 1232 bytes¹. Since signature verification is performed through an instruction present in the transaction, it eats up that limit.  This becomes a problem when trying to check multiple signatures in a single transaction.  In an optimistic case where multiple signers signed the same 32-byte message or a single signer signed multiple 32-byte messages, there’s space for only ten signature checks.²  And, the optimistic case is not what usually happens.  In Tendermint, each validator signs a different message (one which includes their timestsamp), which brings the number down to eight.  This isn’t exactly workable for light clients which need to verify signatures from dozens of validators.

To combat this problem, we’ve developed a process we came to refer to as ‘chunking’.³ Rather than verifying all the signatures in a single transaction, we’ve written a helper contract called `sigverify` which is called multiple times with batches of signatures.  It aggregates information about all the valid signatures it witnesses, storing them in a Solana account.  That account can be passed to the smart contract which needs to check all the signatures.

The account is owned by the `sigverify` program, thus only it can add new entries.  This guarantees that no malicious actor can inject invalid signature into the data.  It’s also tied to the sender of the transaction such that only they can modify it.  This prevents DoS attacks where an adversary may try to fill the account with junk signatures, increasing the verification count.

The process of verifying therefore becomes as follows:
1. Divide signatures to verify in groups of seven.
2. For each group, send a Solana transaction which calls the Ed25519 program and then our `sigverify` program.  The `sigverify` will look at all the verified signatures and store the commitment that it witnessed them in a new account.
3. Once all signatures are verified, call the final smart contract, passing to it the account `sigverify` created.
4. Finally, call `sigverify` to free up the account.  (The caller pays for storage of the account, so freeing the account recovers the tokens spent on storage rent).

At the moment the implementation works with Ed25519 signatures only but adding Secp256k1 signatures can be trivially done as well.  Just like all the other Solana IBC code, this contract is [available in our repository](https://github.com/ComposableFi/emulated-light-client/tree/master/solana/signature-verifier).


## Aside: calling an Ed25519 native program with multiple signatures

By the way, isn’t it fun that Solana provides *no* high level interface for interacting with an Ed25519 program?  Sure, there’s the [`new_ed25519_instruction`](https://docs.rs/solana-sdk/latest/solana_sdk/ed25519_instruction/fn.new_ed25519_instruction.html) function, but it accepts just a single signature, not to mention that it expects the private key pair as an argument.  This is a quite useless interface except in situations where the sender of the transaction is the one signing the message as well.  It’s not only that there’s no high-level interface either.  The binary format of the instruction data [is documented](https://docs.solanalabs.com/runtime/programs#ed25519-program) but for whatever reason the types are exposed in neither `solana-program` nor `solana-sdk`.

All in all, anyone who needs to a) call an Ed25519 native program with more than one signature, b) call it to verify a signature someone else has made or c) verify (inside of smart contract they develop) that the signature has been verified, has to copy the `Ed25519SignatureOffsets` and implement binary manipulation code by themselves.

To fix those shortcomings we had to develop our own code handling all the things that `solana-program` should offer.  This is packaged in [a nice module](https://github.com/ComposableFi/emulated-light-client/blob/master/solana/signature-verifier/src/ed25519_program.rs) to make usage as painless as possible.

# Instruction data limit

This brings the story to the payload size limit.  As aforementioned, a Solana transaction is limited to 1232 bytes.  This needs to be enough to store the sender’s signature, the smart contract address and all account information passed to the smart contract, as well as the call’s instruction data (i.e. the request passed to the smart contract).  The overhead may be reduced with [versioned transactions](https://solanacookbook.com/guides/versioned-transactions.html) but, no matter what, instruction data is limited to around 1100 bytes.  For simple contracts this is enough, but when implementing IBC we need to handle requests which are much larger.

For example, messages sent to update Tendermint’s light client store validator signatures.  As discussed previously, such a signature is over a hundred bytes, and with multiple signatures present in the request, the transaction size limit is quickly reached.

The solution we used for this is analogous to how we handled the signatures.  We’ve created [a helper `write-account` program](https://github.com/ComposableFi/emulated-light-client/tree/master/solana/write-account) which allows arbitrary data to be written to an account.  If a caller needs to pass instruction data which doesn’t fit in the Solana transaction, they can split it into chunks⁴ and send each to Solana.  Once all data is written, the smart contract can be called with instruction data passed in the account.

With a helper interface, the whole process becomes quite simple, and on the client side boils down to straightforward loop:

```rust
let (mut chunks, chunk_account, _) = write::instruction::WriteIter::new(
    &write_account_program_id,
    authority.pubkey(),
    WRITE_ACCOUNT_SEED,
    instruction_data,
)
.unwrap();
for instruction in &mut chunks {
    let transaction = Transaction::new_signed_with_payer(
        &[instruction],
        Some(&authority.pubkey()),
        &[&*authority],
        blockhash,
    );
    let sig = sol_rpc_client
        .send_and_confirm_transaction_with_spinner(&transaction)
        .unwrap();
}
let (write_account, write_account_bump) = chunks.into_account();
```

`write_account` is the address of the the PDA which holds the instruction data.  The account is passed to the smart contract which the caller actually cares about and the smart contract can read the request from there.

Just like with our [`sigverify` program](#sigverify), the account is tied to the sender and only they can modify their contents.  This guarantees that others cannot modify the instruction sent to the smart contract and caller has full control over it.  Similarly, sender of the transaction pays for the storage and can call the `write-account` program to free the account once everything is said and done.  Or, it can reuse the account in the future.


## Reading instruction data from an account

Unfortunately, this feature cannot be made fully transparent to the smart contract.  The Solana runtime is, after all, unaware of our `write-account` program.  The smart contract needs to have explicit support for reading the request from an account rather than the transaction’s payload.

One solution is to always expect data in an account.  This would work but is inflexible.  If the request is small, there is no benefit in using `write-account` over passing the data inside of the transaction.

A better approach is to conditionally read the data either from the instruction or from the account depending how the contract is called.  For example, if the instruction data is empty, read the request from the last account passed to the smart contract call like so:

```rust
/// Solana smart contract entrypoint.
///
/// We’re using a custom entrypoint which has special handling for instruction
/// data account.  See [`get_ix_data`] function.
///
/// # Safety
///
/// Must be called with pointer to properly serialised instruction such as done
/// by the Solana runtime.  See [`solana_program::entrypoint::deserialize`].
#[cfg(not(feature = "no-entrypoint"))]
#[no_mangle]
pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
    let (program_id, mut accounts, mut instruction_data) =
        unsafe { solana_program::entrypoint::deserialize(input) };

    // If instruction data is empty, the actual instruction data comes from the
    // last account passed in the call.
    if instruction_data.is_empty() {
        match get_ix_data(&mut accounts) {
            Ok(data) => instruction_data = data,
            Err(err) => return err.into(),
        }
    }

    match entry(program_id, &accounts, instruction_data) {
        Ok(()) => solana_program::entrypoint::SUCCESS,
        Err(error) => error.into(),
    }
}

/// Interprets data in the last account as instruction data.
fn get_ix_data<'a>(
    accounts: &mut Vec<solana_program::account_info::AccountInfo<'a>>,
) -> Result<&'a [u8], ProgramError> {
    let account = accounts.pop().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let data = alloc::rc::Rc::try_unwrap(account.data).ok().unwrap();
    let (len, data) = stdx::split_at::<4, _>(data.into_inner())
        .ok_or(ProgramError::InvalidInstructionData)?;
    let len = usize::try_from(u32::from_le_bytes(*len))
        .map_err(|_| ProgramError::ArithmeticOverflow)?;
    data.get(..len).ok_or(ProgramError::InvalidInstructionData)
}

/// The actual entrypoint of the smart contract.
fn entry(
    program_id: &solana_program::pubkey::Pubkey,
    accounts: &[solana_program::account_info::AccountInfo],
    instruction_data: &[u8]
) -> solana_program::entrypoint::ProgramResult {
    /* ... */
}

#[cfg(not(feature = "no-entrypoint"))]
solana_program::custom_heap_default!();

#[cfg(not(feature = "no-entrypoint"))]
solana_program::custom_panic_default!();
```

Since this defines the `entrypoint` function Solana expects, [Solana’s `entrypoint` macro](https://docs.rs/solana-program/latest/solana_program/macro.entrypoint.html) cannot be used.  Including both would result in name collision.  This isn’t an issue except that now it’s necessary to remember to also declare global allocator (which we were doing anyway) and panic handler.  As per documentation of the macro, those two things can be done with `custom_heap_default` and `custom_panic_deauflt` macros.


## `entrypoint` and Anchor

This got slightly more complicated in our case because we are using the Anchor framework.  The framework provides a lot of abstractions which are hard to break through when necessary.  The [`anchor_lang::program` macro](https://docs.rs/anchor-lang/latest/anchor_lang/attr.program.html) processes a module implementing all the supported instruction as well as defining the `entrypoint` function.  Once again, this leads to conflict with the function we’ve defined.  Unfortunately, with Anchor, there’s no reliable way to tell it not to introduce that function.  We’ve ended up [forking Anchor](https://github.com/mina86/anchor/tree/custom-entrypoint) with [a change](https://github.com/coral-xyz/anchor/commit/788c61c2d72aad374457d7619d8fe37d6ac2c0e9) which introduces support for a new `custom-entrypoint` Cargo feature:

```diff
diff --git a/lang/syn/src/codegen/program/entry.rs b/lang/syn/src/codegen/program/entry.rs
index 4b04da23..093b1813 100644
--- a/lang/syn/src/codegen/program/entry.rs
+++ b/lang/syn/src/codegen/program/entry.rs
@@ -9,7 +9,7 @@ pub fn generate(program: &Program) -> proc_macro2::TokenStream {
         Err(anchor_lang::error::ErrorCode::InstructionMissing.into())
     });
     quote! {
-        #[cfg(not(feature = "no-entrypoint"))]
+        #[cfg(not(any(feature = "no-entrypoint", feature = "custom-entrypoint")))]
         anchor_lang::solana_program::entrypoint!(entry);
         /// The Anchor codegen exposes a programming model where a user defines
         /// a set of methods inside of a `#[program]` module in a way similar

```

Like `custom-heap`, it needs to be enabled in the `Cargo.toml` of the Solana program which wants to take advantage of it:

```toml
[features]
default = ["custom-entrypoint"]
custom-entrypoint = []
```

# Conclusion

We knew from the start that implementing IBC on Solana would be quite the undertaking.  Before any code had been written, we already had to design the concept of the guest blockchain to overcome Solana’s features limitations.  That turned out to be just the beginning of the journey.  Solana’s focus on speed introduces limitations in the runtime which bring another set of challenges.

Alas, where there’s a will, there’s a way.  We’ve persevered, and as we’re about to launch the Solana IBC bridge, we hope all the work will prove useful to our users who will now be able to trustlessly transfer tokens between Solana and other IBC chains.

________________

¹ For inquisitive readers, this number comes from IPv6 maximum transactional unit (MTU) size mandated to be at least 1280 bytes. The IPv6 header takes 40 of those bytes and the further eight are used by Solana protocol leaving 1232 for the transaction payload.

² `(1232 - 2 - 32) / (14 + 32 + 64) = 10.9`.  2 and 14 come from the overhead of the call to Ed25519 program, 32s are size of the message and public key and 64 is size of the signature.

³ For the record, I dislike the term but somehow we stuck with it.

⁴ Hence, the term ‘chunking’ was born.  Since chronologically we developed the `write-account` program before `sigverify`, we started referring to methods used in both of those programs as ‘chunking’.

module

public import EthLib.Execution.Evm.Delegation
public import EthLib.Execution.Evm.Gas
public import EthLib.Execution.State.Tracker
public import EthLib.Execution.Transactions.Signature

/-!
# `Transactions.Authorization`

The authorizations of a set code transaction, from Pectra.

Each authorization is signed by an account, its authority.

The authority agrees to run the code of an address.

The transaction applies its authorizations in order, before its message runs.

An authorization that fails a check is skipped, and the transaction goes on.

- Its chain is 0 or the chain of the block.
- Its nonce is below `2^64 - 1`.
- Its signature recovers an authority, with a low `s`.
- The authority has no code, or a delegation indicator.
- The nonce of the authority is the nonce of the authorization.

Once its signature recovers the authority, the authority is accessed, even if a later check fails.

A valid authorization sets the delegation indicator of the address as the code of the authority.

An authorization to the zero address clears that code instead.

Either way, the nonce of the authority grows by one.

The transaction paid 25000 for each authorization, as the price of a new account.

So an authority that already has an account gives back 12500 of it, through the refund counter.

[EIP-7702][eip7702] defines the list and its processing.

[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Cryptography.Secp256k1
open EthLib.Execution.Evm (delegationIndicator isValidDelegation)
open EthLib.Execution.Evm.GasCosts
open EthLib.Execution.State (StateError TransactionState)
open EthLib.Serialization.Rlp

/-- The byte before the encoding of an authorization in the hash that its authority signs. -/
def SET_CODE_TX_MAGIC : UInt8 := 0x05

/-- The address that clears the code of an authority: twenty zero bytes. -/
def NULL_ADDRESS : Address := Vector.replicate 20 0

/-- The hash that the authority of an authorization signs.

It is the Keccak-256 hash of `0x05`, then the encoding of the chain, the address and the nonce. -/
def authorizationHash (auth : Authorization) : Except RlpError Hash32 :=
  hashTypedItems SET_CODE_TX_MAGIC
    [Codec.toItem auth.chainId, Codec.toItem auth.address, Codec.toItem auth.nonce]

/-- The authority whose signature an authorization carries, or none for an invalid signature.

The parity is 0 or 1, `r` lies in `[1, n - 1]`, and `s` in `[1, n / 2]`. -/
def recoverAuthority (auth : Authorization) : Option Address :=
  if auth.yParity.toNat < 2 ∧ 0 < auth.r.toNat ∧ auth.r.toNat < Fn.modulus ∧
      0 < auth.s.toNat ∧ Ecdsa.isLowS auth.s.toNat then
    match authorizationHash auth with
    | .ok hash =>
      match Ecdsa.recover hash auth.r.toNat auth.s.toNat (Fin.ofNat 2 auth.yParity.toNat) with
      | .ok (.affine x y) => some (address x y)
      | _ => none
    | .error _ => none
  else none

/-- Whether an authorization names the chain `chainId` or every chain.

Its nonce must also be below 2^64 - 1. -/
def authorizationInScope (chainId : Nat) (auth : Authorization) : Bool :=
  (auth.chainId.toNat = 0 || auth.chainId.toNat = chainId) && auth.nonce.toNat < 2 ^ 64 - 1

/-- Whether the authority may take an authorization: its code and its nonce allow it.

Its code is empty or a delegation indicator, and its nonce is the nonce of the authorization. -/
def authorityAccepts (state : TransactionState) (authority : Address) (auth : Authorization) :
    Except StateError Bool := do
  let account := state.getAccount authority
  let code ← state.getCode account.codeHash
  return (code.size = 0 || isValidDelegation code) && account.nonce = auth.nonce.toNat

/-- The code that an authorization sets.

It is the delegation indicator, or no code for the zero address. -/
def delegationCode (auth : Authorization) : ByteArray :=
  if auth.address = NULL_ADDRESS then .empty else delegationIndicator auth.address

/-- The state after the authority takes a valid authorization at `fork`, and the refund.

The refund is 12500 for an authority that has an account, and 0 otherwise.

The steps of EIP-7702 refund an authority that is not empty.

[Its rationale][eip7702-refund] refunds one that already exists, as here.

They differ only for an empty account, which [EIP-7523][eip7523] forbids after the merge.

[eip7702-refund]: https://eips.ethereum.org/EIPS/eip-7702#charge-maximum-cost-upfront
[eip7523]: https://eips.ethereum.org/EIPS/eip-7523#specification -/
def delegate (fork : Fork) (state : TransactionState) (authority : Address)
    (auth : Authorization) : Except StateError (TransactionState × Nat) := do
  let refund := if state.accountExists authority then
    AUTH_PER_EMPTY_ACCOUNT - REFUND_AUTH_PER_EXISTING_ACCOUNT else 0
  let state ← state.setCode fork authority (delegationCode auth)
  let state ← state.incrementNonce fork authority
  return (state, refund)

/-- What the authorizations so far leave: the state, the accessed addresses and the refund. -/
structure Delegations where
  /-- The state after the valid authorizations so far. -/
  state : TransactionState
  /-- The accessed addresses, with each authority whose signature was recovered. -/
  accessed : Std.ExtTreeSet Address
  /-- The gas that the authorities with an account give back. -/
  refund : Nat

/-- The delegations after one more authorization, on the chain `chainId` at `fork`.

An authorization that fails a check leaves them as they were, except for the access. -/
def applyAuthorization (fork : Fork) (chainId : Nat) (done : Delegations)
    (auth : Authorization) : Except StateError Delegations :=
  if authorizationInScope chainId auth then
    match recoverAuthority auth with
    | some authority => do
      let done := { done with accessed := done.accessed.insert authority }
      if ← authorityAccepts done.state authority auth then
        let (state, refund) ← delegate fork done.state authority auth
        return { done with state, refund := done.refund + refund }
      else return done
    | none => .ok done
  else .ok done

/-- Apply the authorizations of a transaction in order, on the chain `chainId` at `fork`.

It starts from the state and the accessed addresses of the transaction, with no refund.

It fails only when the state lacks the code of an authority. -/
def applyAuthorizations (fork : Fork) (chainId : Nat) (state : TransactionState)
    (accessed : Std.ExtTreeSet Address) (auths : List Authorization) :
    Except StateError Delegations :=
  auths.foldlM (applyAuthorization fork chainId) ⟨state, accessed, 0⟩

end EthLib.Execution.Transactions

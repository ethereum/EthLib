module

public import EthLib.Execution.Evm.Delegation
public import EthLib.Execution.Evm.Frame
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

Up to BPO5, the transaction paid 25000 for each authorization, as the price of a new account.

So an authority that already has an account gives back 12500 of it, through the refund counter.

From Glamsterdam, the transaction paid only a base price for each authorization.

An accepted authorization then pays what it writes, from the gas of the first frame:

- 183600 state gas when the authority has no account;
- 9000 execution gas for the first write to the authority, unless the transaction paid it already;
- 35190 state gas for a new delegation indicator.

The last charge applies when the authority had no indicator at the start of the transaction.

It also needs that no earlier authorization set one for that authority.

There is no refund, and a lack of gas stops the authorizations.

The sender's first write is paid already.

So is the recipient's, when the transaction moves ether.

[EIP-7702][eip7702] defines the list and its processing.

[EIP-2780][eip2780], in Last Call, prices it from Glamsterdam.

Its state gas is that of [EIP-8037][eip8037], in Last Call.

[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
[eip2780]: https://eips.ethereum.org/EIPS/eip-2780#eip-7702-authorization-processing
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Cryptography.Secp256k1
open EthLib.Execution.Evm (EvmError GasMeter delegationIndicator isValidDelegation)
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

Up to BPO5, the refund is 12500 for an authority that has an account, and 0 otherwise.

The steps of EIP-7702 refund an authority that is not empty.

[Its rationale][eip7702-refund] refunds one that already exists, as here.

They differ only for an empty account, which [EIP-7523][eip7523] forbids after the merge.

From Glamsterdam, the refund is 0, since the intrinsic gas pays for no new account.

[eip7702-refund]: https://eips.ethereum.org/EIPS/eip-7702#charge-maximum-cost-upfront
[eip7523]: https://eips.ethereum.org/EIPS/eip-7523#specification -/
def delegate (fork : Fork) (state : TransactionState) (authority : Address)
    (auth : Authorization) : Except StateError (TransactionState × Nat) := do
  let refund := if fork < .glamsterdam ∧ state.accountExists authority then
    AUTH_PER_EMPTY_ACCOUNT - REFUND_AUTH_PER_EXISTING_ACCOUNT else 0
  let state ← state.setCode fork authority (delegationCode auth)
  let state ← state.incrementNonce fork authority
  return (state, refund)

/-- What the authorizations so far leave, with a gas meter of type `Meter`. -/
structure Delegations (Meter : Type) where
  /-- The state after the valid authorizations so far. -/
  state : TransactionState
  /-- The accessed addresses, with each authority whose signature was recovered. -/
  accessed : Std.ExtTreeSet Address
  /-- The gas that the authorities with an account give back. -/
  refund : Nat
  /-- The gas meter of the first frame, which pays the authorizations from Glamsterdam. -/
  meter : Meter
  /-- The accounts whose first write the transaction has paid. -/
  paidWrites : Std.ExtTreeSet Address
  /-- The authorities that an authorization so far gave a delegation indicator. -/
  delegated : Std.ExtTreeSet Address

variable {Meter : Type} [GasMeter Meter]

/-- The meter once an accepted authorization from `authority` pays, from Glamsterdam, or the error.

It pays state gas for a new account, then the first write, then state gas for a new indicator.

It runs before the authorization changes the state. -/
def chargeAuthorization (done : Delegations Meter) (authority : Address) (auth : Authorization) :
    Except EvmError Meter := do
  let meter ← if done.state.accountExists authority then pure done.meter
    else GasMeter.chargeState done.meter NEW_ACCOUNT_STATE_GAS
  let meter ← if authority ∈ done.paidWrites then pure meter
    else GasMeter.charge meter ACCOUNT_WRITE
  let before ← (done.state.getCode (done.state.getPreStateAccount authority).codeHash).mapError
    .state
  if auth.address ≠ NULL_ADDRESS ∧ !isValidDelegation before ∧ authority ∉ done.delegated then
    GasMeter.chargeState meter AUTH_BASE_STATE_GAS
  else pure meter

/-- The delegations once an accepted authorization from `authority` pays at `fork`, or the error.

Up to BPO5 it pays nothing here, since the intrinsic gas paid it.

From Glamsterdam it pays from the meter, and records the write as paid.

It also records the authority as delegated when the authorization sets a delegation indicator. -/
def payAuthorization (fork : Fork) (done : Delegations Meter) (authority : Address)
    (auth : Authorization) : Except EvmError (Delegations Meter) :=
  if fork ≥ .glamsterdam then do
    let meter ← chargeAuthorization done authority auth
    return { done with
      meter
      paidWrites := done.paidWrites.insert authority
      delegated := if auth.address ≠ NULL_ADDRESS then done.delegated.insert authority
        else done.delegated }
  else .ok done

/-- The delegations after one more authorization, on the chain `chainId` at `fork`.

An authorization that fails a check leaves them as they were, except for the access.

Once its signature gives an authority, the authority is read, for the list of EIP-7928.

From Glamsterdam, an authorization that lacks gas stops them with an error.

An error comes with the state so far, whose reads stay. -/
def applyAuthorization (fork : Fork) (chainId : Nat) (done : Delegations Meter)
    (auth : Authorization) : Except (EvmError × TransactionState) (Delegations Meter) :=
  if authorizationInScope chainId auth then
    match recoverAuthority auth with
    | some authority => do
      let done := { done with
        state := done.state.recordAccountRead authority
        accessed := done.accessed.insert authority }
      let halt (e : EvmError) := (e, done.state)
      if ← (authorityAccepts done.state authority auth).mapError (halt ∘ .state) then
        let done ← (payAuthorization fork done authority auth).mapError halt
        let (state, refund) ← (delegate fork done.state authority auth).mapError (halt ∘ .state)
        return { done with state, refund := done.refund + refund }
      else return done
    | none => .ok done
  else .ok done

/-- Apply the authorizations of a transaction in order, on the chain `chainId` at `fork`.

It starts from the state, the accesses, the meter and the paid writes of the transaction.

It starts with no refund.

It fails when the state lacks the code of an authority, and from Glamsterdam when gas lacks.

An error comes with the state so far, whose reads stay. -/
def applyAuthorizations (fork : Fork) (chainId : Nat) (state : TransactionState)
    (accessed : Std.ExtTreeSet Address) (meter : Meter) (paidWrites : Std.ExtTreeSet Address)
    (auths : List Authorization) : Except (EvmError × TransactionState) (Delegations Meter) :=
  auths.foldlM (applyAuthorization fork chainId) ⟨state, accessed, 0, meter, paidWrites, ∅⟩

end EthLib.Execution.Transactions

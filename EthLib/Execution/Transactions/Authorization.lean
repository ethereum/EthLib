module

public import EthLib.Execution.Evm.Delegation
public import EthLib.Execution.Evm.Machine.Frame
public import EthLib.Execution.Evm.Gas.Prices
public import EthLib.Execution.State.Tracker
public import EthLib.Execution.Transactions.Signature

/-!
# `Transactions.Authorization`

The authorizations of a set code transaction, from Pectra.

Each authorization is signed by an account, its authority.

The authority agrees to run the code of an address.

The transaction applies its authorizations in order, before its message runs.

An authorization that fails a check is skipped, and the transaction goes on.

The comments in the code mark each of the nine steps of EIP-7702.

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
  -- Step 3: `msg = keccak(MAGIC || rlp([chain_id, address, nonce]))`.
  hashTypedItems SET_CODE_TX_MAGIC
    [Codec.toItem auth.chainId, Codec.toItem auth.address, Codec.toItem auth.nonce]

/-- The authority whose signature an authorization carries, or none for an invalid signature.

The parity is 0 or 1, `r` lies in `[1, n - 1]`, and `s` in `[1, n / 2]`. -/
def recoverAuthority (auth : Authorization) : Option Address :=
  -- Step 3: "Verify `s` is less than or equal to `secp256k1n/2`, as specified in EIP-2".
  --
  -- The parity, the range of `r` and `0 < s` are bounds of `ecrecover` the EIP leaves implicit.
  if auth.yParity.toNat < 2 ∧ 0 < auth.r.toNat ∧ auth.r.toNat < Fn.modulus ∧
      0 < auth.s.toNat ∧ Ecdsa.isLowS auth.s.toNat then
    match authorizationHash auth with
    | .ok hash =>
      -- Step 3: `authority = ecrecover(msg, y_parity, r, s)`.
      match Ecdsa.recover hash auth.r.toNat auth.s.toNat (Fin.ofNat 2 auth.yParity.toNat) with
      | .ok (.affine x y) => some (address x y)
      | _ => none
    | .error _ => none
  else none

/-- Whether an authorization names the chain `chainId` or every chain.

Its nonce must also be below 2^64 - 1. -/
def authorizationInScope (chainId : Nat) (auth : Authorization) : Bool :=
  -- Step 1: "Verify the chain ID is 0 or the ID of the current chain."
  --
  -- Step 2: "Verify the `nonce` is less than `2**64 - 1`."
  (auth.chainId.toNat = 0 || auth.chainId.toNat = chainId) && auth.nonce.toNat < 2 ^ 64 - 1

/-- Whether the authority may take an authorization: its code and its nonce allow it.

Its code is empty or a delegation indicator, and its nonce is the nonce of the authorization. -/
def authorityAccepts (state : TransactionState) (authority : Address) (auth : Authorization) :
    Except StateError Bool := do
  let account := state.getAccount authority
  let code ← state.getCode account.codeHash
  -- Step 5: "Verify the code of `authority` is empty or already delegated."
  --
  -- Step 6: "Verify the nonce of `authority` is equal to `nonce`."
  return (code.size = 0 || isValidDelegation code) && account.nonce = auth.nonce.toNat

/-- The code that an authorization sets.

It is the delegation indicator, or no code for the zero address. -/
def delegationCode (auth : Authorization) : ByteArray :=
  -- Step 8: "If `address` is `0x0000000000000000000000000000000000000000`", clear the code.
  --
  -- Otherwise, `0xef0100 || address`.
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
  -- Step 7: "Add `PER_EMPTY_ACCOUNT_COST - PER_AUTH_BASE_COST` gas to the global refund counter".
  --
  -- Up to BPO5 only: from Glamsterdam, EIP-2780 drops the refund.
  --
  -- The EIP's condition is "if `authority` is not empty"; here it is that the authority exists.
  let refund := if fork < .glamsterdam ∧ state.accountExists authority then
    AUTH_PER_EMPTY_ACCOUNT - REFUND_AUTH_PER_EXISTING_ACCOUNT else 0
  -- Step 8: "Set the code of `authority` to be `0xef0100 || address`."
  --
  -- For the zero address, the code is cleared instead.
  let state ← state.setCode fork authority (delegationCode auth)
  -- Step 9: "Increase the nonce of `authority` by one."
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

It pays the charges of EIP-2780 that depend on the state.

It runs before the authorization changes the state. -/
def chargeAuthorization (done : Delegations Meter) (authority : Address) (auth : Authorization) :
    Except EvmError Meter := do
  -- EIP-2780: "if the authority account does not already exist", charge the new account leaf.
  --
  -- That charge is `STATE_BYTES_PER_NEW_ACCOUNT × CPSB` in state gas.
  let meter ← if done.state.accountExists authority then pure done.meter
    else GasMeter.chargeState done.meter NEW_ACCOUNT_STATE_GAS
  -- "if this is the first write to the authority within the transaction", charge `ACCOUNT_WRITE`.
  --
  -- "the charge is skipped when the write is already paid for", which the paid writes hold.
  let meter ← if authority ∈ done.paidWrites then pure meter
    else GasMeter.charge meter ACCOUNT_WRITE
  -- Whether "the authority had no delegation indicator at transaction start".
  let before ← (done.state.getCode (done.state.getPreStateAccount authority).codeHash).mapError
    .state
  -- "if the authorization sets a non-zero delegation target",
  --
  -- "the authority had no delegation indicator at transaction start",
  --
  -- "and no earlier authorization set one for that authority in this transaction":
  --
  -- charge `STATE_BYTES_PER_AUTH_BASE × CPSB` in state gas.
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
      -- Later writes are paid: the authority "was written by a preceding valid authorization".
      paidWrites := done.paidWrites.insert authority
      -- An "earlier authorization set one for that authority", for a nonzero address.
      delegated := if auth.address ≠ NULL_ADDRESS then done.delegated.insert authority
        else done.delegated }
  -- Before Glamsterdam, the intrinsic gas paid for the authorization.
  else .ok done

/-- The delegations after one more authorization, on the chain `chainId` at `fork`.

An authorization that fails a check leaves them as they were, except for the access.

Once its signature gives an authority, the authority is read, for the list of EIP-7928.

From Glamsterdam, an authorization that lacks gas stops them with an error.

An error comes with the state so far, whose reads stay. -/
def applyAuthorization (fork : Fork) (chainId : Nat) (done : Delegations Meter)
    (auth : Authorization) : Except (EvmError × TransactionState) (Delegations Meter) :=
  -- Steps 1 and 2.
  if authorizationInScope chainId auth then
    -- Step 3; a failed step 3 skips the tuple.
    match recoverAuthority auth with
    | some authority => do
      -- Step 4: "Add `authority` to `accessed_addresses`", and the read of EIP-7928.
      let done := { done with
        state := done.state.recordAccountRead authority
        accessed := done.accessed.insert authority }
      let halt (e : EvmError) := (e, done.state)
      -- Steps 5 and 6.
      if ← (authorityAccepts done.state authority auth).mapError (halt ∘ .state) then
        -- From Glamsterdam, EIP-2780 charges here.
        --
        -- Its charges "apply only after validation succeeds, before applying the authorization".
        --
        -- A lack of gas stops every authorization, where a failed step skips only its tuple.
        let done ← (payAuthorization fork done authority auth).mapError halt
        -- Steps 7 to 9.
        let (state, refund) ← (delegate fork done.state authority auth).mapError (halt ∘ .state)
        return { done with state, refund := done.refund + refund }
      -- "If any step above fails, immediately stop processing the tuple".
      else return done
    | none => .ok done
  -- A failed step 1 or 2 skips the tuple.
  else .ok done

/-- Apply the authorizations of a transaction in order, on the chain `chainId` at `fork`.

It starts from the state, the accesses, the meter and the paid writes of the transaction.

It starts with no refund.

It fails when the state lacks the code of an authority, and from Glamsterdam when gas lacks.

An error comes with the state so far, whose reads stay. -/
def applyAuthorizations (fork : Fork) (chainId : Nat) (state : TransactionState)
    (accessed : Std.ExtTreeSet Address) (meter : Meter) (paidWrites : Std.ExtTreeSet Address)
    (auths : List Authorization) : Except (EvmError × TransactionState) (Delegations Meter) :=
  -- "For each `[chain_id, address, nonce, y_parity, r, s]` tuple", in order.
  auths.foldlM (applyAuthorization fork chainId) ⟨state, accessed, 0, meter, paidWrites, ∅⟩

end EthLib.Execution.Transactions

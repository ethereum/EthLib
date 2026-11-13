module

public import EthLib.Execution.Proofs.Evm.Call.CodeOrigin
public import EthLib.Execution.Proofs.Transactions.Authorization
public import EthLib.Execution.Transactions.Process

/-!
# Proofs: the first frame of a transaction starts with code hashes of the block or written ones

Each account of the state has no code, a written code, or its code hash in the block.

Buying gas raises the nonce of the sender and takes its fee, so it changes no code hash.

An authorization sets the code of its authority to a delegation, which it writes first.

A delegation to the null address clears the code instead.

Each step of the preparation of the first frame keeps it, and so does every message.

Source: [EIP-7702, Behavior][eip7702].

[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A record of an account read keeps the origin of the code hashes. -/
private theorem keepsCodeOrigin_recordAccountRead (tx : TransactionState) (address : Address) :
    KeepsCodeOrigin tx (tx.recordAccountRead address) :=
  ⟨rfl, fun _ h => h, fun _ => .inr (.inr rfl)⟩

/-- Buying gas keeps the origin of the code hashes, since it raises a nonce and takes a fee. -/
theorem keepsCodeOrigin_buyGas {env : BlockEnvironment fork}
    {state state' : TransactionState} {sender : Address} {tx : Transaction}
    (h : buyGas env state sender tx = .ok state') : KeepsCodeOrigin state state' := by
  unfold buyGas at h
  obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp h
  refine (KeepsCodeOrigin.incrementNonce h1).trans ?_
  refine KeepsCodeOrigin.modifyState_of_keeps (fun account updated hupd => ?_) h2
  split at hupd
  · cases hupd
    rfl
  · cases hupd

/-- An authorization that sets the code of its authority keeps the origin of the code hashes. -/
private theorem keepsCodeOrigin_delegate {state state' : TransactionState}
    {authority : Address} {auth : Authorization} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) :
    KeepsCodeOrigin state state' := by
  obtain ⟨coded, hcode, h⟩ := bind_ok_iff.mp h
  obtain ⟨bumped, hnonce, h⟩ := bind_ok_iff.mp h
  cases h
  exact (KeepsCodeOrigin.setCode hcode).trans (KeepsCodeOrigin.incrementNonce hnonce)

/-- One authorization keeps the origin of the code hashes. -/
private theorem keepsCodeOrigin_applyAuthorization {chainId : Nat}
    {done done' : Delegations Meter} {auth : Authorization}
    (h : applyAuthorization fork chainId done auth = .ok done') :
    KeepsCodeOrigin done.state done'.state := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact .refl _
  · exact keepsCodeOrigin_recordAccountRead _ authority
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    exact (keepsCodeOrigin_recordAccountRead _ authority).trans
      (keepsCodeOrigin_delegate hdelegate)

/-- A list of authorizations keeps the origin of the code hashes. -/
private theorem keepsCodeOrigin_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      KeepsCodeOrigin start.state done.state
  | [], _, _, h => by
    cases h
    exact .refl _
  | _ :: _, _, _, h => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    exact (keepsCodeOrigin_applyAuthorization hnext).trans
      (keepsCodeOrigin_foldlM_applyAuthorization h)

/-- The authorizations of a transaction keep the origin of the code hashes. -/
theorem keepsCodeOrigin_applyAuthorizations {chainId : Nat}
    {state : TransactionState} {accessed : Std.ExtTreeSet Address} {meter : Meter}
    {paid : Std.ExtTreeSet Address} {auths : List Authorization} {done : Delegations Meter}
    (h : applyAuthorizations fork chainId state accessed meter paid auths = .ok done) :
    KeepsCodeOrigin state done.state :=
  keepsCodeOrigin_foldlM_applyAuthorization h

/-- Preparing the first frame of a message keeps the origin of the code hashes. -/
theorem keepsCodeOrigin_prepareFirstFrame {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    KeepsCodeOrigin state first.state := by
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · have hfin : first.state = state.recordAccountRead message.currentTarget := by
        split at h <;>
        · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
          cases h
          rfl
      rw [hfin]
      exact keepsCodeOrigin_recordAccountRead _ _
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target htgt
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    have vdone := keepsCodeOrigin_applyAuthorizations hdone
    dsimp only at h
    generalize hs1 : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = s1 at h
    have v1 : KeepsCodeOrigin state s1 := by
      rw [← hs1]
      split
      · exact vdone.trans (keepsCodeOrigin_recordAccountRead _ _)
      · exact vdone
    have v2 : KeepsCodeOrigin state (s1.recordAccountRead target) :=
      v1.trans (keepsCodeOrigin_recordAccountRead _ _)
    split at h
    all_goals
      obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact v2
      · dsimp only at h
        split at h
        all_goals
          obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact v2.trans (keepsCodeOrigin_recordAccountRead _ _)

end EthLib.Execution.Transactions

module

public import EthLib.Execution.Proofs.Evm.Call.Parent
public import EthLib.Execution.Proofs.Evm.Call.ReadsGrow
public import EthLib.Execution.Proofs.State.Wiped

/-!
# Proofs: a message keeps the storage of an account it does not read

SSTORE writes only the storage of the frame's own account, so other frames keep or wipe it.

Every message at an account records a read of it, by EIP-7928, and no revert drops that read.

So a message keeps or wipes the storage of an account, unless the account is among its reads.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.State.TransactionState

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The writes outside a frame at the address -/

/-- A successful move of the balance of a destroyed account keeps or wipes every storage. -/
theorem keptOrWiped_selfdestructTransfer {address originator beneficiary : Address}
    {tx tx' : TransactionState}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    KeptOrWiped address tx tx' := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (keptOrWiped_moveEther h1).trans (keptOrWiped_setAccountBalance h)
    · cases h
      exact keptOrWiped_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (keptOrWiped_createEther h1).trans (keptOrWiped_setAccountBalance h)

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT keeps or wipes every storage. -/
theorem keptOrWiped_finishSelfdestruct {address beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    KeptOrWiped address evm.state after.state := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact keptOrWiped_selfdestructTransfer (Base.mapError_ok_iff.mp hst)

/-- The preparation of a creation keeps or wipes every storage.

It wipes the storage of the new account, and raises its nonce. -/
theorem keptOrWiped_prepareCreation {address target : Address} {tx tx' : TransactionState}
    (h : prepareCreation fork tx target = .ok tx') : KeptOrWiped address tx tx' := by
  have wipe : KeptOrWiped address tx ((tx.destroyStorage target).markAccountCreated target) :=
    (keptOrWiped_destroyStorage target).trans (.of_eq fun _ => rfl)
  unfold prepareCreation at h
  split at h
  · exact wipe.trans (keptOrWiped_incrementNonce (Base.mapError_ok_iff.mp h))
  · cases h
    exact wipe

/-- The state that a message enters keeps or wipes every storage of the state it is sent from. -/
theorem keptOrWiped_entered {address : Address} {message : Message fork}
    {state entry : TransactionState} {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    KeptOrWiped address state entry := by
  have start : KeptOrWiped address state (startState fork message state) := by
    unfold startState
    split
    · exact keptOrWiped_touchAccount _
    · exact .refl _ _
  rcases h with ⟨-, rfl, -⟩ | ⟨-, moved, -⟩
  · exact start
  · exact start.trans (keptOrWiped_moveEther moved)

/-- Each step of a frame at another account keeps or wipes the storage of `address`.

The steps keep the message, so the frames on the way are not at `address` either. -/
theorem stepRules_keptOrWiped (address : Address) :
    StepRules fork (fun a b : Evm fork Meter => b.message = a.message ∧
      (a.message.currentTarget ≠ address → KeptOrWiped address a.state b.state)) where
  trans hab hbc := ⟨hbc.1.trans hab.1, fun hne =>
    (hab.2 hne).trans (hbc.2 (by rw [hab.1]; exact hne))⟩
  static h := ⟨h.message, fun _ => .of_sameOutside h.state List.not_mem_nil⟩
  -- SSTORE writes the storage of the account of the frame, which is another one.
  sstore _ _ _ _ h := ⟨rfl, fun hne => keptOrWiped_setStorage h (Ne.symm hne)⟩
  tstore _ _ _ _ := ⟨rfl, fun _ => .of_eq fun _ => rfl⟩
  log _ hs _ hm _ := ⟨hm, fun _ => by rw [hs]; exact .refl _ _⟩
  selfdestruct _ _ h := ⟨message_finishSelfdestruct h, fun _ => keptOrWiped_finishSelfdestruct h⟩
  incrementNonce _ _ _ h := ⟨rfl, fun _ => keptOrWiped_incrementNonce h⟩
  incorporate h := ⟨message_incorporateChild _ _, fun hne => by
    rw [state_incorporateChild]
    exact h.2 hne⟩

/-! ## Messages -/

/-- The storage of `address` in `tx'` is kept or wiped from `tx`, or `tx'` has read the account.

Every frame at an account starts from a state that has read it.

So a run whose frame writes the storage of an account has read that account.

Other steps read accounts too, such as BALANCE, a move of ether, or the purchase of gas.

A wipe can hit any account, at its deletion or at the creation of a contract there. -/
def KeptOrRead (address : Address) (tx tx' : TransactionState) : Prop :=
  KeptOrWiped address tx tx' ∨ address ∈ tx'.accountReads

/-- A change that keeps the storage or reads, then another, keeps it or reads.

The second change must keep every read. -/
theorem KeptOrRead.trans {address : Address} {a b c : TransactionState}
    (h : KeptOrRead address a b) (h' : KeptOrRead address b c) (le : b.ReadsLe c) :
    KeptOrRead address a c := by
  rcases h' with h' | h'
  · rcases h with h | h
    · exact .inl (h.trans h')
    · exact .inr (le.accountReads _ h)
  · exact .inr h'

/-- A change that keeps or wipes the storage, then one that keeps it or reads, keeps it or reads.
-/
theorem KeptOrRead.of_keptOrWiped {address : Address} {a b c : TransactionState}
    (h : KeptOrWiped address a b) (h' : KeptOrRead address b c) : KeptOrRead address a c := by
  rcases h' with h' | h'
  · exact .inl (h.trans h')
  · exact .inr h'

/-- What a message keeps: the block, every read, and the storage of `address` unless it reads it.

It keeps them when it starts from a state that has read `address`, if it runs at `address`. -/
def ReadRel (address : Address) (message : Message fork) (state : TransactionState)
    (_substate : Substate) (_meter : Meter) (ended : Evm fork Meter) : Prop :=
  (message.currentTarget = address → address ∈ state.accountReads) →
    ended.state.parent = state.parent ∧ state.ReadsLe ended.state ∧
      KeptOrRead address state ended.state

variable [LawfulGasMeter Meter] {address : Address}

/-- Every successful call and creation keeps the storage of `address`, unless it reads it.

A message at `address` must start from a state that has read `address`.

That holds at every fork, whether or not the message ends with an error. -/
theorem readRel_processMessage_induction (address : Address) (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        ReadRel address message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        ReadRel address message state substate meter ended.val) := by
  let T := ((stepRules_keptOrWiped (fork := fork) (Meter := Meter) address).and
    stepRules_readsLe).and stepRules_parent
  -- A frame keeps its message, its block and every read, and the storage unless it reads it.
  let R : Evm fork Meter → Evm fork Meter → Prop := fun a b =>
    b.message = a.message ∧ b.state.parent = a.state.parent ∧ a.state.ReadsLe b.state ∧
      KeptOrRead address a.state b.state
  -- A frame at `address` has read it.
  let Inv : Evm fork Meter → Prop := fun e =>
    e.message.currentTarget = address → address ∈ e.state.accountReads
  have conv : ∀ {a b : Evm fork Meter}, Inv a →
      ((b.message = a.message ∧ (a.message.currentTarget ≠ address →
        KeptOrWiped address a.state b.state)) ∧ a.state.ReadsLe b.state) ∧
        b.state.parent = a.state.parent → R a b := by
    intro a b hinv h
    refine ⟨h.1.1.1, h.2, h.1.2, ?_⟩
    by_cases hat : a.message.currentTarget = address
    · exact .inr (h.1.2.accountReads _ (hinv hat))
    · exact .inl (h.1.1.2 hat)
  have static : ∀ {a b : Evm fork Meter}, StaticStep a b → R a b := fun h =>
    ⟨h.message, h.parent, h.tracker.readsLe, .inl (.of_sameOutside h.state List.not_mem_nil)⟩
  refine processMessage_rel_byKind (R := R) (Inv := Inv) (Mcall := ReadRel address)
    (Mcreate := ReadRel address) (fun evm => static (.refl evm))
    (fun {a b c} hab hbc => ⟨hbc.1.trans hab.1, hbc.2.1.trans hab.2.1, hab.2.2.1.trans hbc.2.2.1,
      hab.2.2.2.trans hbc.2.2.2 hbc.2.2.1⟩)
    (fun {a b} hinv hab hat => hab.2.2.1.accountReads _ (hinv (by rw [← hab.1]; exact hat)))
    (fun evm error _ => static (staticStep_exceptionalHalt evm error))
    (fun {evm result} hinv hstep => ?_)
    (fun evm _ => static (.of_sameContext ⟨rfl, rfl, rfl, rfl⟩))
    (fun h _ => static (staticStep_runPrecompile h))
    (fun {message state entry substate entrySubstate meter ended} hentry hrun hread => ?_)
    (fun {message state prepared substate meter evm after} hp hm hd hread => ?_) n
  · have k := T.step hstep
    cases result with
    | next after => exact conv hinv k
    | child caller message resume =>
      have kc := conv hinv k.1
      refine ⟨kc, fun child after hres hc => ?_⟩
      rw [childRelByKind_self] at hc
      -- The message starts from a state that has read the account it runs at.
      obtain ⟨hp, hle, hkr⟩ := hc fun hat => hat ▸ step_eq_child_currentRead hstep
      -- The frame that resumes has the context of the caller that takes in the child.
      have same := sameContext_of_step_eq_child hstep hres
      have hstate : after.state = child.state := by rw [same.state, state_incorporateChild]
      refine ⟨by rw [same.message, message_incorporateChild, kc.1], ?_, ?_, ?_⟩
      · rw [hstate, hp, kc.2.1]
      · rw [hstate]
        exact kc.2.2.1.trans hle
      · rw [hstate]
        exact kc.2.2.2.trans hkr hle
  · -- A call ends in its frame, or in the state it is sent from after a failure.
    have hle := readsLe_entered hentry
    obtain ⟨-, hp, hrl, hkr⟩ := hrun fun hat => hle.accountReads _ (hread hat)
    have hparent : ended.state.parent = state.parent := hp.trans (parent_entered hentry)
    refine ⟨(parent_rollbackOnError state ended).trans hparent,
      (hle.trans hrl).trans (readsLe_rollbackOnError _ _), ?_⟩
    unfold rollbackOnError
    split
    · exact .inl (.of_eq fun key => getStorage_restoreTxState hparent address key)
    · exact .of_keptOrWiped (keptOrWiped_entered hentry) hkr
  · -- A creation wipes the storage of its account, runs its init code, then deposits the code.
    have hle := readsLe_prepareCreation hp
    obtain ⟨hpar, hrl, hkr⟩ := hm fun hat => hle.accountReads _ (hread hat)
    have hparent : evm.state.parent = state.parent := hpar.trans (parent_prepareCreation hp)
    have init : KeptOrRead address state evm.state :=
      .of_keptOrWiped (keptOrWiped_prepareCreation hp) hkr
    have hdle := readsLe_depositCode hd
    refine ⟨(parent_depositCode hd).trans hparent, (hle.trans hrl).trans hdle, ?_⟩
    rcases (depositCode_cases hd).2.2 with hs | hs | hs
    · exact .inl (.of_eq fun key => by rw [hs, getStorage_restoreTxState hparent])
    · rw [hs]
      exact init
    · exact init.trans (.inl (keptOrWiped_setCode hs)) hdle

/-- A successful call keeps or wipes the storage of `address`, unless it reads the account.

A call at `address` must start from a state that has read it, as each call of a frame does.

That holds at every fork, whether or not the call ends with an error. -/
theorem keptOrRead_processMessage {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (read : message.currentTarget = address → address ∈ state.accountReads) :
    KeptOrRead address state ended.val.state :=
  ((readRel_processMessage_induction address message.gas).1 message state substate meter held
    rfl ended h read).2.2

/-- A successful creation keeps or wipes the storage of `address`, unless it reads the account.

A creation at `address` must start from a state that has read it, as each one of a frame does.

That holds at every fork, whether or not the creation ends with an error. -/
theorem keptOrRead_processCreateMessage {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (read : message.currentTarget = address → address ∈ state.accountReads) :
    KeptOrRead address state ended.val.state :=
  ((readRel_processMessage_induction address message.gas).2 message state substate meter held
    rfl ended h read).2.2

end EthLib.Execution.Evm

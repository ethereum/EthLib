module

public import EthLib.Execution.Proofs.Evm.Call.CodeOrigin

/-!
# Proofs: a message writes only code that meets the rules of its fork

From Spurious Dragon, a creation deploys at most the code-size cap of its fork ([EIP-170][eip170]).

[EIP-7954][eip7954] raises that cap at Glamsterdam.

From London, a creation never deploys code that starts with the byte `0xEF`, by [EIP-3541][eip3541].

Each code that a call or a creation writes was written before it, or meets the rules of its fork.

[eip170]: https://eips.ethereum.org/EIPS/eip-170#specification
[eip3541]: https://eips.ethereum.org/EIPS/eip-3541#specification
[eip7954]: https://eips.ethereum.org/EIPS/eip-7954#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork Hash32)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The rules and a relation of states -/

/-- A code meets the rules of a deployed code at `fork`.

From Spurious Dragon, it holds at most the code-size cap of the fork.

From London, it does not start with the byte `0xEF`. -/
def CodeRules (fork : Fork) (code : ByteArray) : Prop :=
  (∀ cap, maxCodeSize fork = some cap → code.size ≤ cap) ∧
    (.london ≤ fork → code[0]? ≠ some 0xef)

/-- Each code that the second state has written is written in the first, or meets `P`. -/
def KeepsCodeRules (P : ByteArray → Prop) (tx tx' : TransactionState) : Prop :=
  ∀ (codeHash : Hash32) (code : ByteArray), tx'.codeWrites[codeHash]? = some code →
    tx.codeWrites[codeHash]? = some code ∨ P code

namespace KeepsCodeRules

variable {P : ByteArray → Prop}

/-- Two states with the same written codes keep the rules. -/
theorem of_codeWrites {tx tx' : TransactionState} (h : tx'.codeWrites = tx.codeWrites) :
    KeepsCodeRules P tx tx' :=
  fun _ _ hc => .inl (h ▸ hc)

/-- A state keeps the rules of its own written codes. -/
theorem refl (tx : TransactionState) : KeepsCodeRules P tx tx :=
  of_codeWrites rfl

/-- Two states in a row that each keep the rules keep them together. -/
theorem trans {a b c : TransactionState} (hab : KeepsCodeRules P a b)
    (hbc : KeepsCodeRules P b c) : KeepsCodeRules P a c := by
  intro codeHash code hc
  rcases hbc codeHash code hc with hb | hp
  · exact hab codeHash code hb
  · exact .inr hp

/-- A weaker predicate is kept wherever a stronger one is. -/
theorem mono {Q : ByteArray → Prop} (hPQ : ∀ code, P code → Q code) {tx tx' : TransactionState}
    (h : KeepsCodeRules P tx tx') : KeepsCodeRules Q tx tx' :=
  fun codeHash code hc => (h codeHash code hc).imp_right (hPQ code)

/-- A write of a code that meets the predicate keeps it. -/
theorem setCode {tx tx' : TransactionState} {address : Address} {code : ByteArray}
    (hP : P code) (h : tx.setCode fork address code = .ok tx') : KeepsCodeRules P tx tx' := by
  rcases codeWrites_setCode h with hw | ⟨_, hw⟩
  · exact of_codeWrites hw
  intro codeHash written hc
  rw [hw, Std.ExtTreeMap.getElem?_insert] at hc
  split at hc
  · cases hc
    exact .inr hP
  · exact .inl hc

end KeepsCodeRules

/-! ## Steps of a frame -/

/-- The move of the balance of a self-destructing account keeps the written codes. -/
private theorem codeWrites_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    tx'.codeWrites = tx.codeWrites := by
  unfold Evm.selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (codeWrites_modifyState h).trans
        (codeWrites_moveEther h1)
    · cases h
      exact codeWrites_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (codeWrites_modifyState h).trans
      (codeWrites_modifyState h1)

/-- Each write of a step keeps the rules of the written codes, for every predicate. -/
theorem stepRules_keepsCodeRules (P : ByteArray → Prop) :
    StepRules fork (fun a b : Evm fork Meter => KeepsCodeRules P a.state b.state) where
  trans := KeepsCodeRules.trans
  static h := by
    refine .of_codeWrites ?_
    rw [h.tracker.rest]
    rfl
  sstore _ _ _ _ _ _ h := .of_codeWrites (codeWrites_setStorage h)
  tstore _ _ _ _ := .of_codeWrites rfl
  log _ hs _ _ _ := by rw [hs]; exact .refl _
  selfdestruct _ _ h := by
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact .of_codeWrites (codeWrites_selfdestructTransfer (Base.mapError_ok_iff.mp hst))
  incrementNonce _ _ _ _ h := .of_codeWrites (codeWrites_modifyState h)
  incorporate h := by rw [state_incorporateChild]; exact h

/-! ## Messages -/

/-- The state that a message enters has the written codes of its sender state. -/
private theorem codeWrites_entered {message : Message fork}
    {state entry : TransactionState} {substate entrySubstate : Substate}
    (hentry : Entered fork message state substate entry entrySubstate) :
    entry.codeWrites = state.codeWrites := by
  have hstart : (startState fork message state).codeWrites = state.codeWrites := by
    unfold startState
    split
    · exact codeWrites_touchAccount state message.currentTarget
    · rfl
  rcases hentry with ⟨-, rfl, -⟩ | ⟨-, hm, -⟩
  · exact hstart
  · exact (codeWrites_moveEther hm).trans hstart

/-- A rollback on error keeps the rules, when the frame keeps them. -/
private theorem keepsCodeRules_rollbackOnError {P : ByteArray → Prop}
    {snapshot : TransactionState} {ended : Evm fork Meter}
    (hk : KeepsCodeRules P snapshot ended.state) :
    KeepsCodeRules P snapshot (rollbackOnError snapshot ended).state := by
  unfold rollbackOnError
  split
  -- A rollback puts back the written codes of a snapshot, so it writes no new code.
  · exact .of_codeWrites (sameWrites_restoreTxState ended.state snapshot).codeWrites
  · exact hk

/-- The preparation of a creation keeps the written codes. -/
private theorem codeWrites_prepareCreation {state prepared : TransactionState}
    {address : Address} (hp : prepareCreation fork state address = .ok prepared) :
    prepared.codeWrites = state.codeWrites := by
  unfold prepareCreation at hp
  dsimp only at hp
  split at hp
  · have hn := Base.mapError_ok_iff.mp hp
    unfold TransactionState.incrementNonce at hn
    exact (codeWrites_modifyState hn).trans rfl
  · cases hp
    rfl

/-- A deposit of code puts back the state before the creation, keeps the state, or writes code.

It writes only an output that meets the rules of its fork. -/
private theorem depositCode_cases_rules {snapshot : TransactionState}
    {evm after : Evm fork Meter} (h : depositCode fork snapshot evm = .ok after) :
    after.state = evm.state.restoreTxState snapshot ∨ after.state = evm.state ∨
      (CodeRules fork evm.output ∧
        evm.state.setCode fork evm.message.currentTarget evm.output = .ok after.state) := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    exact .inl rfl
  split at h
  · cases h
    exact .inl rfl
  rename_i hprefix
  split at h
  · cases h
    exact .inl rfl
  split at h
  · cases h
    split
    · exact .inl rfl
    · exact .inr (.inl rfl)
  rename_i hsize
  split at h
  · cases h
    exact .inl rfl
  rename_i hcap
  obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
  cases h
  refine .inr (.inr ⟨⟨fun cap hm => ?_, fun hl hb => hprefix ⟨hl, hb⟩⟩,
    Base.mapError_ok_iff.mp hst⟩)
  rw [hm] at hcap
  simpa using hcap

/-- A deposit of code keeps the rules from the state before the creation. -/
private theorem keepsCodeRules_depositCode {state prepared : TransactionState}
    {address : Address} {evm after : Evm fork Meter}
    (hp : prepareCreation fork state address = .ok prepared)
    (hk : KeepsCodeRules (CodeRules fork) prepared evm.state)
    (hd : depositCode fork state evm = .ok after) :
    KeepsCodeRules (CodeRules fork) state after.state := by
  have hprep : KeepsCodeRules (CodeRules fork) state prepared :=
    .of_codeWrites (codeWrites_prepareCreation hp)
  rcases depositCode_cases_rules hd with hs | hs | ⟨hrules, hs⟩
  · rw [hs]
    exact .of_codeWrites (sameWrites_restoreTxState evm.state state).codeWrites
  · rw [hs]
    exact hprep.trans hk
  -- A message writes code only when a creation deploys it, and the deposit checks the rules first.
  · exact (hprep.trans hk).trans (.setCode hrules hs)

/-- By induction on gas, calls and creations keep the rules of the written codes. -/
private theorem keepsCodeRules_induction [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        KeepsCodeRules (CodeRules fork) state ended.val.state) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        KeepsCodeRules (CodeRules fork) state ended.val.state) :=
  (stepRules_keepsCodeRules (CodeRules fork)).processMessage
    (M := fun _ state _ _ ended => KeepsCodeRules (CodeRules fork) state ended.state)
    (fun hentry hrun => keepsCodeRules_rollbackOnError
      ((KeepsCodeRules.of_codeWrites (codeWrites_entered hentry)).trans hrun))
    (fun hp hm hd => keepsCodeRules_depositCode hp hm hd)
    (fun h => h) n

/-- Each code that a call writes was written before it, or meets the rules of its fork. -/
theorem keepsCodeRules_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processMessage fork message state substate meter held = .ok ended) :
    KeepsCodeRules (CodeRules fork) state ended.val.state :=
  (keepsCodeRules_induction message.gas).1 message state substate meter held rfl ended h

/-- Each code that a creation writes was written before it, or meets the rules of its fork. -/
theorem keepsCodeRules_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    KeepsCodeRules (CodeRules fork) state ended.val.state :=
  (keepsCodeRules_induction message.gas).2 message state substate meter held rfl ended h

end EthLib.Execution.Evm

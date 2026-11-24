module

public import EthLib.Execution.Proofs.Evm.Call.SlotSurplus

/-!
# Proofs: the parts of an instruction keep the error and the surplus of a frame

A frame keeps the surplus of another when it keeps its error and its surplus does not drop.

A pop, a push, an access, a record of a read and a charge keep the surplus.

So does each instruction that reads and writes only the stack, and KECCAK256.

So does each instruction of the program counter, of memory and of the environment.

So do RETURN, the reads of another account, SLOAD, TLOAD, TSTORE and each LOG.

REVERT instead stops its frame with an error, so the frame fails.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)

variable {fork : Fork}

/-- The frame `b` keeps the error of the frame `a`, and a surplus at least that of `a`.

That relation is a preorder. -/
def SurplusKept (a b : Evm fork StateGasMeter) : Prop :=
  b.error = a.error ∧ slotSurplus a ≤ slotSurplus b

/-! ## The relation and the parts of an instruction -/

/-- Every frame keeps its own surplus. -/
theorem surplusKept_refl (evm : Evm fork StateGasMeter) : SurplusKept evm evm :=
  ⟨rfl, le_rfl⟩

/-- Two steps that each keep the surplus keep it together. -/
theorem SurplusKept.trans {a b c : Evm fork StateGasMeter} (hab : SurplusKept a b)
    (hbc : SurplusKept b c) : SurplusKept a c :=
  ⟨hbc.1.trans hab.1, hab.2.trans hbc.2⟩

/-- A pop keeps the surplus. -/
theorem surplusKept_popWord {evm after : Evm fork StateGasMeter} {x : U256}
    (h : popWord evm = .ok (x, after)) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ⟨rfl, le_rfl⟩

/-- A push keeps the surplus. -/
theorem surplusKept_pushWord {evm after : Evm fork StateGasMeter} {x : U256}
    (h : pushWord evm x = .ok after) : SurplusKept evm after := by
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ⟨rfl, le_rfl⟩

/-- A charge of execution gas keeps the surplus. -/
theorem surplusKept_chargeGas {evm after : Evm fork StateGasMeter} {amount : Nat}
    (h : chargeGas evm amount = .ok after) : SurplusKept evm after := by
  obtain ⟨gas, hgas, h⟩ := Base.bind_ok_iff.mp h
  cases h
  -- A charge of execution gas keeps the net state gas and the state.
  obtain ⟨-, rfl⟩ := StateGasMeter.charge_eq_ok_iff.mp hgas
  exact ⟨rfl, le_rfl⟩

/-- A charge of state gas keeps the surplus. -/
theorem surplusKept_chargeStateGas {evm after : Evm fork StateGasMeter} {amount : Nat}
    (h : chargeStateGas evm amount = .ok after) : SurplusKept evm after := by
  obtain ⟨gas, hgas, h⟩ := Base.bind_ok_iff.mp h
  cases h
  -- A charge of state gas raises the net state gas, and keeps the state.
  have hused := StateGasMeter.stateGasUsed_chargeState hgas
  refine ⟨rfl, ?_⟩
  simp only [slotSurplus, hused]
  omega

/-- A charge of a price and of the growth of memory keeps the surplus. -/
theorem surplusKept_chargeGasAndMemory {evm after : Evm fork StateGasMeter} {cost : Nat}
    {ranges : List (U256 × U256)} (h : chargeGasAndMemory evm cost ranges = .ok after) :
    SurplusKept evm after := by
  obtain ⟨_, hc, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (surplusKept_chargeGas hc :)

/-- A step that only adds reads and keeps the meter and the error keeps the surplus. -/
theorem surplusKept_of_staticStep {a b : Evm fork StateGasMeter} (h : StaticStep a b)
    (hgas : b.gas = a.gas) (herr : b.error = a.error) : SurplusKept a b := by
  refine ⟨herr, le_of_eq ?_⟩
  simp only [slotSurplus, hgas, nonceOrCodeFreshSlots_of_readsMore h.tracker]

/-- An access to an address keeps the surplus. -/
theorem surplusKept_accessAddress (evm : Evm fork StateGasMeter) (address : Address) :
    SurplusKept evm (accessAddress evm address).2 := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  rw [h]
  exact ⟨rfl, le_rfl⟩

/-- An access to a slot keeps the surplus. -/
theorem surplusKept_accessStorageKey (evm : Evm fork StateGasMeter) (address : Address)
    (key : Bytes32) : SurplusKept evm (accessStorageKey evm address key).2 := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm address key
  rw [h]
  exact ⟨rfl, le_rfl⟩

/-- A record of the read of an account keeps the surplus. -/
theorem surplusKept_recordAccountRead (evm : Evm fork StateGasMeter) (address : Address) :
    SurplusKept evm (recordAccountRead evm address) :=
  surplusKept_of_staticStep (staticStep_recordAccountRead evm address) rfl rfl

/-- A record of the read of a slot keeps the surplus. -/
theorem surplusKept_recordStorageRead (evm : Evm fork StateGasMeter) (address : Address)
    (key : Bytes32) : SurplusKept evm (recordStorageRead evm address key) :=
  surplusKept_of_staticStep (staticStep_recordStorageRead evm address key) rfl rfl

/-- The pops of the topics of a log keep the surplus. -/
theorem surplusKept_popTopics {evm after : Evm fork StateGasMeter} {n : Nat}
    {topics : List Bytes32} (h : popTopics evm n = .ok (topics, after)) :
    SurplusKept evm after := by
  induction n generalizing evm topics with
  | zero =>
    cases h
    exact surplusKept_refl _
  | succ k ih =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (surplusKept_popWord h1).trans (ih h2)

/-! ## The instructions that read and write only the stack, and KECCAK256 -/

/-- An instruction with one operand keeps the surplus. -/
theorem surplusKept_unaryOp {cost : Nat} {f : U256 → U256}
    {evm after : Evm fork StateGasMeter} (h : unaryOp cost f evm = .ok after) :
    SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_chargeGas h2) (surplusKept_pushWord h3)) :)

/-- An instruction with two operands keeps the surplus. -/
theorem surplusKept_binaryOp {cost : Nat} {f : U256 → U256 → U256}
    {evm after : Evm fork StateGasMeter} (h : binaryOp cost f evm = .ok after) :
    SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1) (SurplusKept.trans (surplusKept_popWord h2)
    (SurplusKept.trans (surplusKept_chargeGas h3) (surplusKept_pushWord h4))) :)

/-- An instruction with three operands keeps the surplus. -/
theorem surplusKept_ternaryOp {cost : Nat} {f : U256 → U256 → U256 → U256}
    {evm after : Evm fork StateGasMeter} (h : ternaryOp cost f evm = .ok after) :
    SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1) (SurplusKept.trans (surplusKept_popWord h2)
    (SurplusKept.trans (surplusKept_popWord h3)
      (SurplusKept.trans (surplusKept_chargeGas h4) (surplusKept_pushWord h5)))) :)

/-- POP keeps the surplus. -/
theorem surplusKept_popStep {evm after : Evm fork StateGasMeter}
    (h : popStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1) (surplusKept_chargeGas h2) :)

/-- PUSHn keeps the surplus. -/
theorem surplusKept_pushN {n : Fin 33} {evm after : Evm fork StateGasMeter}
    (h : pushN n evm = .ok after) : SurplusKept evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_chargeGas h1) (surplusKept_pushWord h2) :)

/-- DUPn keeps the surplus. -/
theorem surplusKept_dupN {n : Fin 16} {evm after : Evm fork StateGasMeter}
    (h : dupN n evm = .ok after) : SurplusKept evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · cases h
  · obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (SurplusKept.trans (surplusKept_chargeGas h1) (surplusKept_pushWord h2) :)

/-- SWAPn keeps the surplus. -/
theorem surplusKept_swapN {n : Fin 16} {evm after : Evm fork StateGasMeter}
    (h : swapN n evm = .ok after) : SurplusKept evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
    · cases h
      exact (surplusKept_chargeGas h1 :)
  · cases h

/-- DUPN keeps the surplus. -/
theorem surplusKept_dupnStep {evm after : Evm fork StateGasMeter}
    (h : dupnStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
    · obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact (SurplusKept.trans (surplusKept_chargeGas h1) (surplusKept_pushWord h2) :)
  · cases h

/-- SWAPN keeps the surplus. -/
theorem surplusKept_swapnStep {evm after : Evm fork StateGasMeter}
    (h : swapnStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
      exact (surplusKept_chargeGas h1 :)
    · cases h
  · cases h

/-- EXCHANGE keeps the surplus. -/
theorem surplusKept_exchangeStep {evm after : Evm fork StateGasMeter}
    (h : exchangeStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
      exact (surplusKept_chargeGas h1 :)
    · cases h
  · cases h

/-- EXP keeps the surplus. -/
theorem surplusKept_expStep {evm after : Evm fork StateGasMeter}
    (h : expStep fork evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1) (SurplusKept.trans (surplusKept_popWord h2)
    (SurplusKept.trans (surplusKept_chargeGas h3) (surplusKept_pushWord h4))) :)

/-- KECCAK256 keeps the surplus. -/
theorem surplusKept_keccak256Step {evm after : Evm fork StateGasMeter}
    (h : keccak256Step evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1) (SurplusKept.trans (surplusKept_popWord h2)
    (SurplusKept.trans (surplusKept_chargeGasAndMemory h3) (surplusKept_pushWord h4))) :)

/-- Each instruction that reads and writes only the stack, and KECCAK256, keeps the surplus. -/
theorem surplusKept_stackOnlyStep {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter}
    (hf : stackOnlyStep fork op = some f) (h : f evm = .ok after) : SurplusKept evm after := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hf <;>
    (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf) <;>
    subst hf <;> first
    | exact surplusKept_binaryOp h
    | exact surplusKept_unaryOp h
    | exact surplusKept_ternaryOp h
    | exact surplusKept_expStep h
    | exact surplusKept_keccak256Step h
    | exact surplusKept_popStep h
    | exact surplusKept_pushN h
    | exact surplusKept_dupN h
    | exact surplusKept_swapN h
    | exact surplusKept_dupnStep h
    | exact surplusKept_swapnStep h
    | exact surplusKept_exchangeStep h

/-! ## The instructions that move or read the program counter, and STOP -/

/-- An instruction that reads the frame keeps the surplus. -/
theorem surplusKept_readFrame {cost : Nat} {value : Evm fork StateGasMeter → U256}
    {evm after : Evm fork StateGasMeter} (h : readFrame cost value evm = .ok after) :
    SurplusKept evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_chargeGas h1) (surplusKept_pushWord h2) :)

/-- An instruction that reads a number of the environment keeps the surplus. -/
theorem surplusKept_readNumber {cost : Nat} {value : Evm fork StateGasMeter → Nat}
    {evm after : Evm fork StateGasMeter} (h : readNumber cost value evm = .ok after) :
    SurplusKept evm after := by
  unfold readNumber at h
  split at h
  · exact surplusKept_readFrame h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h

/-- JUMP keeps the surplus. -/
theorem surplusKept_jumpStep {evm after : Evm fork StateGasMeter}
    (h : jumpStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  have paid := SurplusKept.trans (surplusKept_popWord h1) (surplusKept_chargeGas h2)
  split at h
  · cases h
    exact paid
  · cases h

/-- JUMPI keeps the surplus. -/
theorem surplusKept_jumpiStep {evm after : Evm fork StateGasMeter}
    (h : jumpiStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  have paid := SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_popWord h2) (surplusKept_chargeGas h3))
  split at h
  · cases h
    exact paid
  · split at h
    · cases h
      exact paid
    · cases h

/-- JUMPDEST keeps the surplus. -/
theorem surplusKept_jumpdestStep {evm after : Evm fork StateGasMeter}
    (h : jumpdestStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (surplusKept_chargeGas h1 :)

/-- Each instruction that moves or reads the program counter, and STOP, keeps the surplus. -/
theorem surplusKept_controlFlowStep {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter}
    (hf : controlFlowStep op = some f) (h : f evm = .ok after) : SurplusKept evm after := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case stop =>
    cases h
    exact surplusKept_refl _
  all_goals first
    | exact surplusKept_readFrame h
    | exact surplusKept_jumpStep h
    | exact surplusKept_jumpiStep h
    | exact surplusKept_jumpdestStep h

/-! ## The instructions that move bytes to or from memory -/

/-- MLOAD keeps the surplus. -/
theorem surplusKept_mloadStep {evm after : Evm fork StateGasMeter}
    (h : mloadStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_chargeGasAndMemory h2) (surplusKept_pushWord h3)) :)

/-- MSTORE keeps the surplus. -/
theorem surplusKept_mstoreStep {evm after : Evm fork StateGasMeter}
    (h : mstoreStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_popWord h2) (surplusKept_chargeGasAndMemory h3)) :)

/-- MSTORE8 keeps the surplus. -/
theorem surplusKept_mstore8Step {evm after : Evm fork StateGasMeter}
    (h : mstore8Step evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_popWord h2) (surplusKept_chargeGasAndMemory h3)) :)

/-- MCOPY keeps the surplus. -/
theorem surplusKept_mcopyStep {evm after : Evm fork StateGasMeter}
    (h : mcopyStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1) (SurplusKept.trans (surplusKept_popWord h2)
    (SurplusKept.trans (surplusKept_popWord h3) (surplusKept_chargeGasAndMemory h4))) :)

/-- CALLDATALOAD keeps the surplus. -/
theorem surplusKept_calldataloadStep {evm after : Evm fork StateGasMeter}
    (h : calldataloadStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_chargeGas h2) (surplusKept_pushWord h3)) :)

/-- A copy to memory keeps the surplus. -/
theorem surplusKept_copyToMemory {base : Nat} {source : ByteArray}
    {evm after : Evm fork StateGasMeter} (h : copyToMemory base source evm = .ok after) :
    SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1) (SurplusKept.trans (surplusKept_popWord h2)
    (SurplusKept.trans (surplusKept_popWord h3) (surplusKept_chargeGasAndMemory h4))) :)

/-- RETURNDATACOPY keeps the surplus. -/
theorem surplusKept_returndatacopyStep {evm after : Evm fork StateGasMeter}
    (h : returndatacopyStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  have paid := SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_popWord h2)
      (SurplusKept.trans (surplusKept_popWord h3) (surplusKept_chargeGas h4)))
  split at h
  · cases h
  · cases h
    exact paid

/-- Each instruction that moves bytes to or from memory keeps the surplus. -/
theorem surplusKept_memoryDataStep {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter}
    (hf : memoryDataStep op = some f) (h : f evm = .ok after) : SurplusKept evm after := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case mload => exact surplusKept_mloadStep h
  case mstore => exact surplusKept_mstoreStep h
  case mstore8 => exact surplusKept_mstore8Step h
  case mcopy => exact surplusKept_mcopyStep h
  case calldataload => exact surplusKept_calldataloadStep h
  case calldatacopy | codecopy => exact surplusKept_copyToMemory h
  case returndatacopy => exact surplusKept_returndatacopyStep h
  all_goals exact surplusKept_readFrame h

/-! ## RETURN and REVERT -/

/-- A halt with output keeps the surplus. -/
theorem surplusKept_haltWithOutput {evm after : Evm fork StateGasMeter}
    (h : haltWithOutput evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_popWord h2) (surplusKept_chargeGasAndMemory h3)) :)

/-- A halt with output stops the frame. -/
theorem running_haltWithOutput {evm after : Evm fork StateGasMeter}
    (h : haltWithOutput evm = .ok after) : after.running = false := by
  obtain ⟨⟨_, _⟩, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rfl

/-- RETURN keeps the surplus, and REVERT stops its frame with its own error, so it fails. -/
theorem surplusKept_returnOpStep {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter} (hf : returnOpStep fork op = some f)
    (h : f evm = .ok after) : SurplusKept evm after ∨ FailedFrame after := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hf
  · subst hf
    exact .inl (surplusKept_haltWithOutput h)
  · split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
      have stops := running_haltWithOutput h1
      cases h
      -- REVERT stops the frame with the revert error.
      exact .inr ⟨stops, by simp, .inl rfl⟩
    · cases hf

/-! ## The instructions that read the environment -/

/-- BLOCKHASH keeps the surplus. -/
theorem surplusKept_blockhashStep {evm after : Evm fork StateGasMeter}
    (h : blockhashStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_chargeGas h2) (surplusKept_pushWord h3)) :)

/-- BLOBHASH keeps the surplus. -/
theorem surplusKept_blobhashStep {hf : .dencun ≤ fork}
    {evm after : Evm fork StateGasMeter} (h : blobhashStep hf evm = .ok after) :
    SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_chargeGas h2) (surplusKept_pushWord h3)) :)

/-- Each instruction that reads the environment keeps the surplus. -/
theorem surplusKept_environmentStep {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter}
    (hf : environmentStep fork op = some f) (h : f evm = .ok after) : SurplusKept evm after := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hf
  case blockhash =>
    subst hf
    exact surplusKept_blockhashStep h
  case blobhash =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact surplusKept_blobhashStep h
    · cases hf
  all_goals (repeat' split at hf) <;> (try simp only [Option.some.injEq] at hf) <;> (try subst hf)
  all_goals first
    | cases hf
    | exact surplusKept_readFrame h
    | exact surplusKept_readNumber h

/-! ## The instructions that read another account -/

/-- BALANCE keeps the surplus. -/
theorem surplusKept_balanceStep {evm after : Evm fork StateGasMeter}
    (h : balanceStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_accessAddress _ _)
      (SurplusKept.trans (surplusKept_chargeGas h2) (surplusKept_pushWord h3 :))) :)

/-- EXTCODESIZE keeps the surplus. -/
theorem surplusKept_extcodesizeStep {evm after : Evm fork StateGasMeter}
    (h : extcodesizeStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_accessAddress _ _)
      (SurplusKept.trans (surplusKept_chargeGas h2) (surplusKept_pushWord h3 :))) :)

/-- EXTCODECOPY keeps the surplus. -/
theorem surplusKept_extcodecopyStep {evm after : Evm fork StateGasMeter}
    (h : extcodecopyStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨word, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1) (SurplusKept.trans (surplusKept_popWord h2)
    (SurplusKept.trans (surplusKept_popWord h3) (SurplusKept.trans (surplusKept_popWord h4)
      (SurplusKept.trans (surplusKept_accessAddress _ _) (surplusKept_chargeGasAndMemory h5))))) :)

/-- EXTCODEHASH keeps the surplus. -/
theorem surplusKept_extcodehashStep {evm after : Evm fork StateGasMeter}
    (h : extcodehashStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_accessAddress _ _)
      (SurplusKept.trans (surplusKept_chargeGas h2) (surplusKept_pushWord h3 :))) :)

/-- Each instruction that reads another account keeps the surplus. -/
theorem surplusKept_accountStep {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter}
    (hf : accountStep fork op = some f) (h : f evm = .ok after) : SurplusKept evm after := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hf
  case balance =>
    subst hf
    exact surplusKept_balanceStep h
  case extcodesize =>
    subst hf
    exact surplusKept_extcodesizeStep h
  case extcodecopy =>
    subst hf
    exact surplusKept_extcodecopyStep h
  case extcodehash =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact surplusKept_extcodehashStep h
    · cases hf
  case selfbalance =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact (surplusKept_readFrame h :)
    · cases hf

/-! ## The instructions that use storage -/

/-- SLOAD keeps the surplus. -/
theorem surplusKept_sloadStep {evm after : Evm fork StateGasMeter}
    (h : sloadStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_accessStorageKey _ _ _)
      (SurplusKept.trans (surplusKept_chargeGas h2) (surplusKept_pushWord h3 :))) :)

/-! ## The instructions of transient storage -/

/-- TLOAD keeps the surplus. -/
theorem surplusKept_tloadStep {evm after : Evm fork StateGasMeter}
    (h : tloadStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (SurplusKept.trans (surplusKept_popWord h1)
    (SurplusKept.trans (surplusKept_chargeGas h2) (surplusKept_pushWord h3)) :)

/-- TSTORE keeps the surplus. -/
theorem surplusKept_tstoreStep {evm after : Evm fork StateGasMeter}
    (h : tstoreStep evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · cases h
  · cases h
    exact (SurplusKept.trans (surplusKept_popWord h1)
      (SurplusKept.trans (surplusKept_popWord h2) (surplusKept_chargeGas h3)) :)

/-- TLOAD and TSTORE keep the surplus. -/
theorem surplusKept_transientStorageStep {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter}
    (hf : transientStorageStep fork op = some f) (h : f evm = .ok after) :
    SurplusKept evm after := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf
  case tload =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact surplusKept_tloadStep h
    · cases hf
  case tstore =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact surplusKept_tstoreStep h
    · cases hf

/-! ## The LOG instructions -/

/-- LOGn keeps the surplus. -/
theorem surplusKept_logStep {n : Nat} {evm after : Evm fork StateGasMeter}
    (h : logStep n evm = .ok after) : SurplusKept evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · cases h
  · cases h
    exact (SurplusKept.trans (surplusKept_popWord h1) (SurplusKept.trans (surplusKept_popWord h2)
      (SurplusKept.trans (surplusKept_popTopics h3) (surplusKept_chargeGasAndMemory h4))) :)

/-- Each LOG instruction keeps the surplus. -/
theorem surplusKept_logOpStep {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter}
    (hf : logOpStep op = some f) (h : f evm = .ok after) : SurplusKept evm after := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
  case log =>
    subst hf
    exact surplusKept_logStep h

end EthLib.Execution.Evm

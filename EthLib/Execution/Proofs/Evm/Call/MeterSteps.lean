module

public import EthLib.Execution.Proofs.Evm.Call.Run

/-!
# Proofs: each instruction changes the meter of its frame only through the meter operations

A relation of two meters may hold of each operation that a frame applies to its meter.

Then it holds from the meter of a frame before each successful instruction to the meter after it.

A pop, a push, an access and a record of a read keep the meter.

The meter operations are a charge, a refill, a halt, a revert, a drain, a credit and an absorb.

Each section below covers the instructions that one module of the interpreter defines.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The rules for a relation `Q` of two meters to hold from a frame to every frame after it.

It must be reflexive and transitive, and hold of each operation that a frame applies to its meter.

A frame charges execution gas or state gas, refills state gas, exhausts and rolls back.

A call or a creation drains the reservoir, credits back a message that never ran, and absorbs one.

The child of an absorb may be any meter. -/
structure MeterRules (Q : Meter → Meter → Prop) : Prop where
  /-- Every meter is related to itself. -/
  refl : ∀ meter, Q meter meter
  /-- The relation is transitive. -/
  trans : ∀ {a b c}, Q a b → Q b c → Q a c
  /-- A charge of execution gas keeps the relation. -/
  charge : ∀ {meter after : Meter} {amount : Nat}, GasMeter.charge meter amount = .ok after →
    Q meter after
  /-- A charge of state gas keeps the relation. -/
  chargeState : ∀ {meter after : Meter} {amount : Nat},
    GasMeter.chargeState meter amount = .ok after → Q meter after
  /-- A refill of state gas keeps the relation. -/
  refill : ∀ (meter : Meter) (amount : Nat), Q meter (GasMeter.refill meter amount)
  /-- An exceptional halt keeps the relation. -/
  exhaust : ∀ meter : Meter, Q meter (GasMeter.exhaust meter)
  /-- A revert keeps the relation. -/
  rollback : ∀ meter : Meter, Q meter (GasMeter.rollback meter)
  /-- Passing on the reservoir keeps the relation. -/
  drain : ∀ meter : Meter, Q meter (GasMeter.drain meter)
  /-- Taking back a message that never ran keeps the relation. -/
  credit : ∀ (meter : Meter) (gas reservoir : Nat), Q meter (GasMeter.credit meter gas reservoir)
  /-- Taking in the meter of any message that ran keeps the relation. -/
  absorb : ∀ (meter child : Meter) (succeeded : Bool),
    Q meter (GasMeter.absorb meter child succeeded)

namespace MeterRules

variable {Q : Meter → Meter → Prop}

/-! ## The parts of an instruction -/

/-- A pop keeps the meter. -/
theorem popWord_keeps (rules : MeterRules Q) {evm after : Evm fork Meter} {x : U256}
    (h : popWord evm = .ok (x, after)) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact rules.refl _

/-- A push keeps the meter. -/
theorem pushWord_keeps (rules : MeterRules Q) {evm after : Evm fork Meter} {x : U256}
    (h : pushWord evm x = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact rules.refl _

/-- A charge of execution gas keeps the relation. -/
theorem chargeGas_keeps (rules : MeterRules Q) {evm after : Evm fork Meter} {amount : Nat}
    (h : chargeGas evm amount = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, hc, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact rules.charge hc

/-- A charge of state gas keeps the relation. -/
theorem chargeStateGas_keeps (rules : MeterRules Q) {evm after : Evm fork Meter} {amount : Nat}
    (h : chargeStateGas evm amount = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, hc, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact rules.chargeState hc

/-- A refill of state gas keeps the relation. -/
theorem refillStateGas_keeps (rules : MeterRules Q) (evm : Evm fork Meter) (amount : Nat) :
    Q evm.gas (refillStateGas evm amount).gas :=
  rules.refill _ _

/-- A charge of a price and of the growth of memory keeps the relation. -/
theorem chargeGasAndMemory_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    {cost : Nat} {ranges : List (U256 × U256)}
    (h : chargeGasAndMemory evm cost ranges = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, hc, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.chargeGas_keeps hc :)

/-- An access to an address keeps the meter. -/
theorem accessAddress_keeps (rules : MeterRules Q) (evm : Evm fork Meter) (address : Address) :
    Q evm.gas (accessAddress evm address).2.gas := by
  unfold accessAddress
  split <;> exact rules.refl _

/-- An access to a slot keeps the meter. -/
theorem accessStorageKey_keeps (rules : MeterRules Q) (evm : Evm fork Meter) (address : Address)
    (key : Bytes32) : Q evm.gas (accessStorageKey evm address key).2.gas := by
  unfold accessStorageKey
  split <;> exact rules.refl _

/-- An exceptional halt keeps the relation. -/
theorem exceptionalHalt_keeps (rules : MeterRules Q) (evm : Evm fork Meter) (e : EvmError) :
    Q evm.gas (exceptionalHalt evm e).gas :=
  rules.exhaust _

/-- The pops of the topics of a log keep the meter. -/
theorem popTopics_keeps (rules : MeterRules Q) {evm after : Evm fork Meter} {n : Nat}
    {topics : List Bytes32} (h : popTopics evm n = .ok (topics, after)) : Q evm.gas after.gas := by
  induction n generalizing evm topics with
  | zero =>
    cases h
    exact rules.refl _
  | succ k ih =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (rules.trans (rules.popWord_keeps h1) (ih h2) :)

/-! ## The instructions that read and write only the stack, and KECCAK256 -/

/-- An instruction with one operand keeps the relation. -/
theorem unaryOp_keeps (rules : MeterRules Q) {cost : Nat} {f : U256 → U256}
    {evm after : Evm fork Meter} (h : unaryOp cost f evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1)
    (rules.trans (rules.chargeGas_keeps h2) (rules.pushWord_keeps h3)) :)

/-- An instruction with two operands keeps the relation. -/
theorem binaryOp_keeps (rules : MeterRules Q) {cost : Nat} {f : U256 → U256 → U256}
    {evm after : Evm fork Meter} (h : binaryOp cost f evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.popWord_keeps h2)
    (rules.trans (rules.chargeGas_keeps h3) (rules.pushWord_keeps h4))) :)

/-- An instruction with three operands keeps the relation. -/
theorem ternaryOp_keeps (rules : MeterRules Q) {cost : Nat} {f : U256 → U256 → U256 → U256}
    {evm after : Evm fork Meter} (h : ternaryOp cost f evm = .ok after) :
    Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.popWord_keeps h2)
    (rules.trans (rules.popWord_keeps h3)
      (rules.trans (rules.chargeGas_keeps h4) (rules.pushWord_keeps h5)))) :)

/-- POP keeps the relation. -/
theorem popStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : popStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.chargeGas_keeps h2) :)

/-- PUSHn keeps the relation. -/
theorem pushN_keeps (rules : MeterRules Q) {n : Fin 33} {evm after : Evm fork Meter}
    (h : pushN n evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.chargeGas_keeps h1) (rules.pushWord_keeps h2) :)

/-- DUPn keeps the relation. -/
theorem dupN_keeps (rules : MeterRules Q) {n : Fin 16} {evm after : Evm fork Meter}
    (h : dupN n evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · cases h
  · obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (rules.trans (rules.chargeGas_keeps h1) (rules.pushWord_keeps h2) :)

/-- SWAPn keeps the relation. -/
theorem swapN_keeps (rules : MeterRules Q) {n : Fin 16} {evm after : Evm fork Meter}
    (h : swapN n evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
    · cases h
      exact (rules.chargeGas_keeps h1 :)
  · cases h

/-- DUPN keeps the relation. -/
theorem dupnStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : dupnStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
    · obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact (rules.trans (rules.chargeGas_keeps h1) (rules.pushWord_keeps h2) :)
  · cases h

/-- SWAPN keeps the relation. -/
theorem swapnStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : swapnStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
      exact (rules.chargeGas_keeps h1 :)
    · cases h
  · cases h

/-- EXCHANGE keeps the relation. -/
theorem exchangeStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : exchangeStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
      exact (rules.chargeGas_keeps h1 :)
    · cases h
  · cases h

/-- EXP keeps the relation. -/
theorem expStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : expStep fork evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.popWord_keeps h2)
    (rules.trans (rules.chargeGas_keeps h3) (rules.pushWord_keeps h4))) :)

/-- KECCAK256 keeps the relation. -/
theorem keccak256Step_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : keccak256Step evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.popWord_keeps h2)
    (rules.trans (rules.chargeGasAndMemory_keeps h3) (rules.pushWord_keeps h4))) :)

/-- Each instruction that reads and writes only the stack, and KECCAK256, keeps the relation. -/
theorem stackOnlyStep_keeps (rules : MeterRules Q) {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : stackOnlyStep fork op = some f) (h : f evm = .ok after) : Q evm.gas after.gas := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hf
  all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf) <;>
    (try subst hf)
  all_goals first
    | cases hf
    | exact rules.binaryOp_keeps h
    | exact rules.unaryOp_keeps h
    | exact rules.ternaryOp_keeps h
    | exact rules.expStep_keeps h
    | exact rules.keccak256Step_keeps h
    | exact rules.popStep_keeps h
    | exact rules.pushN_keeps h
    | exact rules.dupN_keeps h
    | exact rules.swapN_keeps h
    | exact rules.dupnStep_keeps h
    | exact rules.swapnStep_keeps h
    | exact rules.exchangeStep_keeps h

/-! ## The instructions that move or read the program counter, and STOP -/

/-- An instruction that reads the frame keeps the relation. -/
theorem readFrame_keeps (rules : MeterRules Q) {cost : Nat} {value : Evm fork Meter → U256}
    {evm after : Evm fork Meter} (h : readFrame cost value evm = .ok after) :
    Q evm.gas after.gas := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.chargeGas_keeps h1) (rules.pushWord_keeps h2) :)

/-- JUMP keeps the relation. -/
theorem jumpStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : jumpStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  have paid := rules.trans (rules.popWord_keeps h1) (rules.chargeGas_keeps h2)
  split at h
  · cases h
    exact paid
  · cases h

/-- JUMPI keeps the relation. -/
theorem jumpiStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : jumpiStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  have paid := rules.trans (rules.popWord_keeps h1)
    (rules.trans (rules.popWord_keeps h2) (rules.chargeGas_keeps h3))
  split at h
  · cases h
    exact paid
  · split at h
    · cases h
      exact paid
    · cases h

/-- JUMPDEST keeps the relation. -/
theorem jumpdestStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : jumpdestStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.chargeGas_keeps h1 :)

/-- Each instruction that moves or reads the program counter, and STOP, keeps the relation. -/
theorem controlFlowStep_keeps (rules : MeterRules Q) {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : controlFlowStep op = some f) (h : f evm = .ok after) : Q evm.gas after.gas := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case stop =>
    cases h
    exact rules.refl _
  all_goals first
    | exact rules.readFrame_keeps h
    | exact rules.jumpStep_keeps h
    | exact rules.jumpiStep_keeps h
    | exact rules.jumpdestStep_keeps h

/-! ## The instructions that move bytes to or from memory -/

/-- MLOAD keeps the relation. -/
theorem mloadStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : mloadStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1)
    (rules.trans (rules.chargeGasAndMemory_keeps h2) (rules.pushWord_keeps h3)) :)

/-- MSTORE keeps the relation. -/
theorem mstoreStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : mstoreStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1)
    (rules.trans (rules.popWord_keeps h2) (rules.chargeGasAndMemory_keeps h3)) :)

/-- MSTORE8 keeps the relation. -/
theorem mstore8Step_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : mstore8Step evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1)
    (rules.trans (rules.popWord_keeps h2) (rules.chargeGasAndMemory_keeps h3)) :)

/-- MCOPY keeps the relation. -/
theorem mcopyStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : mcopyStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.popWord_keeps h2)
    (rules.trans (rules.popWord_keeps h3) (rules.chargeGasAndMemory_keeps h4))) :)

/-- CALLDATALOAD keeps the relation. -/
theorem calldataloadStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : calldataloadStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1)
    (rules.trans (rules.chargeGas_keeps h2) (rules.pushWord_keeps h3)) :)

/-- A copy to memory keeps the relation. -/
theorem copyToMemory_keeps (rules : MeterRules Q) {base : Nat} {source : ByteArray}
    {evm after : Evm fork Meter} (h : copyToMemory base source evm = .ok after) :
    Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.popWord_keeps h2)
    (rules.trans (rules.popWord_keeps h3) (rules.chargeGasAndMemory_keeps h4))) :)

/-- RETURNDATACOPY keeps the relation. -/
theorem returndatacopyStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : returndatacopyStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  have paid := rules.trans (rules.popWord_keeps h1) (rules.trans (rules.popWord_keeps h2)
    (rules.trans (rules.popWord_keeps h3) (rules.chargeGas_keeps h4)))
  split at h
  · cases h
  · cases h
    exact paid

/-- Each instruction that moves bytes to or from memory keeps the relation. -/
theorem memoryDataStep_keeps (rules : MeterRules Q) {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : memoryDataStep op = some f) (h : f evm = .ok after) : Q evm.gas after.gas := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case mload => exact rules.mloadStep_keeps h
  case mstore => exact rules.mstoreStep_keeps h
  case mstore8 => exact rules.mstore8Step_keeps h
  case mcopy => exact rules.mcopyStep_keeps h
  case calldataload => exact rules.calldataloadStep_keeps h
  case calldatacopy | codecopy => exact rules.copyToMemory_keeps h
  case returndatacopy => exact rules.returndatacopyStep_keeps h
  all_goals exact rules.readFrame_keeps h

/-! ## RETURN and REVERT -/

/-- A halt with output keeps the relation. -/
theorem haltWithOutput_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : haltWithOutput evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1)
    (rules.trans (rules.popWord_keeps h2) (rules.chargeGasAndMemory_keeps h3)) :)

/-- RETURN and REVERT keep the relation. -/
theorem returnOpStep_keeps (rules : MeterRules Q) {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : returnOpStep fork op = some f) (h : f evm = .ok after) : Q evm.gas after.gas := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hf
  · subst hf
    exact rules.haltWithOutput_keeps h
  · split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact (rules.haltWithOutput_keeps h1 :)
    · cases hf

/-! ## The instructions that read the environment -/

/-- BLOCKHASH keeps the relation. -/
theorem blockhashStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : blockhashStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1)
    (rules.trans (rules.chargeGas_keeps h2) (rules.pushWord_keeps h3)) :)

/-- BLOBHASH keeps the relation. -/
theorem blobhashStep_keeps (rules : MeterRules Q) {hf : .dencun ≤ fork}
    {evm after : Evm fork Meter} (h : blobhashStep hf evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1)
    (rules.trans (rules.chargeGas_keeps h2) (rules.pushWord_keeps h3)) :)

/-- Each instruction that reads the environment keeps the relation. -/
theorem environmentStep_keeps (rules : MeterRules Q) {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : environmentStep fork op = some f) (h : f evm = .ok after) : Q evm.gas after.gas := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hf
  case blockhash =>
    subst hf
    exact rules.blockhashStep_keeps h
  case blobhash =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact rules.blobhashStep_keeps h
    · cases hf
  all_goals (repeat' split at hf) <;> (try simp only [Option.some.injEq] at hf) <;> (try subst hf)
  all_goals first
    | cases hf
    | exact rules.readFrame_keeps h

/-! ## The instructions that read another account -/

/-- BALANCE keeps the relation. -/
theorem balanceStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : balanceStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.accessAddress_keeps _ _)
    (rules.trans (rules.chargeGas_keeps h2) (rules.pushWord_keeps h3 :))) :)

/-- EXTCODESIZE keeps the relation. -/
theorem extcodesizeStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : extcodesizeStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.accessAddress_keeps _ _)
    (rules.trans (rules.chargeGas_keeps h2) (rules.pushWord_keeps h3 :))) :)

/-- EXTCODECOPY keeps the relation. -/
theorem extcodecopyStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : extcodecopyStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨word, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.popWord_keeps h2)
    (rules.trans (rules.popWord_keeps h3) (rules.trans (rules.popWord_keeps h4)
      (rules.trans (rules.accessAddress_keeps _ _) (rules.chargeGasAndMemory_keeps h5))))) :)

/-- EXTCODEHASH keeps the relation. -/
theorem extcodehashStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : extcodehashStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.accessAddress_keeps _ _)
    (rules.trans (rules.chargeGas_keeps h2) (rules.pushWord_keeps h3 :))) :)

/-- Each instruction that reads another account keeps the relation. -/
theorem accountStep_keeps (rules : MeterRules Q) {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : accountStep fork op = some f) (h : f evm = .ok after) : Q evm.gas after.gas := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hf
  case balance =>
    subst hf
    exact rules.balanceStep_keeps h
  case extcodesize =>
    subst hf
    exact rules.extcodesizeStep_keeps h
  case extcodecopy =>
    subst hf
    exact rules.extcodecopyStep_keeps h
  case extcodehash =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact rules.extcodehashStep_keeps h
    · cases hf
  case selfbalance =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact (rules.readFrame_keeps h :)
    · cases hf

/-! ## The instructions that use storage -/

/-- SLOAD keeps the relation. -/
theorem sloadStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : sloadStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.accessStorageKey_keeps _ _ _)
    (rules.trans (rules.chargeGas_keeps h2) (rules.pushWord_keeps h3 :))) :)

/-- SSTORE keeps the relation, when it pays and when it halts once it has read the slot. -/
theorem sstoreStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : sstoreStep evm = .ok after) : Q evm.gas after.gas := by
  unfold sstoreStep at h
  split at h
  · cases h
  obtain ⟨⟨word, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨new, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · cases h
  have pre := rules.trans (rules.trans (rules.popWord_keeps h1) (rules.popWord_keeps h2))
    (rules.accessStorageKey_keeps e2 e2.message.currentTarget (U256.toBeBytes word))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · cases h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (rules.trans pre (rules.trans (rules.refill _ _)
      (rules.trans (rules.chargeGas_keeps h3) (rules.chargeStateGas_keeps h4))) :)
  · exact (rules.trans pre (rules.exhaust _) :)

/-- SLOAD and SSTORE keep the relation. -/
theorem storageStep_keeps (rules : MeterRules Q) {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : storageStep op = some f) (h : f evm = .ok after) : Q evm.gas after.gas := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case sload => exact rules.sloadStep_keeps h
  case sstore => exact rules.sstoreStep_keeps h

/-! ## The instructions of transient storage -/

/-- TLOAD keeps the relation. -/
theorem tloadStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : tloadStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.popWord_keeps h1)
    (rules.trans (rules.chargeGas_keeps h2) (rules.pushWord_keeps h3)) :)

/-- TSTORE keeps the relation. -/
theorem tstoreStep_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    (h : tstoreStep evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · cases h
  · cases h
    exact (rules.trans (rules.popWord_keeps h1)
      (rules.trans (rules.popWord_keeps h2) (rules.chargeGas_keeps h3)) :)

/-- TLOAD and TSTORE keep the relation. -/
theorem transientStorageStep_keeps (rules : MeterRules Q) {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : transientStorageStep fork op = some f) (h : f evm = .ok after) :
    Q evm.gas after.gas := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf
  case tload =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact rules.tloadStep_keeps h
    · cases hf
  case tstore =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact rules.tstoreStep_keeps h
    · cases hf

/-! ## The LOG instructions and SELFDESTRUCT -/

/-- LOGn keeps the relation. -/
theorem logStep_keeps (rules : MeterRules Q) {n : Nat} {evm after : Evm fork Meter}
    (h : logStep n evm = .ok after) : Q evm.gas after.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · cases h
  · cases h
    exact (rules.trans (rules.popWord_keeps h1) (rules.trans (rules.popWord_keeps h2)
      (rules.trans (rules.popTopics_keeps h3) (rules.chargeGasAndMemory_keeps h4))) :)

/-- Each LOG instruction keeps the relation. -/
theorem logOpStep_keeps (rules : MeterRules Q) {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : logOpStep op = some f) (h : f evm = .ok after) : Q evm.gas after.gas := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
  case log =>
    subst hf
    exact rules.logStep_keeps h

/-- SELFDESTRUCT keeps the relation. -/
theorem selfdestructOpStep_keeps (rules : MeterRules Q) {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : selfdestructOpStep fork op = some f) (h : f evm = .ok after) :
    Q evm.gas after.gas := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
  subst hf
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have pre := rules.trans (rules.popWord_keeps h1)
    (rules.accessAddress_keeps e1 (toAddressMasked w))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact (rules.trans pre (rules.trans (rules.chargeGas_keeps h2 :)
        (rules.chargeStateGas_keeps h3)) :)
  · exact (rules.trans pre (rules.exhaust _) :)

/-- Each instruction that gives the next frame keeps the relation. -/
theorem instruction_keeps (rules : MeterRules Q) {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (h : run evm = .ok after) : Q evm.gas after.gas := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.stackOnlyStep_keeps hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.controlFlowStep_keeps hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.memoryDataStep_keeps hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.returnOpStep_keeps hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.environmentStep_keeps hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.accountStep_keeps hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.storageStep_keeps hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.transientStorageStep_keeps hf h
  rcases orElse_eq_some hrun with hf | hf
  · exact rules.logOpStep_keeps hf h
  · exact rules.selfdestructOpStep_keeps hf h

/-! ## The calls and the creations -/

/-- A caller that takes in the frame of any child keeps the relation. -/
theorem incorporateChild_keeps (rules : MeterRules Q) (caller child : Evm fork Meter) :
    Q caller.gas (incorporateChild fork caller child).gas := by
  unfold incorporateChild
  split <;> exact rules.absorb _ _ _

/-- A call that runs no message keeps the relation. -/
theorem skipCall_keeps (rules : MeterRules Q) {evm after : Evm fork Meter} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) : Q evm.gas after.gas := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (rules.trans (rules.credit evm.gas gas reservoir) (rules.pushWord_keeps h1 :) :)

/-- A caller that resumes after a call keeps the relation, whatever its child. -/
theorem resumeCall_keeps (rules : MeterRules Q) {caller child after : Evm fork Meter}
    {newAccount : Nat} {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    Q caller.gas after.gas := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  refine rules.trans ?_ (rules.pushWord_keeps h1 :)
  dsimp only
  split
  · exact rules.incorporateChild_keeps _ _
  · exact rules.trans (rules.incorporateChild_keeps _ _) (rules.refill _ _)

/-- A creator that resumes after a creation keeps the relation, whatever its child. -/
theorem resumeCreate_keeps (rules : MeterRules Q) {caller child after : Evm fork Meter}
    {newAccount : Nat} {address : Address}
    (h : resumeCreate fork caller newAccount address child = .ok after) :
    Q caller.gas after.gas := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  refine rules.trans ?_ (rules.pushWord_keeps h1 :)
  dsimp only
  split
  · exact rules.incorporateChild_keeps _ _
  · exact rules.trans (rules.incorporateChild_keeps _ _) (rules.refill _ _)

/-- A result that keeps the relation from a frame keeps it from any frame before that one. -/
theorem lift (rules : MeterRules Q) {C : Evm fork Meter → Message fork → Evm fork Meter → Prop}
    {evm evm' : Evm fork Meter} {result : StepResult fork Meter}
    (r : result.Keeps (fun a b => Q a.gas b.gas) C evm') (h : Q evm.gas evm'.gas) :
    result.Keeps (fun a b => Q a.gas b.gas) C evm :=
  StepResult.Keeps.lift (R := fun a b => Q a.gas b.gas) (fun hab hbc => rules.trans hab hbc) h r

/-- A successful send of a message keeps the relation. -/
theorem genericCall_keeps (rules : MeterRules Q)
    {C : Evm fork Meter → Message fork → Evm fork Meter → Prop} {evm : Evm fork Meter}
    {message : Message fork} {newAccount : Nat} {outputStart outputSize : U256}
    {result : StepResult fork Meter}
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    result.Keeps (fun a b => Q a.gas b.gas) C evm := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (rules.trans (rules.refill evm.gas newAccount) (rules.skipCall_keeps hs :) :)
  · cases h
    exact ⟨rules.refl _, fun _ _ hres _ => (rules.resumeCall_keeps hres :)⟩

/-- The successful end of a call instruction keeps the relation. -/
theorem finishCall_keeps (rules : MeterRules Q)
    {C : Evm fork Meter → Message fork → Evm fork Meter → Prop} {kind : CallKind}
    {call : CallOperands} {callee : Callee} {subCall newAccount expandBy : Nat}
    {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    result.Keeps (fun a b => Q a.gas b.gas) C evm := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  have pre := rules.drain evm.gas
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (rules.trans pre (rules.trans (rules.refill _ newAccount) (rules.skipCall_keeps hs :)) :)
  · exact rules.lift (rules.genericCall_keeps h) pre

/-- The pops of the operands of a call keep the meter. -/
theorem popCallOperands_keeps (rules : MeterRules Q) {kind : CallKind}
    {evm after : Evm fork Meter} {call : CallOperands}
    (h : popCallOperands kind evm = .ok (call, after)) : Q evm.gas after.gas := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have p3 : Q e2.gas e3.gas := by
    unfold popCallValue at h3
    split at h3
    · exact rules.popWord_keeps h3
    · cases h3
      exact rules.refl _
  exact rules.trans (rules.popWord_keeps h1) (rules.trans (rules.popWord_keeps h2)
    (rules.trans p3 (rules.trans (rules.popWord_keeps h4) (rules.trans (rules.popWord_keeps h5)
      (rules.trans (rules.popWord_keeps h6) (rules.popWord_keeps h7))))))

/-- The access to a delegate keeps the meter. -/
theorem accessDelegation_keeps (rules : MeterRules Q) {evm after : Evm fork Meter}
    {address : Address} {known : Nat} {callee : Callee}
    (h : accessDelegation evm address known = .ok (callee, after)) : Q evm.gas after.gas := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (rules.accessAddress_keeps _ _ :)
  · cases h
    exact rules.refl _

/-- The payment of a call keeps the relation. -/
theorem payCall_keeps (rules : MeterRules Q) {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    Q evm.gas after.gas := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact rules.trans (rules.chargeGas_keeps h1)
      (rules.trans (rules.chargeStateGas_keeps h2) (rules.chargeGas_keeps h3))
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact rules.chargeGas_keeps h1

/-- A successful step of a call instruction keeps the relation. -/
theorem callStep_keeps (rules : MeterRules Q)
    {C : Evm fork Meter → Message fork → Evm fork Meter → Prop} {kind : CallKind}
    {evm : Evm fork Meter} {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    result.Keeps (fun a b => Q a.gas b.gas) C evm := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha := rules.accessAddress_keeps e1 call.address
  rw [hacc] at ha
  have s3 : Q evm.gas (recordAccountRead e2 call.address).gas :=
    rules.trans (rules.popCallOperands_keeps h1) ha
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 := rules.trans s3 (rules.accessDelegation_keeps h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      exact rules.lift (rules.finishCall_keeps h) (rules.trans s4 (rules.payCall_keeps h5))
    · exact (rules.trans s4 (rules.exhaust _) :)
  · exact (rules.trans s3 (rules.exhaust _) :)

/-- A successful launch of a creation keeps the relation. -/
theorem launchCreate_keeps (rules : MeterRules Q)
    {C : Evm fork Meter → Message fork → Evm fork Meter → Prop} {evm : Evm fork Meter}
    {value : U256} {initCode : ByteArray} {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) :
    result.Keeps (fun a b => Q a.gas b.gas) C evm := by
  unfold launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (rules.skipCall_keeps hs :)
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have access := rules.accessAddress_keeps
    (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) address
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, -, hr⟩ := Base.bind_ok_iff.mp hr
    have ms : Q evm.gas e2.gas :=
      rules.trans access (rules.trans (rules.chargeStateGas_keeps h1 :) (rules.chargeGas_keeps h2))
    split at hr
    · cases hr
      have md := rules.trans ms (rules.drain e2.gas)
      exact ⟨md, fun _ _ hres _ => rules.trans md (rules.resumeCreate_keeps hres)⟩
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      exact (rules.trans ms (rules.trans (refillStateGas_keeps rules _ _ :)
        (rules.pushWord_keeps h3 :)) :)
  · exact (rules.trans access (rules.exhaust _) :)

/-- A successful step of CREATE or CREATE2 keeps the relation. -/
theorem createStep_keeps (rules : MeterRules Q)
    {C : Evm fork Meter → Message fork → Evm fork Meter → Prop} {create2 : Bool}
    {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : createStep create2 evm = .ok result) :
    result.Keeps (fun a b => Q a.gas b.gas) C evm := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have m4 : Q e3.gas e4.gas := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, e⟩, he, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact rules.popWord_keeps he
    · cases h4
      exact rules.refl _
  have m5 : Q evm.gas e5.gas := rules.trans (rules.popWord_keeps h1)
    (rules.trans (rules.popWord_keeps h2) (rules.trans (rules.popWord_keeps h3)
      (rules.trans m4 (rules.chargeGasAndMemory_keeps h5))))
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact rules.lift (rules.launchCreate_keeps h) m5

/-- A successful instruction that may send a message keeps the relation. -/
theorem messageInstruction_keeps (rules : MeterRules Q)
    {C : Evm fork Meter → Message fork → Evm fork Meter → Prop} {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : result.Keeps (fun a b => Q a.gas b.gas) C evm := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact rules.callStep_keeps h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact rules.callStep_keeps h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact rules.createStep_keeps h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact rules.createStep_keeps h
         · cases hrun)

end MeterRules

end EthLib.Execution.Evm

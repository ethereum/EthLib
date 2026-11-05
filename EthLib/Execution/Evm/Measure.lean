module

public import EthLib.Execution.Evm.AccountData
public import EthLib.Execution.Evm.ControlFlow
public import EthLib.Execution.Evm.EnvironmentData
public import EthLib.Execution.Evm.LogData
public import EthLib.Execution.Evm.MemoryData
public import EthLib.Execution.Evm.Return
public import EthLib.Execution.Evm.StackOnly
public import EthLib.Execution.Evm.Storage
public import EthLib.Execution.Evm.TransientStorage

/-!
# `Evm.Measure`

The measure of a frame is twice its gas left, plus one while it runs.

Each instruction that succeeds lowers the measure of a running frame.

An instruction that lets the frame run charges at least 1 gas, so it lowers the measure by 2.

STOP, RETURN and REVERT can charge nothing, but they stop the frame, so they lower it by 1.

So the execution of a frame ends, and needs no bound on its number of steps.

The groups of instructions below are those of their own modules.

These theorems are part of the specification, not of its proofs.

A definition that runs the loop must show that each step lowers the measure, so it needs them.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The measure of a frame: twice its gas left, plus one while it runs. -/
def measure (evm : Evm fork Meter) : Nat :=
  2 * GasMeter.gasLeft evm.gas + evm.running.toNat

/-- A step lowers the measure of the frame `evm`.

A message to run first has less gas than the frame.

Any frame that ends the message with at most its gas lets the frame go on with a lower measure. -/
def StepResult.Decreases (evm : Evm fork Meter) : StepResult fork Meter → Prop
  | .next after => measure after < measure evm
  | .child _ message resume =>
    message.gas < GasMeter.gasLeft evm.gas ∧
      ∀ child after, GasMeter.gasLeft child.gas ≤ message.gas → resume child = .ok after →
        measure after < measure evm

/-- The second frame has at least `amount` less gas than the first, and runs as the first does. -/
structure Pays (amount : Nat) (before after : Evm fork Meter) : Prop where
  /-- The gas left drops by at least `amount`. -/
  gasLeft : GasMeter.gasLeft after.gas + amount ≤ GasMeter.gasLeft before.gas
  /-- The frame runs after exactly when it runs before. -/
  running : after.running = before.running

/-- A frame with the gas and the running flag of another pays nothing to reach it. -/
theorem Pays.of_eq {before after : Evm fork Meter} (gas : after.gas = before.gas)
    (running : after.running = before.running) : Pays 0 before after :=
  ⟨by rw [gas]; omega, running⟩

/-- Two payments in a row pay their sum. -/
theorem Pays.trans {a b c : Evm fork Meter} {m n : Nat} (hab : Pays m a b) (hbc : Pays n b c) :
    Pays (m + n) a c :=
  ⟨by have := hab.gasLeft; have := hbc.gasLeft; omega, hbc.running.trans hab.running⟩

/-- A payment of `n` is a payment of any `m ≤ n`. -/
theorem Pays.mono {a b : Evm fork Meter} {m n : Nat} (h : Pays n a b) (hle : m ≤ n := by decide) :
    Pays m a b :=
  ⟨by have := h.gasLeft; omega, h.running⟩

/-- A payment to a frame is a payment to any frame with the same gas and running flag. -/
theorem Pays.congr {a b c : Evm fork Meter} {n : Nat} (h : Pays n a b) (gas : c.gas = b.gas)
    (running : c.running = b.running) : Pays n a c :=
  ⟨gas ▸ h.gasLeft, running.trans h.running⟩

/-- A frame that pays at least 1 gas and still runs has a lower measure. -/
theorem Pays.measure_lt {a b : Evm fork Meter} (h : Pays 1 a b) (running : a.running = true) :
    measure b < measure a := by
  have := h.gasLeft
  simp only [measure, h.running, running]
  omega

/-- A running frame that stops, with no more gas, has a lower measure. -/
theorem measure_lt_of_stop {a b : Evm fork Meter}
    (gas : GasMeter.gasLeft b.gas ≤ GasMeter.gasLeft a.gas) (stops : b.running = false)
    (running : a.running = true) : measure b < measure a := by
  simp only [measure, stops, running]
  simp only [Bool.toNat_false, Bool.toNat_true]
  omega

/-! ## The parts of an instruction -/

/-- A pop pays nothing. -/
theorem popWord_pays {evm after : Evm fork Meter} {x : U256}
    (h : popWord evm = .ok (x, after)) : Pays 0 evm after := by
  obtain ⟨⟨_, _⟩, -, h⟩ := except_bind_eq_ok h
  cases h
  exact .of_eq rfl rfl

/-- A push pays nothing. -/
theorem pushWord_pays {evm after : Evm fork Meter} {x : U256}
    (h : pushWord evm x = .ok after) : Pays 0 evm after := by
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  cases h
  exact .of_eq rfl rfl

/-- A charge of `amount` pays `amount`. -/
theorem chargeGas_pays [LawfulGasMeter Meter] {evm after : Evm fork Meter} {amount : Nat}
    (h : chargeGas evm amount = .ok after) : Pays amount evm after := by
  obtain ⟨_, hc, h⟩ := except_bind_eq_ok h
  cases h
  exact ⟨LawfulGasMeter.gasLeft_charge hc, rfl⟩

/-- A charge of a price and of the growth of memory pays at least the price. -/
theorem chargeGasAndMemory_pays [LawfulGasMeter Meter] {evm after : Evm fork Meter}
    {cost : Nat} {ranges : List (U256 × U256)}
    (h : chargeGasAndMemory evm cost ranges = .ok after) : Pays cost evm after := by
  obtain ⟨_, hc, h⟩ := except_bind_eq_ok h
  cases h
  exact ((chargeGas_pays hc).mono (Nat.le_add_right _ _)).congr rfl rfl

/-- An access to an address pays nothing. -/
theorem accessAddress_pays (evm : Evm fork Meter) (address : Address) :
    Pays 0 evm (accessAddress evm address).2 := by
  unfold accessAddress
  split <;> exact .of_eq rfl rfl

/-- An access to a slot pays nothing. -/
theorem accessStorageKey_pays (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    Pays 0 evm (accessStorageKey evm address key).2 := by
  unfold accessStorageKey
  split <;> exact .of_eq rfl rfl

/-- The pops of the topics of a log pay nothing. -/
theorem popTopics_pays {evm after : Evm fork Meter} {n : Nat} {topics : List Bytes32}
    (h : popTopics evm n = .ok (topics, after)) : Pays 0 evm after := by
  induction n generalizing evm topics with
  | zero =>
    cases h
    exact .of_eq rfl rfl
  | succ k ih =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := except_bind_eq_ok h
    obtain ⟨⟨_, e2⟩, h2, h⟩ := except_bind_eq_ok h
    cases h
    exact ((popWord_pays h1).trans (ih h2)).mono (by omega)

/-! ## The prices of the instructions that read an account or storage -/

/-- The price of BALANCE is at least 1 at every fork. -/
theorem one_le_balanceCost (fork : Fork) (cold : Bool) : 1 ≤ balanceCost fork cold := by
  unfold balanceCost accountAccessCost gasSchedule
  repeat' split
  all_goals decide

/-- The price of EXTCODESIZE is at least 1 at every fork. -/
theorem one_le_externalBaseCost (fork : Fork) (cold : Bool) : 1 ≤ externalBaseCost fork cold := by
  unfold externalBaseCost accountAccessCost gasSchedule
  repeat' split
  all_goals decide

/-- The price of EXTCODEHASH is at least 1 at every fork. -/
theorem one_le_extcodehashCost (fork : Fork) (cold : Bool) : 1 ≤ extcodehashCost fork cold := by
  unfold extcodehashCost accountAccessCost gasSchedule
  repeat' split
  all_goals decide

/-- The price of SLOAD is at least 1 at every fork. -/
theorem one_le_sloadCost (fork : Fork) (cold : Bool) : 1 ≤ sloadCost fork cold := by
  unfold sloadCost
  repeat' split
  all_goals decide

/-- The price of SSTORE is at least 1 at every fork. -/
theorem one_le_sstoreCost (fork : Fork) (original current new : U256) (cold : Bool) :
    1 ≤ sstoreCost fork original current new cold := by
  unfold sstoreCost sstoreReadCost sstoreResetCost sloadCost
  repeat' split
  all_goals simp only [COLD_STORAGE_ACCESS, STORAGE_SET, COLD_STORAGE_WRITE, WARM_ACCESS]
  all_goals omega

variable [LawfulGasMeter Meter]

/-! ## The instructions that read and write only the stack, and KECCAK256 -/

/-- An instruction with one operand pays its price. -/
theorem unaryOp_pays {cost : Nat} {f : U256 → U256} {evm after : Evm fork Meter}
    (h : unaryOp cost f evm = .ok after) : Pays cost evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact ((((popWord_pays h1).trans (chargeGas_pays h2)).trans (pushWord_pays h3)).mono
    (m := cost) (by omega)).congr rfl rfl

/-- An instruction with two operands pays its price. -/
theorem binaryOp_pays {cost : Nat} {f : U256 → U256 → U256} {evm after : Evm fork Meter}
    (h : binaryOp cost f evm = .ok after) : Pays cost evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h4, h⟩ := except_bind_eq_ok h
  cases h
  exact (((((popWord_pays h1).trans (popWord_pays h2)).trans (chargeGas_pays h3)).trans
    (pushWord_pays h4)).mono (m := cost) (by omega)).congr rfl rfl

/-- An instruction with three operands pays its price. -/
theorem ternaryOp_pays {cost : Nat} {f : U256 → U256 → U256 → U256} {evm after : Evm fork Meter}
    (h : ternaryOp cost f evm = .ok after) : Pays cost evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h4, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h5, h⟩ := except_bind_eq_ok h
  cases h
  exact ((((((popWord_pays h1).trans (popWord_pays h2)).trans (popWord_pays h3)).trans
    (chargeGas_pays h4)).trans (pushWord_pays h5)).mono (m := cost) (by omega)).congr rfl rfl

/-- POP pays its price. -/
theorem popStep_pays {evm after : Evm fork Meter} (h : popStep evm = .ok after) :
    Pays OPCODE_POP evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  cases h
  exact (((popWord_pays h1).trans (chargeGas_pays h2)).mono (m := OPCODE_POP) (by omega)).congr
    rfl rfl

/-- PUSHn pays at least 1 gas. -/
theorem pushN_pays {n : Fin 33} {evm after : Evm fork Meter} (h : pushN n evm = .ok after) :
    Pays 1 evm after := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  cases h
  have price : 1 ≤ if n.val = 0 then OPCODE_PUSH0 else OPCODE_PUSH := by split <;> decide
  exact (((chargeGas_pays h1).trans (pushWord_pays h2)).mono (m := 1) (by omega)).congr rfl rfl

/-- DUPn pays its price. -/
theorem dupN_pays {n : Fin 16} {evm after : Evm fork Meter} (h : dupN n evm = .ok after) :
    Pays OPCODE_DUP evm after := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  split at h
  · cases h
  · obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
    cases h
    exact (((chargeGas_pays h1).trans (pushWord_pays h2)).mono (m := OPCODE_DUP) (by omega)).congr
      rfl rfl

/-- SWAPn pays its price. -/
theorem swapN_pays {n : Fin 16} {evm after : Evm fork Meter} (h : swapN n evm = .ok after) :
    Pays OPCODE_SWAP evm after := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  split at h
  · split at h
    · cases h
    · cases h
      exact (chargeGas_pays h1).congr rfl rfl
  · cases h

/-- DUPN pays its price. -/
theorem dupnStep_pays {evm after : Evm fork Meter} (h : dupnStep evm = .ok after) :
    Pays OPCODE_DUPN evm after := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  split at h
  · split at h
    · cases h
    · obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
      cases h
      exact (((chargeGas_pays h1).trans (pushWord_pays h2)).mono (m := OPCODE_DUPN)
        (by omega)).congr rfl rfl
  · cases h

/-- SWAPN pays its price. -/
theorem swapnStep_pays {evm after : Evm fork Meter} (h : swapnStep evm = .ok after) :
    Pays OPCODE_SWAPN evm after := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  split at h
  · split at h
    · cases h
      exact (chargeGas_pays h1).congr rfl rfl
    · cases h
  · cases h

/-- EXCHANGE pays its price. -/
theorem exchangeStep_pays {evm after : Evm fork Meter} (h : exchangeStep evm = .ok after) :
    Pays OPCODE_EXCHANGE evm after := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  split at h
  · split at h
    · cases h
      exact (chargeGas_pays h1).congr rfl rfl
    · cases h
  · cases h

/-- EXP pays at least its base price. -/
theorem expStep_pays {evm after : Evm fork Meter} (h : expStep fork evm = .ok after) :
    Pays OPCODE_EXP_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h4, h⟩ := except_bind_eq_ok h
  cases h
  exact (((((popWord_pays h1).trans (popWord_pays h2)).trans (chargeGas_pays h3)).trans
    (pushWord_pays h4)).mono (m := OPCODE_EXP_BASE) (by omega)).congr rfl rfl

/-- KECCAK256 pays at least its base price. -/
theorem keccak256Step_pays {evm after : Evm fork Meter} (h : keccak256Step evm = .ok after) :
    Pays OPCODE_KECCAK256_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h4, h⟩ := except_bind_eq_ok h
  cases h
  exact (((((popWord_pays h1).trans (popWord_pays h2)).trans (chargeGasAndMemory_pays h3)).trans
    (pushWord_pays h4)).mono (m := OPCODE_KECCAK256_BASE) (by omega)).congr rfl rfl

/-- Each instruction that reads and writes only the stack, and KECCAK256, lowers the measure. -/
theorem stackOnlyStep_measure_lt {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : stackOnlyStep fork op = some f) (h : f evm = .ok after) (running : evm.running = true) :
    measure after < measure evm := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hf
  all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf) <;>
    (try subst hf)
  all_goals first
    | cases hf
    | exact ((binaryOp_pays h).mono).measure_lt running
    | exact ((unaryOp_pays h).mono).measure_lt running
    | exact ((ternaryOp_pays h).mono).measure_lt running
    | exact ((expStep_pays h).mono).measure_lt running
    | exact ((keccak256Step_pays h).mono).measure_lt running
    | exact ((popStep_pays h).mono).measure_lt running
    | exact (pushN_pays h).measure_lt running
    | exact ((dupN_pays h).mono).measure_lt running
    | exact ((swapN_pays h).mono).measure_lt running
    | exact ((dupnStep_pays h).mono).measure_lt running
    | exact ((swapnStep_pays h).mono).measure_lt running
    | exact ((exchangeStep_pays h).mono).measure_lt running

/-! ## The instructions that move or read the program counter, and STOP -/

/-- An instruction that reads the frame pays its price. -/
theorem readFrame_pays {cost : Nat} {value : Evm fork Meter → U256} {evm after : Evm fork Meter}
    (h : readFrame cost value evm = .ok after) : Pays cost evm after := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  cases h
  exact (((chargeGas_pays h1).trans (pushWord_pays h2)).mono (m := cost) (by omega)).congr rfl rfl

/-- JUMP pays its price. -/
theorem jumpStep_pays {evm after : Evm fork Meter} (h : jumpStep evm = .ok after) :
    Pays OPCODE_JUMP evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  have paid := ((popWord_pays h1).trans (chargeGas_pays h2)).mono (m := OPCODE_JUMP) (by omega)
  split at h
  · cases h
    exact paid.congr rfl rfl
  · cases h

/-- JUMPI pays its price. -/
theorem jumpiStep_pays {evm after : Evm fork Meter} (h : jumpiStep evm = .ok after) :
    Pays OPCODE_JUMPI evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  have paid := (((popWord_pays h1).trans (popWord_pays h2)).trans (chargeGas_pays h3)).mono
    (m := OPCODE_JUMPI) (by omega)
  split at h
  · cases h
    exact paid.congr rfl rfl
  · split at h
    · cases h
      exact paid.congr rfl rfl
    · cases h

/-- JUMPDEST pays its price. -/
theorem jumpdestStep_pays {evm after : Evm fork Meter} (h : jumpdestStep evm = .ok after) :
    Pays OPCODE_JUMPDEST evm after := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  cases h
  exact (chargeGas_pays h1).congr rfl rfl

/-- Each instruction that moves or reads the program counter, and STOP, lowers the measure. -/
theorem controlFlowStep_measure_lt {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : controlFlowStep op = some f) (h : f evm = .ok after) (running : evm.running = true) :
    measure after < measure evm := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case stop =>
    cases h
    exact measure_lt_of_stop (Nat.le_refl _) rfl running
  all_goals first
    | exact ((readFrame_pays h).mono).measure_lt running
    | exact ((jumpStep_pays h).mono).measure_lt running
    | exact ((jumpiStep_pays h).mono).measure_lt running
    | exact ((jumpdestStep_pays h).mono).measure_lt running

/-! ## The instructions that move bytes to or from memory -/

/-- MLOAD pays its price. -/
theorem mloadStep_pays {evm after : Evm fork Meter} (h : mloadStep evm = .ok after) :
    Pays OPCODE_MLOAD_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact ((((popWord_pays h1).trans (chargeGasAndMemory_pays h2)).trans (pushWord_pays h3)).mono
    (m := OPCODE_MLOAD_BASE) (by omega)).congr rfl rfl

/-- MSTORE pays its price. -/
theorem mstoreStep_pays {evm after : Evm fork Meter} (h : mstoreStep evm = .ok after) :
    Pays OPCODE_MSTORE_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact ((((popWord_pays h1).trans (popWord_pays h2)).trans (chargeGasAndMemory_pays h3)).mono
    (m := OPCODE_MSTORE_BASE) (by omega)).congr rfl rfl

/-- MSTORE8 pays its price. -/
theorem mstore8Step_pays {evm after : Evm fork Meter} (h : mstore8Step evm = .ok after) :
    Pays OPCODE_MSTORE8_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact ((((popWord_pays h1).trans (popWord_pays h2)).trans (chargeGasAndMemory_pays h3)).mono
    (m := OPCODE_MSTORE8_BASE) (by omega)).congr rfl rfl

/-- MCOPY pays at least its base price. -/
theorem mcopyStep_pays {evm after : Evm fork Meter} (h : mcopyStep evm = .ok after) :
    Pays OPCODE_MCOPY_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h4, h⟩ := except_bind_eq_ok h
  cases h
  exact (((((popWord_pays h1).trans (popWord_pays h2)).trans (popWord_pays h3)).trans
    (chargeGasAndMemory_pays h4)).mono (m := OPCODE_MCOPY_BASE) (by omega)).congr rfl rfl

/-- CALLDATALOAD pays its price. -/
theorem calldataloadStep_pays {evm after : Evm fork Meter}
    (h : calldataloadStep evm = .ok after) : Pays OPCODE_CALLDATALOAD evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact ((((popWord_pays h1).trans (chargeGas_pays h2)).trans (pushWord_pays h3)).mono
    (m := OPCODE_CALLDATALOAD) (by omega)).congr rfl rfl

/-- A copy to memory pays at least its base price. -/
theorem copyToMemory_pays {base : Nat} {source : ByteArray} {evm after : Evm fork Meter}
    (h : copyToMemory base source evm = .ok after) : Pays base evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h4, h⟩ := except_bind_eq_ok h
  cases h
  exact (((((popWord_pays h1).trans (popWord_pays h2)).trans (popWord_pays h3)).trans
    (chargeGasAndMemory_pays h4)).mono (m := base) (by omega)).congr rfl rfl

/-- RETURNDATACOPY pays at least its base price. -/
theorem returndatacopyStep_pays {evm after : Evm fork Meter}
    (h : returndatacopyStep evm = .ok after) : Pays OPCODE_RETURNDATACOPY_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h4, h⟩ := except_bind_eq_ok h
  have paid := ((((popWord_pays h1).trans (popWord_pays h2)).trans (popWord_pays h3)).trans
    (chargeGas_pays h4)).mono (m := OPCODE_RETURNDATACOPY_BASE) (by omega)
  split at h
  · cases h
  · cases h
    exact paid.congr rfl rfl

/-- Each instruction that moves bytes to or from memory lowers the measure. -/
theorem memoryDataStep_measure_lt {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : memoryDataStep op = some f) (h : f evm = .ok after) (running : evm.running = true) :
    measure after < measure evm := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case mload => exact ((mloadStep_pays h).mono).measure_lt running
  case mstore => exact ((mstoreStep_pays h).mono).measure_lt running
  case mstore8 => exact ((mstore8Step_pays h).mono).measure_lt running
  case mcopy => exact ((mcopyStep_pays h).mono).measure_lt running
  case calldataload => exact ((calldataloadStep_pays h).mono).measure_lt running
  case calldatacopy | codecopy => exact ((copyToMemory_pays h).mono).measure_lt running
  case returndatacopy => exact ((returndatacopyStep_pays h).mono).measure_lt running
  all_goals exact ((readFrame_pays h).mono).measure_lt running

/-! ## RETURN and REVERT -/

/-- A halt with output stops the frame, with no more gas. -/
theorem haltWithOutput_stops {evm after : Evm fork Meter} (h : haltWithOutput evm = .ok after) :
    GasMeter.gasLeft after.gas ≤ GasMeter.gasLeft evm.gas ∧ after.running = false := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  have := (((popWord_pays h1).trans (popWord_pays h2)).trans (chargeGasAndMemory_pays h3)).gasLeft
  exact ⟨by simp only at this ⊢; omega, rfl⟩

/-- RETURN and REVERT lower the measure. -/
theorem returnOpStep_measure_lt {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : returnOpStep fork op = some f) (h : f evm = .ok after) (running : evm.running = true) :
    measure after < measure evm := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hf
  · subst hf
    obtain ⟨gas, stops⟩ := haltWithOutput_stops h
    exact measure_lt_of_stop gas stops running
  · split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
      cases h
      obtain ⟨gas, stops⟩ := haltWithOutput_stops h1
      exact measure_lt_of_stop gas stops running
    · cases hf

/-! ## The instructions that read the environment -/

/-- BLOCKHASH pays its price. -/
theorem blockhashStep_pays {evm after : Evm fork Meter} (h : blockhashStep evm = .ok after) :
    Pays OPCODE_BLOCKHASH evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact ((((popWord_pays h1).trans (chargeGas_pays h2)).trans (pushWord_pays h3)).mono
    (m := OPCODE_BLOCKHASH) (by omega)).congr rfl rfl

/-- BLOBHASH pays its price. -/
theorem blobhashStep_pays {hf : .dencun ≤ fork} {evm after : Evm fork Meter}
    (h : blobhashStep hf evm = .ok after) : Pays OPCODE_BLOBHASH evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact ((((popWord_pays h1).trans (chargeGas_pays h2)).trans (pushWord_pays h3)).mono
    (m := OPCODE_BLOBHASH) (by omega)).congr rfl rfl

/-- Each instruction that reads the environment lowers the measure. -/
theorem environmentStep_measure_lt {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : environmentStep fork op = some f) (h : f evm = .ok after)
    (running : evm.running = true) : measure after < measure evm := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hf
  case blockhash =>
    subst hf
    exact ((blockhashStep_pays h).mono).measure_lt running
  case blobhash =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact ((blobhashStep_pays h).mono).measure_lt running
    · cases hf
  all_goals (repeat' split at hf) <;> (try simp only [Option.some.injEq] at hf) <;> (try subst hf)
  all_goals first
    | cases hf
    | exact ((readFrame_pays h).mono).measure_lt running

/-! ## The instructions that read another account -/

/-- BALANCE pays at least 1 gas. -/
theorem balanceStep_pays {evm after : Evm fork Meter} (h : balanceStep evm = .ok after) :
    Pays 1 evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact (((((popWord_pays h1).trans (accessAddress_pays _ _)).trans (chargeGas_pays h2)).trans
    (pushWord_pays h3)).mono (m := 1)
    (by simp only [Nat.zero_add, Nat.add_zero]; exact one_le_balanceCost _ _)).congr rfl rfl

/-- EXTCODESIZE pays at least 1 gas. -/
theorem extcodesizeStep_pays {evm after : Evm fork Meter} (h : extcodesizeStep evm = .ok after) :
    Pays 1 evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact (((((popWord_pays h1).trans (accessAddress_pays _ _)).trans (chargeGas_pays h2)).trans
    (pushWord_pays h3)).mono (m := 1)
    (by simp only [Nat.zero_add, Nat.add_zero]; exact one_le_externalBaseCost _ _)).congr rfl rfl

/-- EXTCODECOPY pays at least 1 gas. -/
theorem extcodecopyStep_pays {evm after : Evm fork Meter} (h : extcodecopyStep evm = .ok after) :
    Pays 1 evm after := by
  obtain ⟨⟨word, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h5, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  cases h
  exact ((((((popWord_pays h1).trans (popWord_pays h2)).trans (popWord_pays h3)).trans
    (popWord_pays h4)).trans ((accessAddress_pays _ _).trans (chargeGasAndMemory_pays h5))).mono
    (m := 1) (by
      simp only [Nat.zero_add, Nat.add_zero]
      exact Nat.le_trans (one_le_externalBaseCost _ _) (Nat.le_add_right _ _))).congr rfl rfl

/-- EXTCODEHASH pays at least 1 gas. -/
theorem extcodehashStep_pays {evm after : Evm fork Meter} (h : extcodehashStep evm = .ok after) :
    Pays 1 evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact (((((popWord_pays h1).trans (accessAddress_pays _ _)).trans (chargeGas_pays h2)).trans
    (pushWord_pays h3)).mono (m := 1)
    (by simp only [Nat.zero_add, Nat.add_zero]; exact one_le_extcodehashCost _ _)).congr rfl rfl

/-- Each instruction that reads another account lowers the measure. -/
theorem accountStep_measure_lt {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : accountStep fork op = some f) (h : f evm = .ok after) (running : evm.running = true) :
    measure after < measure evm := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hf
  case balance =>
    subst hf
    exact (balanceStep_pays h).measure_lt running
  case extcodesize =>
    subst hf
    exact (extcodesizeStep_pays h).measure_lt running
  case extcodecopy =>
    subst hf
    exact (extcodecopyStep_pays h).measure_lt running
  case extcodehash =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact (extcodehashStep_pays h).measure_lt running
    · cases hf
  case selfbalance =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact ((readFrame_pays h).mono).measure_lt running
    · cases hf

/-! ## The instructions that use storage -/

/-- SLOAD pays at least 1 gas. -/
theorem sloadStep_pays {evm after : Evm fork Meter} (h : sloadStep evm = .ok after) :
    Pays 1 evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact (((((popWord_pays h1).trans (accessStorageKey_pays _ _ _)).trans
    (chargeGas_pays h2)).trans (pushWord_pays h3)).mono (m := 1)
    (by simp only [Nat.zero_add, Nat.add_zero]; exact one_le_sloadCost _ _)).congr rfl rfl

/-- SSTORE pays at least 1 gas. -/
theorem sstoreStep_pays {evm after : Evm fork Meter} (h : sstoreStep evm = .ok after) :
    Pays 1 evm after := by
  obtain ⟨⟨word, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨new, e2⟩, h2, h⟩ := except_bind_eq_ok h
  dsimp only at h
  split at h <;> try (cases h; done)
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  split at h <;> try (cases h; done)
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  cases h
  exact (((((popWord_pays h1).trans (popWord_pays h2)).trans
    (accessStorageKey_pays _ _ _)).trans (chargeGas_pays h3)).mono (m := 1)
    (by simp only [Nat.zero_add, Nat.add_zero]; exact one_le_sstoreCost _ _ _ _ _)).congr rfl rfl

/-- SLOAD and SSTORE lower the measure. -/
theorem storageStep_measure_lt {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : storageStep op = some f) (h : f evm = .ok after) (running : evm.running = true) :
    measure after < measure evm := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case sload => exact (sloadStep_pays h).measure_lt running
  case sstore => exact (sstoreStep_pays h).measure_lt running

/-! ## The instructions of transient storage -/

/-- TLOAD pays its price. -/
theorem tloadStep_pays {evm after : Evm fork Meter} (h : tloadStep evm = .ok after) :
    Pays OPCODE_TLOAD evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact ((((popWord_pays h1).trans (chargeGas_pays h2)).trans (pushWord_pays h3)).mono
    (m := OPCODE_TLOAD) (by omega)).congr rfl rfl

/-- TSTORE pays its price. -/
theorem tstoreStep_pays {evm after : Evm fork Meter} (h : tstoreStep evm = .ok after) :
    Pays OPCODE_TSTORE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  split at h
  · cases h
  · cases h
    exact ((((popWord_pays h1).trans (popWord_pays h2)).trans (chargeGas_pays h3)).mono
      (m := OPCODE_TSTORE) (by omega)).congr rfl rfl

/-- TLOAD and TSTORE lower the measure. -/
theorem transientStorageStep_measure_lt {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : transientStorageStep fork op = some f) (h : f evm = .ok after)
    (running : evm.running = true) : measure after < measure evm := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf
  case tload =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact ((tloadStep_pays h).mono).measure_lt running
    · cases hf
  case tstore =>
    split at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact ((tstoreStep_pays h).mono).measure_lt running
    · cases hf

/-! ## The LOG instructions -/

/-- LOGn pays at least its base price. -/
theorem logStep_pays {n : Nat} {evm after : Evm fork Meter} (h : logStep n evm = .ok after) :
    Pays OPCODE_LOG_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h4, h⟩ := except_bind_eq_ok h
  split at h
  · cases h
  · cases h
    exact (((((popWord_pays h1).trans (popWord_pays h2)).trans (popTopics_pays h3)).trans
      (chargeGasAndMemory_pays h4)).mono (m := OPCODE_LOG_BASE) (by omega)).congr rfl rfl

/-- Each LOG instruction lowers the measure. -/
theorem logOpStep_measure_lt {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : logOpStep op = some f) (h : f evm = .ok after) (running : evm.running = true) :
    measure after < measure evm := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
  case log =>
    subst hf
    exact ((logStep_pays h).mono).measure_lt running

end EthLib.Execution.Evm

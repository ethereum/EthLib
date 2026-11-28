module

public import EthLib.Execution.Proofs.Evm.OpTables.Instructions
public import EthLib.Execution.Proofs.Evm.OpTables.Messages
public import EthLib.Execution.Proofs.Evm.Call.ChildGas

/-!
# Proofs: with the meter of state gas, a step that goes on had the gas left for its price

The first charge of each instruction holds its whole constant price.

Nothing before that charge changes the meter, so the gas left covers the price.

SSTORE first checks the stipend, and a refill before its charge gives back nothing before Istanbul.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open GasCosts

variable {fork : Fork}

/-! ## The parts that keep the meter -/

section Keep

variable {Meter : Type}

/-- A pop keeps the meter. -/
theorem gas_popWord {evm after : Evm fork Meter} {x : U256}
    (h : popWord evm = .ok (x, after)) : after.gas = evm.gas := by
  obtain ⟨⟨_, _⟩, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rfl

/-- An access to an address keeps the meter. -/
theorem gas_accessAddress (evm : Evm fork Meter) (address : Address) :
    (accessAddress evm address).2.gas = evm.gas := by
  unfold accessAddress
  split <;> rfl

/-- An access to a slot keeps the meter. -/
theorem gas_accessStorageKey (evm : Evm fork Meter) (address : Address) (key : Base.Bytes32) :
    (accessStorageKey evm address key).2.gas = evm.gas := by
  unfold accessStorageKey
  split <;> rfl

/-- The pops of the topics of a log keep the meter. -/
theorem gas_popTopics {evm after : Evm fork Meter} {n : Nat}
    {topics : List EthLib.Base.Hash32} (h : popTopics evm n = .ok (topics, after)) :
    after.gas = evm.gas := by
  induction n generalizing evm topics with
  | zero =>
    cases h
    rfl
  | succ k ih =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (ih h2).trans (gas_popWord h1)

/-- The pop of the salt of a creation keeps the meter. -/
theorem gas_popSalt {create2 : Bool} {evm after : Evm fork Meter} {salt : Option U256}
    (h : popSalt create2 evm = .ok (salt, after)) : after.gas = evm.gas := by
  unfold popSalt at h
  cases create2
  · cases h
    rfl
  · obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact gas_popWord h1

end Keep

/-! ## The first charge -/

/-- A charge with the growth of memory that succeeds has its price within the gas left. -/
theorem le_gasLeft_of_chargeGasAndMemory {evm after : Evm fork StateGasMeter} {cost : Nat}
    {ranges : List (U256 × U256)} (h : chargeGasAndMemory evm cost ranges = .ok after) :
    cost ≤ GasMeter.gasLeft evm.gas := by
  obtain ⟨_, h1, -⟩ := Base.bind_ok_iff.mp h
  have := le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h1
  omega

/-- An instruction that reads the frame had the gas left for its price. -/
theorem readFrame_covers {cost : Nat} {value : Evm fork StateGasMeter → U256}
    {evm after : Evm fork StateGasMeter} (h : readFrame cost value evm = .ok after) :
    cost ≤ GasMeter.gasLeft evm.gas := by
  obtain ⟨_, h1, -⟩ := Base.bind_ok_iff.mp h
  exact le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h1

/-- An instruction that reads a number had the gas left for its price. -/
theorem readNumber_covers {cost : Nat} {value : Evm fork StateGasMeter → Nat}
    {evm after : Evm fork StateGasMeter} (h : readNumber cost value evm = .ok after) :
    cost ≤ GasMeter.gasLeft evm.gas := by
  unfold readNumber at h
  split at h
  · exact readFrame_covers h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h

/-- A charge after parts that keep the meter is within the gas left at the start. -/
theorem pops_covers {evm mid after : Evm fork StateGasMeter} {cost : Nat}
    (hgas : mid.gas = evm.gas) (h : chargeGas mid cost = .ok after) :
    cost ≤ GasMeter.gasLeft evm.gas :=
  hgas ▸ le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h

/-- A charge with memory after parts that keep the meter is within the gas left at the start. -/
theorem pops_coversMemory {evm mid after : Evm fork StateGasMeter} {cost : Nat}
    {ranges : List (U256 × U256)} (hgas : mid.gas = evm.gas)
    (h : chargeGasAndMemory mid cost ranges = .ok after) : cost ≤ GasMeter.gasLeft evm.gas :=
  hgas ▸ le_gasLeft_of_chargeGasAndMemory h

/-- An instruction with one operand had the gas left for its price. -/
theorem unaryOp_covers {cost : Nat} {f : U256 → U256} {evm after : Evm fork StateGasMeter}
    (h : unaryOp cost f evm = .ok after) : cost ≤ GasMeter.gasLeft evm.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
  exact pops_covers (gas_popWord h1) h2

/-- An instruction with two operands had the gas left for its price. -/
theorem binaryOp_covers {cost : Nat} {f : U256 → U256 → U256}
    {evm after : Evm fork StateGasMeter} (h : binaryOp cost f evm = .ok after) :
    cost ≤ GasMeter.gasLeft evm.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, -⟩ := Base.bind_ok_iff.mp h
  exact pops_covers ((gas_popWord h2).trans (gas_popWord h1)) h3

/-- An instruction with three operands had the gas left for its price. -/
theorem ternaryOp_covers {cost : Nat} {f : U256 → U256 → U256 → U256}
    {evm after : Evm fork StateGasMeter} (h : ternaryOp cost f evm = .ok after) :
    cost ≤ GasMeter.gasLeft evm.gas := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, -⟩ := Base.bind_ok_iff.mp h
  exact pops_covers (((gas_popWord h3).trans (gas_popWord h2)).trans (gas_popWord h1)) h4

/-! ## The instructions of the stack -/

/-- Each instruction that reads and writes only the stack had the gas left for its price. -/
theorem stackOnlyStep_covers {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter} (hf : stackOnlyStep fork op = some f)
    (h : f evm = .ok after) : op.constantGas fork ≤ GasMeter.gasLeft evm.gas := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hf
  all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf) <;>
    (try subst hf)
  case push n =>
    rw [constantGas_push]
    obtain ⟨_, h1, -⟩ := Base.bind_ok_iff.mp h
    exact le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h1
  case exp =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, -⟩ := Base.bind_ok_iff.mp h
    have := pops_covers ((gas_popWord h2).trans (gas_popWord h1)) h3
    simp only [Op.constantGas]
    omega
  case keccak256 =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, -⟩ := Base.bind_ok_iff.mp h
    have := le_gasLeft_of_chargeGasAndMemory h3
    rw [gas_popWord h2, gas_popWord h1] at this
    simp only [Op.constantGas]
    simp only [keccak256Cost] at this
    omega
  case pop =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
    exact pops_covers (gas_popWord h1) h2
  case dup n =>
    obtain ⟨_, h1, -⟩ := Base.bind_ok_iff.mp h
    exact le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h1
  case swap n =>
    obtain ⟨_, h1, -⟩ := Base.bind_ok_iff.mp h
    exact le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h1
  case dupn.isTrue =>
    obtain ⟨_, h1, -⟩ := Base.bind_ok_iff.mp h
    exact le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h1
  case swapn.isTrue =>
    obtain ⟨_, h1, -⟩ := Base.bind_ok_iff.mp h
    exact le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h1
  case exchange.isTrue =>
    obtain ⟨_, h1, -⟩ := Base.bind_ok_iff.mp h
    exact le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h1
  all_goals first
    | cases hf
    | exact binaryOp_covers h
    | exact unaryOp_covers h
    | exact ternaryOp_covers h

/-! ## Control flow, memory, the environment and RETURN -/

/-- Each instruction of control flow had the gas left for its price. -/
theorem controlFlowStep_covers {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter} (hf : controlFlowStep op = some f)
    (h : f evm = .ok after) : op.constantGas fork ≤ GasMeter.gasLeft evm.gas := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case stop => exact Nat.zero_le _
  case jump =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
    exact pops_covers (gas_popWord h1) h2
  case jumpi =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, -⟩ := Base.bind_ok_iff.mp h
    exact pops_covers ((gas_popWord h2).trans (gas_popWord h1)) h3
  case jumpdest =>
    obtain ⟨_, h1, -⟩ := Base.bind_ok_iff.mp h
    exact le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h1
  all_goals exact readFrame_covers h

/-- Three pops, then a charge with the growth of memory, had the gas left for the charge. -/
theorem pop3_covers {evm e1 e2 e3 after : Evm fork StateGasMeter} {x y z : U256} {cost : Nat}
    {ranges : List (U256 × U256)} (h1 : popWord evm = .ok (x, e1))
    (h2 : popWord e1 = .ok (y, e2)) (h3 : popWord e2 = .ok (z, e3))
    (h4 : chargeGasAndMemory e3 cost ranges = .ok after) : cost ≤ GasMeter.gasLeft evm.gas := by
  have := le_gasLeft_of_chargeGasAndMemory h4
  rwa [gas_popWord h3, gas_popWord h2, gas_popWord h1] at this

/-- Each instruction that moves bytes to or from memory had the gas left for its price. -/
theorem memoryDataStep_covers {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter} (hf : memoryDataStep op = some f)
    (h : f evm = .ok after) : op.constantGas fork ≤ GasMeter.gasLeft evm.gas := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case mload =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
    have := le_gasLeft_of_chargeGasAndMemory h2
    rwa [gas_popWord h1] at this
  case mstore | mstore8 =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, -⟩ := Base.bind_ok_iff.mp h
    have := le_gasLeft_of_chargeGasAndMemory h3
    rwa [gas_popWord h2, gas_popWord h1] at this
  case mcopy | calldatacopy | codecopy =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, -⟩ := Base.bind_ok_iff.mp h
    have := pop3_covers h1 h2 h3 h4
    simp only [Op.constantGas]
    omega
  case calldataload =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
    exact pops_covers (gas_popWord h1) h2
  case returndatacopy =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, -⟩ := Base.bind_ok_iff.mp h
    have := pops_covers (((gas_popWord h3).trans (gas_popWord h2)).trans (gas_popWord h1)) h4
    simp only [Op.constantGas]
    omega
  all_goals exact readFrame_covers h

/-- RETURN and REVERT have no constant price. -/
theorem returnOpStep_covers {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm : Evm fork StateGasMeter} (hf : returnOpStep fork op = some f) :
    op.constantGas fork ≤ GasMeter.gasLeft evm.gas := by
  cases op <;> simp only [returnOpStep, reduceCtorEq] at hf <;> exact Nat.zero_le _

/-- Each instruction that reads the environment had the gas left for its price. -/
theorem environmentStep_covers {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter} (hf : environmentStep fork op = some f)
    (h : f evm = .ok after) : op.constantGas fork ≤ GasMeter.gasLeft evm.gas := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hf
  all_goals (repeat' split at hf) <;> (try simp only [Option.some.injEq] at hf) <;> (try subst hf)
  case blockhash | blobhash.isTrue =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
    exact pops_covers (gas_popWord h1) h2
  all_goals first
    | cases hf
    | exact readFrame_covers h
    | exact readNumber_covers h

/-! ## Accounts, storage and logs -/

/-- Each instruction that reads another account had the gas left for its price. -/
theorem accountStep_covers {op : Op}
    {f : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter} (hf : accountStep fork op = some f)
    (h : f evm = .ok after) : op.constantGas fork ≤ GasMeter.gasLeft evm.gas := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hf
  all_goals (repeat' split at hf) <;> (try simp only [Option.some.injEq] at hf) <;> (try subst hf)
  case balance =>
    obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
    have := pops_covers ((gas_accessAddress _ _).trans (gas_popWord h1)) h2
    exact Nat.le_trans (balanceCost_le _ _) this
  case extcodesize =>
    obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
    have := pops_covers ((gas_accessAddress _ _).trans (gas_popWord h1)) h2
    exact Nat.le_trans (externalBaseCost_le _ _) this
  case extcodehash.isTrue =>
    obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
    have := pops_covers ((gas_accessAddress _ _).trans (gas_popWord h1)) h2
    exact Nat.le_trans (extcodehashCost_le _ _) this
  case extcodecopy =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h5, -⟩ := Base.bind_ok_iff.mp h
    have g : e4.gas = evm.gas :=
      ((gas_popWord h4).trans (gas_popWord h3)).trans ((gas_popWord h2).trans (gas_popWord h1))
    exact Nat.le_trans (externalBaseCost_le _ _) (Nat.le_trans (Nat.le_add_right _ _)
      (pops_coversMemory ((gas_accessAddress _ _).trans g) h5))
  case selfbalance.isTrue =>
    dsimp only at h
    exact readFrame_covers (evm := recordAccountRead evm evm.message.currentTarget) h
  all_goals cases hf

/-- SSTORE from Istanbul costs at most the stipend that it checks first. -/
theorem constantGas_sstore_le_stipend (h : fork ≥ .istanbul) :
    Op.constantGas fork .sstore ≤ CALL_STIPEND := by
  revert h
  cases fork <;> decide

/-- SSTORE had the gas left for its price, or halted once it read the slot. -/
theorem sstoreStep_covers {evm after : Evm fork StateGasMeter} (h : sstoreStep evm = .ok after) :
    Op.constantGas fork .sstore ≤ GasMeter.gasLeft evm.gas ∨
      ∃ mid e, e.aborts = false ∧ after = exceptionalHalt mid e := by
  unfold sstoreStep at h
  split at h
  · cases h
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨new, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have g2 : e2.gas = evm.gas := (gas_popWord h2).trans (gas_popWord h1)
  dsimp only at h
  split at h
  · cases h
  rename_i hstipend
  by_cases hi : fork ≥ .istanbul
  · -- From Istanbul, the gas left is above the stipend.
    left
    have := constantGas_sstore_le_stipend hi
    have : ¬GasMeter.gasLeft e2.gas ≤ CALL_STIPEND := fun hl => hstipend ⟨hi, hl⟩
    rw [← g2]
    omega
  rcases keepReads_eq_ok_halt h with h | ⟨e, -, he, rfl⟩
  · -- Before Istanbul, the refill gives back nothing, so the charge is within the gas left.
    left
    obtain ⟨_, h3, -⟩ := Base.bind_ok_iff.mp h
    have hc := le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h3
    have hr : sstoreStateRefill fork (e2.state.getStorageOriginal e2.message.currentTarget
        (U256.toBeBytes word)) (e2.state.getStorage e2.message.currentTarget
        (U256.toBeBytes word)) new = 0 := by
      -- Before Istanbul, no write refills state gas.
      simp [sstoreStateRefill, sstoreCase, hi]
    simp only [refillStateGas, hr, gasLeft_refill_zero_stateGas, recordStorageRead,
      gas_accessStorageKey, g2] at hc
    exact Nat.le_trans (constantGas_sstore_le _ _ _ _ _) hc
  · exact .inr ⟨_, e, he, rfl⟩

/-- SELFDESTRUCT had the gas left for its price, or halted once it read the beneficiary. -/
theorem selfdestructStep_covers {evm after : Evm fork StateGasMeter}
    (h : selfdestructStep fork evm = .ok after) :
    (gasSchedule fork).OPCODE_SELFDESTRUCT_BASE ≤ GasMeter.gasLeft evm.gas ∨
      ∃ mid e, e.aborts = false ∧ after = exceptionalHalt mid e := by
  unfold selfdestructStep at h
  split at h
  · cases h
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok_halt h with h | ⟨e, -, he, rfl⟩
  · left
    obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
    have := le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h2
    simp only [recordAccountRead, gas_accessAddress, gas_popWord h1, selfdestructCost] at this
    omega
  · exact .inr ⟨_, e, he, rfl⟩

/-- Each instruction that gives the next frame had the gas left for its price, or halted. -/
theorem instruction_covers {op : Op}
    {run : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter} (hrun : instruction fork op = some run)
    (h : run evm = .ok after) :
    op.constantGas fork ≤ GasMeter.gasLeft evm.gas ∨
      ∃ mid e, e.aborts = false ∧ after = exceptionalHalt mid e := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact .inl (stackOnlyStep_covers hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact .inl (controlFlowStep_covers hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact .inl (memoryDataStep_covers hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact .inl (returnOpStep_covers hf)
  rcases orElse_eq_some hrun with hf | hrun
  · exact .inl (environmentStep_covers hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact .inl (accountStep_covers hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · left
      obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
      have := pops_covers ((gas_accessStorageKey _ _ _).trans (gas_popWord h1)) h2
      exact Nat.le_trans (sloadCost_le _ _) this
    · exact sstoreStep_covers h
  rcases orElse_eq_some hrun with hf | hrun
  · left
    cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨_, h2, -⟩ := Base.bind_ok_iff.mp h
      exact pops_covers (gas_popWord h1) h2
    · obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨_, h3, -⟩ := Base.bind_ok_iff.mp h
      exact pops_covers ((gas_popWord h2).trans (gas_popWord h1)) h3
  rcases orElse_eq_some hrun with hf | hf
  · left
    cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, -⟩ := Base.bind_ok_iff.mp h
    have := le_gasLeft_of_chargeGasAndMemory h4
    rw [gas_popTopics h3, gas_popWord h2, gas_popWord h1] at this
    simp only [Op.constantGas, logCost] at this ⊢
    omega
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact selfdestructStep_covers h

/-! ## The calls and the creations -/

/-- A call that pays had its extra price within the gas left. -/
theorem le_gasLeft_of_payCall {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork StateGasMeter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    extraGas ≤ GasMeter.gasLeft evm.gas := by
  unfold payCall at h
  split at h
  · obtain ⟨_, h1, -⟩ := Base.bind_ok_iff.mp h
    have := le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h1
    omega
  · obtain ⟨_, h1, -⟩ := Base.bind_ok_iff.mp h
    have := le_gasLeft_of_chargeGas charge_le_gasLeft_stateGas h1
    unfold messageCallGas at this
    dsimp only at this
    omega

/-- A call had the gas left for its price, or halted once it read the state. -/
theorem callStep_covers {kind : CallKind} {evm : Evm fork StateGasMeter}
    {result : StepResult fork StateGasMeter} (h : callStep kind evm = .ok result) :
    callBaseCost fork false ≤ GasMeter.gasLeft evm.gas ∨
      ∃ mid e, e.aborts = false ∧ result = .next (exceptionalHalt mid e) := by
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  have g2 : e2.gas = evm.gas := by
    have := gas_accessAddress e1 call.address
    rw [hacc] at this
    rw [this, popCallOperands_eq_ok h1]
  rw [hacc] at h
  dsimp only at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok_halt h with h | ⟨e, -, he, rfl⟩
  · obtain ⟨⟨callee, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    rcases keepReads_eq_ok_halt h with h | ⟨e, -, he, rfl⟩
    · obtain ⟨⟨subCall, e4⟩, h4, -⟩ := Base.bind_ok_iff.mp h
      left
      have := le_gasLeft_of_payCall h4
      have bounds := callBaseCost_le_callExtraGas (fork := fork) (kind := kind)
        (state := e3.state) (call := call) (cold := cold) (callee := callee)
      rw [gas_accessDelegation h3] at this
      change _ ≤ GasMeter.gasLeft e2.gas at this
      rw [g2] at this
      dsimp only at this
      omega
    · exact .inr ⟨_, e, he, rfl⟩
  · exact .inr ⟨_, e, he, rfl⟩

/-- A creation had the gas left for its price. -/
theorem createStep_covers {create2 : Bool} {evm : Evm fork StateGasMeter}
    {result : StepResult fork StateGasMeter} (h : createStep create2 evm = .ok result) :
    createBaseCost fork ≤ GasMeter.gasLeft evm.gas := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h5, -⟩ := Base.bind_ok_iff.mp h
  have := pops_coversMemory ((gas_popSalt h4).trans ((gas_popWord h3).trans
    ((gas_popWord h2).trans (gas_popWord h1)))) h5
  omega

/-- Each instruction that may send a message had the gas left for its price, or halted. -/
theorem messageInstruction_covers {op : Op}
    {run : Evm fork StateGasMeter → Except EvmError (StepResult fork StateGasMeter)}
    {evm : Evm fork StateGasMeter} {result : StepResult fork StateGasMeter}
    (hrun : messageInstruction fork op = some run) (h : run evm = .ok result) :
    op.constantGas fork ≤ GasMeter.gasLeft evm.gas ∨
      ∃ mid e, e.aborts = false ∧ result = .next (exceptionalHalt mid e) := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := StateGasMeter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact callStep_covers h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact callStep_covers h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact .inl (createStep_covers h))
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact .inl (createStep_covers h)
         · cases hrun)

end EthLib.Execution.Evm

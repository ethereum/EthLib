module

public import EthLib.Execution.Proofs.Evm.Call.NonceOrCodeFreshSlots
public import EthLib.Execution.Proofs.Evm.Gas.StateGas

/-!
# Proofs: a frame pays for the slots it counts

The meter of [EIP-8037][eip8037] counts the net state gas of a frame, which can be negative.

The slots counted are the fresh slots of the accounts with a nonce or code.

The surplus of a frame is its net state gas, less the state gas of a new slot for each such slot.

A frame fails when it stops with an error, and its meter has rolled back unless it reverted.

The message that ran the frame then puts back the state from before it.

A frame pays for its slots from an earlier frame when it failed, or when its surplus did not drop.

Its surplus is then compared only when the earlier frame had no error, and it then has none.

That relation is a preorder, and an exceptional halt pays for its slots.

A running frame pays when it keeps its error and its surplus does not drop.

Every frame pays from a frame with an error that has not failed.

The relation compares no meters.

A run keeps the starting reservoir, the baseline and the committed spill, proved apart.

A message pays when its last frame keeps the starting reservoir and committed spill of its meter.

Its net state gas must then be at least a floor, plus the state gas of the slots it adds.

The floor is the least of the net state gas of its meter and that of its meter rolled back.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- The net state gas of a frame, less the state gas of a new slot for each slot it counts. -/
def slotSurplus (evm : Evm fork StateGasMeter) : Int :=
  evm.gas.stateGasUsed - STORAGE_SET_STATE_GAS * (nonceOrCodeFreshSlots evm.state).card

/-- A frame that stops with an error.

Unless it reverted, its meter has no spill and its reservoir is at its baseline. -/
def FailedFrame (evm : Evm fork StateGasMeter) : Prop :=
  evm.running = false ∧ evm.error ≠ none ∧
    (evm.error = some .revert ∨ (evm.gas.spill = 0 ∧ evm.gas.reservoir = evm.gas.baseline))

/-- The frame `b` pays for its slots from the frame `a`.

Either `b` failed, or `a` did not fail.

In the second case, when `a` has no error, `b` has none and a surplus at least that of `a`. -/
def PaysSlots (a b : Evm fork StateGasMeter) : Prop :=
  FailedFrame b ∨
    (¬FailedFrame a ∧ (a.error = none → b.error = none ∧ slotSurplus a ≤ slotSurplus b))

/-- Every frame pays for its slots from itself. -/
theorem PaysSlots.refl (evm : Evm fork StateGasMeter) : PaysSlots evm evm := by
  -- A failed frame pays by its failure, and any other frame by its own surplus.
  by_cases h : FailedFrame evm
  · exact Or.inl h
  · exact Or.inr ⟨h, fun herr => ⟨herr, le_rfl⟩⟩

/-- A frame that pays from one that pays from a third pays from the third. -/
theorem PaysSlots.trans {a b c : Evm fork StateGasMeter} (hab : PaysSlots a b)
    (hbc : PaysSlots b c) : PaysSlots a c := by
  rcases hbc with hc | ⟨hb, hbc⟩
  · exact Or.inl hc
  · rcases hab with hb' | ⟨ha, hab⟩
    -- The middle frame cannot both fail and not fail.
    · exact absurd hb' hb
    -- Without an error, the surpluses chain from the first frame to the last.
    · refine Or.inr ⟨ha, fun herr => ?_⟩
      obtain ⟨hberr, hle⟩ := hab herr
      obtain ⟨hcerr, hle'⟩ := hbc hberr
      exact ⟨hcerr, hle.trans hle'⟩

/-- An exceptional halt fails, so it pays for its slots from every frame. -/
theorem paysSlots_exceptionalHalt (a evm : Evm fork StateGasMeter) (error : EvmError) :
    PaysSlots a (exceptionalHalt evm error) := by
  -- The halt stops with an error, and its meter has rolled back to the baseline.
  refine Or.inl ⟨rfl, by simp [exceptionalHalt], Or.inr ⟨rfl, rfl⟩⟩

/-- A frame pays from a running frame when it keeps its error and its surplus does not drop. -/
theorem PaysSlots.of_le {a b : Evm fork StateGasMeter} (running : a.running = true)
    (herr : b.error = a.error) (hle : slotSurplus a ≤ slotSurplus b) : PaysSlots a b := by
  -- A running frame has not failed, and its error passes on to the later frame.
  refine Or.inr ⟨fun hf => by simp [hf.1] at running, fun hnone => ⟨herr.trans hnone, hle⟩⟩

/-- A message pays for its slots, from the state and the meter it starts with.

The frame that ends it keeps the starting reservoir and the committed spill of the meter.

Its net state gas is at least the floor plus the state gas of a new slot for each slot it adds.

The floor is the least of the net state gas of the meter and that of the meter rolled back.

The message and the substate are not read; they give the form of a relation of messages. -/
def MessagePays (_message : Message fork) (state : TransactionState) (_substate : Substate)
    (meter : StateGasMeter) (ended : Evm fork StateGasMeter) : Prop :=
  ended.gas.grant = meter.grant ∧ ended.gas.committed = meter.committed ∧
    min meter.stateGasUsed meter.restore.stateGasUsed +
        STORAGE_SET_STATE_GAS *
          (((nonceOrCodeFreshSlots ended.state).card : Int) - (nonceOrCodeFreshSlots state).card) ≤
      ended.gas.stateGasUsed

/-- A meter at the start of a message has a floor of zero. -/
theorem min_stateGasUsed_start (gas reservoir : Nat) :
    min (StateGasMeter.start gas reservoir).stateGasUsed
      (StateGasMeter.start gas reservoir).restore.stateGasUsed = 0 := by
  -- Both meters hold their whole reservoir, with no spill and nothing committed.
  simp [StateGasMeter.start, StateGasMeter.restore, StateGasMeter.stateGasUsed]

end EthLib.Execution.Evm

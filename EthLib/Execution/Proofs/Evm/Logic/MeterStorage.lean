module

public import EthLib.Execution.Proofs.Evm.Logic.MeterInstructions
public import EthLib.Execution.Proofs.Evm.Instructions.SelfDestruct

/-!
# Proofs: the instructions that pay state gas, under the state gas meter

A write of storage and SELFDESTRUCT pay state gas, and keep their reads when they halt.

Paying both kinds of gas from one counter is conservative for the state gas meter of EIP-8037.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

set_option hygiene false in
/-- Close a relation of two frames whose fields agree, from the relation that holds before. -/
local macro "keep" : tactic =>
  `(tactic| exact ⟨⟨meter, below, rfl⟩, keeps, hc, hf, hp, he⟩)

set_option hygiene false in
/-- Take the relation of two frames apart, so the second is the first with a state gas meter. -/
local macro "split_tracks" t:term : tactic =>
  `(tactic| obtain ⟨⟨meter, below, rfl⟩, keeps, hc, hf, hp, he⟩ := $t)

/-- SSTORE runs alike under the state gas meter. -/
theorem sstoreStep_bridge : Bridge (fork := fork) 1 sstoreStep sstoreStep := by
  intro start startMeter below
  change KeptLifts start startMeter (start.pc + 1) _ _
  unfold sstoreStep
  simp only [message_withStateGas]
  by_cases static : fork ≥ .glamsterdam ∧ start.message.isStatic = true
  · simp only [static, and_self, ↓reduceIte]
    exact KeptLifts.error
  simp only [static, ↓reduceIte]
  refine (Tracks.init below).popWord.bindKept ?_
  rintro ⟨w, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bindKept ?_
  rintro ⟨v, l⟩ ⟨_, _⟩ ⟨rfl, t⟩
  split_tracks t
  by_cases stipend : fork ≥ .istanbul ∧ l.gas ≤ CALL_STIPEND
  · simp only [GasMeter.gasLeft, stipend, and_self, ↓reduceIte]
    exact KeptLifts.error
  have high : ¬(fork ≥ .istanbul ∧ meter.gasLeft ≤ CALL_STIPEND) := fun h =>
    stipend ⟨h.1, Nat.le_trans below h.2⟩
  simp only [GasMeter.gasLeft, gas_withStateGas, stipend, high, ↓reduceIte]
  by_cases hb : fork ≥ .berlin <;> simp only [accessStorageKey, hb, ↓reduceIte] <;>
  · refine Tracks.keepReadsKept (by keep) ?_
    refine (Tracks.chargeGas (Tracks.refillStateGas (by keep) _) _).bindKept fun _ _ t => ?_
    refine (t.chargeStateGas _).bindKept fun _ _ t => ?_
    split_tracks t
    simp only [message_withStateGas]
    refine (Sim.ite (fun _ => Sim.error (R := Lands start startMeter (start.pc + 1)))
      fun _ => ?_).kept
    refine Sim.ofState.bind ?_
    rintro _ _ rfl
    exact Sim.pure (Tracks.advance (by keep) 1)

/-- SELFDESTRUCT runs alike under the state gas meter. -/
theorem selfdestructStep_bridge :
    Bridge (fork := fork) 1 (selfdestructStep fork) (selfdestructStep fork) := by
  intro start startMeter below
  change KeptLifts start startMeter (start.pc + 1) _ _
  unfold selfdestructStep
  simp only [message_withStateGas]
  by_cases static : fork ≥ .glamsterdam ∧ start.message.isStatic = true
  · simp only [static, and_self, ↓reduceIte]
    exact KeptLifts.error
  simp only [static, ↓reduceIte]
  refine (Tracks.init below).popWord.bindKept ?_
  rintro ⟨w, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  split_tracks t
  by_cases hb : fork ≥ .berlin <;> simp only [accessAddress, hb, ↓reduceIte] <;>
  · refine (Tracks.checkGas (by keep) _).bindKept fun _ _ _ => ?_
    refine Tracks.keepReadsKept (by keep) ?_
    refine (Tracks.chargeGas (by keep) _).bindKept fun _ _ t => ?_
    refine (t.chargeStateGas _).bindKept fun _ _ t => ?_
    split_tracks t
    unfold finishSelfdestruct
    simp only [message_withStateGas, state_withStateGas]
    refine (Sim.ite (fun _ => Sim.error (R := Lands start startMeter (start.pc + 1)))
      fun _ => ?_).kept
    refine Sim.ofState.bind ?_
    rintro _ _ rfl
    exact Sim.pure ⟨⟨meter, below, rfl⟩, keeps, hc, hf, fun h => by simp at h,
      fun h => he ▸ h, fun h => by simp at h⟩

end EthLib.Execution.Evm.Logic

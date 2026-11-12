module

public import EthLib.Base.Proofs.Fork
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import Mathlib.Logic.Relation

/-!
# Proofs: a chain of beacon states

A chain of beacon states runs one step at a time.

A step is a slot with the upgrades due at the slot it reaches, or a block at the slot of the state.

Slots that advance a state across forks are a run of slot steps.

A block that the state transition accepts is a run of slot steps, then one block step.

So an invariant that each step keeps, under hypotheses on that step, holds along every such block.

The hypotheses need hold only for the steps between its first and its last state.

A run of steps never moves the fork back, so a run between two states of one fork stays in it.

Inside one fork, a step is one slot or one block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- One step of a chain of beacon states.

It is a slot with the upgrades due at the slot it reaches.

Or it is a block that runs on the state of its fork, at the slot of the state.

A block step takes any execution engine.

It may skip the check of the proposer signature and of the state root.

So a chain may hold more states than the specification computes.

An invariant of every chain is then the stronger result. -/
inductive ChainStep (config : Config) (checks : SignatureChecks) :
    ForkedBeaconState preset → ForkedBeaconState preset → Prop
  /-- A slot, with the upgrades due at the slot it reaches. -/
  | slot {forked after : ForkedBeaconState preset} :
    advanceSlotAcross config checks forked = .ok after → ChainStep config checks forked after
  /-- A block at the slot of the state, on the state of its fork. -/
  | block {fork : Fork} {state after : BeaconState preset fork}
    (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
    (validateResult : Bool) :
    applySignedBlock config checks engine state signed validateResult = .ok after →
    ChainStep config checks ⟨fork, state⟩ ⟨fork, after⟩

/-- Slots that advance a state across forks are a run of slot steps of a chain. -/
theorem advanceSlotsAcross_chainSteps :
    ∀ {count : Nat} {forked advanced : ForkedBeaconState preset},
      advanceSlotsAcross config checks count forked = .ok advanced →
      Relation.ReflTransGen (ChainStep config checks) forked advanced
  | 0, forked, advanced, computed => by
    simp only [advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Relation.ReflTransGen.refl
  | count + 1, forked, advanced, computed => by
    simp only [advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact Relation.ReflTransGen.head (ChainStep.slot nextOk) (advanceSlotsAcross_chainSteps rest)

/-- A block that the state transition accepts is a run of steps of a chain. -/
theorem stateTransitionAcross_chainSteps {fork : Fork} {engine : ExecutionEngine preset fork}
    {forked : ForkedBeaconState preset} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {after : BeaconState preset fork}
    (computed :
      stateTransitionAcross config checks engine forked signed validateResult = .ok after) :
    Relation.ReflTransGen (ChainStep config checks) forked ⟨fork, after⟩ := by
  obtain ⟨advanced, slotsOk, applied⟩ := stateTransitionAcross_ok computed
  simp only [processSlotsAcross, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, slotsOk⟩ := slotsOk
  exact (advanceSlotsAcross_chainSteps slotsOk).tail
    (ChainStep.block engine signed validateResult applied)

/-- A run of steps of a chain, each of which meets a property, is a run of steps with it.

The property need hold only for the steps between the first and the last state.

That is every such step on any run, not only the steps of one run.

Each such step is reached from the first state, and reaches the last one. -/
theorem chainSteps_and {property : ForkedBeaconState preset → ForkedBeaconState preset → Prop}
    {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last)
    (meets : ∀ forked after, Relation.ReflTransGen (ChainStep config checks) first forked →
      ChainStep config checks forked after →
      Relation.ReflTransGen (ChainStep config checks) after last → property forked after) :
    Relation.ReflTransGen
      (fun forked after => ChainStep config checks forked after ∧ property forked after)
      first last := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head step rest more =>
    exact .head ⟨step, meets _ _ .refl step rest⟩
      (more fun forked after reach => meets forked after (.head step reach))

/-- One step of a chain never moves the fork back. -/
theorem ChainStep.fork_le {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) : forked.fork ≤ after.fork := by
  cases step with
  | slot computed =>
    obtain ⟨_, _, upgraded⟩ := bind_ok_iff.mp computed
    exact (processUpgrades_fork_le upgraded :)
  | block => exact Nat.le_refl _

/-- A run of steps of a chain never moves the fork back. -/
theorem fork_le_of_chainSteps {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    first.fork ≤ last.fork := by
  induction steps with
  | refl => exact Nat.le_refl _
  | tail _ step more => exact Nat.le_trans more step.fork_le

/-- The last step of a run inside one fork starts in that fork. -/
theorem fork_eq_of_chainSteps {fork : Fork} {first last : BeaconState preset fork}
    {forked : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, first⟩ forked)
    (step : ChainStep config checks forked ⟨fork, last⟩) :
    ∃ middle : BeaconState preset fork, forked = ⟨fork, middle⟩ := by
  obtain ⟨middleFork, middle⟩ := forked
  obtain rfl : middleFork = fork :=
    Fork.ctorIdx_injective (Nat.le_antisymm step.fork_le (fork_le_of_chainSteps steps))
  exact ⟨middle, rfl⟩

/-- One step of a chain inside one fork is a slot or a block of that fork. -/
theorem ChainStep.slot_or_block {fork : Fork} {state after : BeaconState preset fork}
    (step : ChainStep config checks ⟨fork, state⟩ ⟨fork, after⟩) :
    advanceSlot config checks state = .ok after ∨
      ∃ (engine : ExecutionEngine preset fork) (block : BeaconBlock preset fork),
        Consensus.processBlock config checks engine state block = .ok after := by
  generalize first : (⟨fork, state⟩ : ForkedBeaconState preset) = forked at step
  generalize second : (⟨fork, after⟩ : ForkedBeaconState preset) = upgraded at step
  cases step with
  | slot computed =>
    subst first
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    subst second
    have same := processUpgrades_eq_of_fork_le upgraded (Nat.le_refl _)
    cases same
    exact .inl advancedOk
  | block engine signed _ computed =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok computed
    cases first
    cases second
    exact .inr ⟨engine, signed.message, blockOk⟩

end EthLib.Consensus

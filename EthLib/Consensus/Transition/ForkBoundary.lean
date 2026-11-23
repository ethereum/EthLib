module

public import EthLib.Consensus.Transition.StateTransition
public import EthLib.Consensus.Transition.Upgrade

/-!
# `Consensus.Transition.ForkBoundary`

The state transition across the first slot of a fork epoch.

Each fork upgrades the state once the slots reach the first slot of its fork epoch.

The upgrade follows the epoch transition of the fork before it, at the end of the last slot.

When several forks share a fork epoch, the state upgrades through each of them in order.

A block then runs on the state of the fork at its slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset}

/-- A beacon state together with its fork. -/
structure ForkedBeaconState (preset : Preset) where
  /-- The fork of the state. -/
  fork : Fork
  /-- The state. -/
  state : BeaconState preset fork

/-- The state upgraded to the next consensus fork, which is always a later fork.

The upgrade to Gloas checks the signatures of the pending deposits of builders.

Heze, and a fork with no beacon state of its own, has no next fork, which is an error. -/
def upgradeNext (config : Config) (checks : SignatureChecks) :
    (pre : ForkedBeaconState preset) →
      Except TransitionError {post : ForkedBeaconState preset // pre.fork < post.fork}
  -- Altair computes its participation flags and its first sync committees.
  | ⟨.phase0, pre⟩ => do
    return ⟨⟨.altair, ← upgradeToAltair config pre⟩, (by decide : Fork.phase0 < .altair)⟩
  -- Bellatrix, Capella and Deneb carry the fields over, with their new fields at initial values.
  | ⟨.altair, pre⟩ =>
    return ⟨⟨.bellatrix, carryFields config .bellatrix pre (by decide) (by decide)⟩,
      (by decide : Fork.altair < .bellatrix)⟩
  | ⟨.bellatrix, pre⟩ =>
    return ⟨⟨.shapella, carryFields config .shapella pre (by decide) (by decide)⟩,
      (by decide : Fork.bellatrix < .shapella)⟩
  | ⟨.shapella, pre⟩ =>
    return ⟨⟨.dencun, carryFields config .dencun pre (by decide) (by decide)⟩,
      (by decide : Fork.shapella < .dencun)⟩
  -- Electra, Fulu, Gloas and Heze each have an upgrade of their own.
  | ⟨.dencun, pre⟩ => do
    return ⟨⟨.pectra, ← upgradeToElectra config pre⟩, (by decide : Fork.dencun < .pectra)⟩
  | ⟨.pectra, pre⟩ => do
    return ⟨⟨.fusaka, ← upgradeToFulu config pre⟩, (by decide : Fork.pectra < .fusaka)⟩
  | ⟨.fusaka, pre⟩ => do
    return ⟨⟨.glamsterdam, ← upgradeToGloas config checks pre⟩,
      (by decide : Fork.fusaka < .glamsterdam)⟩
  | ⟨.glamsterdam, pre⟩ => do
    return ⟨⟨.hegota, ← upgradeToHeze config pre⟩, (by decide : Fork.glamsterdam < .hegota)⟩
  -- Any other fork has no next consensus fork.
  | ⟨fork, _⟩ => throw (.accessor (.forkNotYetSpecified fork))

/-- Whether the next consensus fork starts at the slot of a state. -/
def upgradeDue (config : Config) (forked : ForkedBeaconState preset) : Bool :=
  -- The slot `s` is the first of its epoch, `s mod SLOTS_PER_EPOCH = 0`.
  --
  -- That epoch is the fork epoch of the next fork; after Heze no fork is scheduled.
  forked.state.slot % preset.SLOTS_PER_EPOCH == 0 &&
    (config.nextFork forked.fork).any fun (_, epoch) =>
      computeEpochAtSlot preset forked.state.slot == epoch

/-- The state after every upgrade that is due at its slot, one fork after another. -/
def processUpgrades (config : Config) (checks : SignatureChecks)
    (forked : ForkedBeaconState preset) : Except TransitionError (ForkedBeaconState preset) :=
  -- The next fork is due at this slot: the state upgrades to it.
  if upgradeDue config forked then do
    let next ← upgradeNext config checks forked
    -- A fork that shares its fork epoch with the next one is due at the same slot, so recur.
    processUpgrades config checks next.val
  else pure forked
termination_by Fork.last.ctorIdx + 1 - forked.fork.ctorIdx
decreasing_by
  -- Each upgrade moves to a later fork, and no fork comes after the last one.
  have later : forked.fork.ctorIdx < next.val.fork.ctorIdx := next.property
  have bounded : next.val.fork.ctorIdx ≤ Fork.last.ctorIdx := by cases next.val.fork <;> decide
  omega

/-- The state after one slot, then after the upgrades due at the slot it reaches. -/
def advanceSlotAcross (config : Config) (checks : SignatureChecks)
    (forked : ForkedBeaconState preset) : Except TransitionError (ForkedBeaconState preset) := do
  -- The slot runs under the rules of the fork of the state, epoch transition included.
  let state ← advanceSlot config checks forked.state
  -- The upgrades then apply at the slot reached, before any block of that slot.
  processUpgrades config checks ⟨forked.fork, state⟩

/-- The state some count of slots later, one slot at a time, with the upgrades on the way. -/
def advanceSlotsAcross (config : Config) (checks : SignatureChecks) :
    Nat → ForkedBeaconState preset → Except TransitionError (ForkedBeaconState preset)
  -- The loop over the slots runs as a recursion on the count of slots left.
  | 0, forked => pure forked
  | count + 1, forked => do
    advanceSlotsAcross config checks count (← advanceSlotAcross config checks forked)

/-- The state at a later slot, with the upgrades on the way. -/
def processSlotsAcross (config : Config) (checks : SignatureChecks)
    (forked : ForkedBeaconState preset) (slot : Slot) :
    Except TransitionError (ForkedBeaconState preset) := do
  -- The target slot is after the slot `s` of the state.
  ensure (forked.state.slot < slot) (.slotNotAfter slot forked.state.slot)
  -- One slot at a time while `s` is below the target slot, each followed by its upgrades.
  advanceSlotsAcross config checks (slot.toNat - forked.state.slot.toNat) forked

/-- The state after a signed block, from a state that may be of an earlier fork. -/
def stateTransitionAcross {fork : Fork} (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (forked : ForkedBeaconState preset)
    (signed : SignedBeaconBlock preset fork) (validateResult : Bool := true) :
    Except TransitionError (BeaconState preset fork) := do
  -- The state advances to the slot of the block, with the upgrades on the way.
  let advanced ← processSlotsAcross config checks forked signed.message.slot
  -- The block is of the fork that the state then has, and it applies to that state.
  if same : advanced.fork = fork then
    applySignedBlock config checks engine (same ▸ advanced.state) signed validateResult
  else throw (.blockForkMismatch fork advanced.fork)

end EthLib.Consensus

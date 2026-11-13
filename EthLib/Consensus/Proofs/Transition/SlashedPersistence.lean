module

public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# Persistence of slashing at a validator's registry index

A successful transition cannot clear a slashed flag or remove its registry entry.

Each result follows from the frame of its step, through `of_frame` and `of_upgradeFrame`.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}

/-- Each slashed validator remains slashed at the same registry index. -/
def SlashedPersistence {f h : Fork} (s : BeaconState preset f)
    (t : BeaconState preset h) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v → v.slashed = true →
    ∃ w, t.validators.data[i]? = some w ∧ w.slashed = true

namespace SlashedPersistence

theorem refl (s : BeaconState preset fork) : SlashedPersistence s s :=
  fun _ v found flag => ⟨v, found, flag⟩

theorem trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : SlashedPersistence s t) (two : SlashedPersistence t u) :
    SlashedPersistence s u := by
  intro i v found flag
  obtain ⟨w, read, slashed⟩ := one i v found flag
  exact two i w read slashed

theorem of_data {f h : Fork} {s : BeaconState preset f} {t : BeaconState preset h}
    (same : t.validators.data = s.validators.data := by rfl) : SlashedPersistence s t := by
  intro i v found flag
  exact ⟨v, same.symm ▸ found, flag⟩

/-- A frame never clears a slashed flag or removes a registry entry. -/
theorem of_frame (frame : Frame s t) : SlashedPersistence s t := by
  intro i v found flag
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have grown : i < t.validators.data.size := Nat.lt_of_lt_of_le inside frame.registryGrows
  have read := Array.getElem?_eq_getElem grown
  exact ⟨_, read, frame.slashed i v _ found read flag⟩

/-- An upgrade frame keeps each slashed flag at its position, so it never clears one. -/
theorem of_upgradeFrame {f h : Fork} {s : BeaconState preset f} {t : BeaconState preset h}
    (frame : UpgradeFrame config s t) : SlashedPersistence s t := by
  intro i v found flag
  have same := frame.slashed i
  rw [found] at same
  obtain ⟨w, read, marked⟩ := Option.map_eq_some_iff.mp same
  exact ⟨w, read, marked.trans flag⟩

end SlashedPersistence

theorem Step.slashedPersistence {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : SlashedPersistence x.state y.state := by
  cases step with
  | block engine signed due ok =>
    exact .of_frame (frame_processBlock (applySignedBlock_ok ok).2.1)
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, afterEq⟩ := advanceSlot_ok slotOk
    have epoch : SlashedPersistence cached epoched := by
      unfold epochIfLast at epochedOk
      split at epochedOk
      · obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
        exact (SlashedPersistence.of_data (congrArg (·.data)
          (processJustificationAndFinalization_keeps justifiedOk).2.2.2.2.2.1)).trans
          (.of_frame frame.toFrame)
      · cases epochedOk; exact .refl _
    have advancedKept : SlashedPersistence x.state advanced :=
      (SlashedPersistence.of_frame (frame_processSlot cachedOk)).trans
        (epoch.trans (.of_data (by rw [afterEq])))
    exact advancedKept.trans <|
      processUpgrades_induction (property := fun z => SlashedPersistence advanced z.state)
        (fun held ok => held.trans (.of_upgradeFrame (upgradeFrame_upgradeNext ok)))
        (.refl _) upgrades

theorem Run.slashedPersistence {x y : ForkedBeaconState preset}
    (run : Run config checks x y) : SlashedPersistence x.state y.state := by
  induction run with
  | nil => exact SlashedPersistence.refl _
  | snoc pre step ih => exact ih.trans step.slashedPersistence

end EthLib.Consensus

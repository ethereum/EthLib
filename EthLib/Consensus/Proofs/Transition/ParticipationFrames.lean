module

public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Containers.State

/-!
# Proofs: steps that keep the participation flags

From Altair the state keeps one byte of flags for each validator, in each of two epochs.

Most steps of a block keep both lists of flags whole.

A deposit can add a validator, so it keeps only the bytes below the earlier size of the registry.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork} {first second third : BeaconState preset fork}

/-- A step that keeps the participation flags of both recent epochs. -/
def ParticipationKept (state after : BeaconState preset fork) : Prop :=
  after.previousEpochParticipation = state.previousEpochParticipation ∧
    after.currentEpochParticipation = state.currentEpochParticipation

theorem ParticipationKept.refl (state : BeaconState preset fork) : ParticipationKept state state :=
  ⟨rfl, rfl⟩

theorem ParticipationKept.trans (one : ParticipationKept first second)
    (two : ParticipationKept second third) : ParticipationKept first third :=
  ⟨two.1.trans one.1, two.2.trans one.2⟩

/-- A fold whose every step keeps the participation flags keeps them. -/
theorem ParticipationKept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → ParticipationKept a b) {items : List α}
    (computed : items.foldlM step first = .ok second) : ParticipationKept first second :=
  (foldlM_ok_steps ParticipationKept ParticipationKept.refl ParticipationKept.trans each
    computed).1

/-- A step that keeps the flags at each position below the earlier size of the registry. -/
def ParticipationKeptBelow (state after : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (position : Nat), position < state.validators.data.size →
    (after.previousEpochParticipation altair).data[position]? =
        (state.previousEpochParticipation altair).data[position]? ∧
      (after.currentEpochParticipation altair).data[position]? =
        (state.currentEpochParticipation altair).data[position]?

theorem ParticipationKeptBelow.refl (state : BeaconState preset fork) :
    ParticipationKeptBelow state state :=
  fun _ _ _ => ⟨rfl, rfl⟩

/-- Two steps keep the flags below the first size of the registry, when it does not shrink. -/
theorem ParticipationKeptBelow.trans (one : ParticipationKeptBelow first second)
    (two : ParticipationKeptBelow second third)
    (grows : first.validators.data.size ≤ second.validators.data.size) :
    ParticipationKeptBelow first third := fun altair position inside =>
  have later := two altair position (Nat.lt_of_lt_of_le inside grows)
  ⟨later.1.trans (one altair position inside).1, later.2.trans (one altair position inside).2⟩

/-- A step that keeps both lists of flags keeps them below any size. -/
theorem ParticipationKept.below (kept : ParticipationKept first second) :
    ParticipationKeptBelow first second :=
  fun _ _ _ => ⟨by rw [kept.1], by rw [kept.2]⟩

end EthLib.Consensus

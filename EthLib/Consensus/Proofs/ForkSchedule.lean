module

public import EthLib.Base.Proofs.Fork
public import EthLib.Consensus.ForkSchedule

/-!
# Proofs: the fork at an epoch

The fork at an epoch is the latest consensus fork that has started by then.

So it never moves back as the epoch grows, whatever the order of the configured epochs.

The blob limit at an epoch is that of the latest schedule entry that has started by then.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

namespace Config

/-- The first epoch of each consensus fork in a configuration, and nothing for other forks. -/
def activationEpoch (config : Config) : Fork → Option Epoch
  | .phase0 => some 0
  | .altair => some config.ALTAIR_FORK_EPOCH
  | .bellatrix => some config.BELLATRIX_FORK_EPOCH
  | .shapella => some config.CAPELLA_FORK_EPOCH
  | .dencun => some config.DENEB_FORK_EPOCH
  | .pectra => some config.ELECTRA_FORK_EPOCH
  | .fusaka => some config.FULU_FORK_EPOCH
  | _ => none

variable {config : Config}

/-- The fork at an epoch is a consensus fork that has started by that epoch. -/
theorem activationEpoch_forkAtEpoch (epoch : Epoch) :
    ∃ first, config.activationEpoch (config.forkAtEpoch epoch) = some first ∧ first ≤ epoch := by
  unfold forkAtEpoch
  repeat' split
  all_goals simp_all [activationEpoch, UInt64.le_iff_toNat_le]

/-- Every consensus fork that has started by an epoch is at or before the fork at that epoch. -/
theorem le_forkAtEpoch {fork : Fork} {first epoch : Epoch}
    (scheduled : config.activationEpoch fork = some first) (started : first ≤ epoch) :
    fork ≤ config.forkAtEpoch epoch := by
  cases fork <;> simp only [activationEpoch, reduceCtorEq, Option.some.injEq] at scheduled <;>
    subst scheduled <;> unfold forkAtEpoch
  all_goals
    repeat' split
  all_goals first | decide | simp_all [UInt64.le_iff_toNat_le]

/-- The fork at an epoch never moves back as the epoch grows. -/
theorem forkAtEpoch_mono {earlier later : Epoch} (le : earlier ≤ later) :
    config.forkAtEpoch earlier ≤ config.forkAtEpoch later := by
  obtain ⟨first, scheduled, started⟩ := activationEpoch_forkAtEpoch (config := config) earlier
  exact le_forkAtEpoch scheduled (UInt64.le_trans started le)

/-- The fork at an epoch is never BPO1 or BPO2, which change only the blob schedule. -/
theorem forkAtEpoch_ne_bpo (epoch : Epoch) :
    config.forkAtEpoch epoch ≠ .bpo1 ∧ config.forkAtEpoch epoch ≠ .bpo2 := by
  obtain ⟨first, scheduled, -⟩ := activationEpoch_forkAtEpoch (config := config) epoch
  constructor <;> intro bpo <;> simp [bpo, activationEpoch] at scheduled

/-- The blob limit at an epoch.

When an entry has started by the epoch, the limit is that of a latest such entry.

Otherwise the limit of Electra holds. -/
theorem getBlobParameters_spec (epoch : Epoch) :
    (∃ entry ∈ config.BLOB_SCHEDULE, entry.EPOCH ≤ epoch ∧
        config.getBlobParameters epoch = ⟨entry.EPOCH, entry.MAX_BLOBS_PER_BLOCK⟩ ∧
        ∀ other ∈ config.BLOB_SCHEDULE, other.EPOCH ≤ epoch → other.EPOCH ≤ entry.EPOCH) ∨
      ((∀ other ∈ config.BLOB_SCHEDULE, epoch < other.EPOCH) ∧
        config.getBlobParameters epoch =
          ⟨config.ELECTRA_FORK_EPOCH, config.MAX_BLOBS_PER_BLOCK_ELECTRA⟩) := by
  let order := fun a b : BlobScheduleEntry => decide (b.EPOCH ≤ a.EPOCH)
  have sorted : (config.BLOB_SCHEDULE.mergeSort order).Pairwise (fun a b => order a b) :=
    List.pairwise_mergeSort
      (fun a b c ab bc => by simp_all [order, UInt64.le_iff_toNat_le]; omega)
      (fun a b => by simp [order, UInt64.le_iff_toNat_le]; omega) _
  unfold getBlobParameters
  split
  · rename_i entry found
    obtain ⟨started, before, after, split, missed⟩ := List.find?_eq_some_iff_append.mp found
    have member : entry ∈ config.BLOB_SCHEDULE := by
      have : entry ∈ config.BLOB_SCHEDULE.mergeSort order := by
        rw [split]
        simp
      exact List.mem_mergeSort.mp this
    refine .inl ⟨entry, member, by simpa using started, rfl, fun other mem otherStarted => ?_⟩
    have inSorted : other ∈ config.BLOB_SCHEDULE.mergeSort order := List.mem_mergeSort.mpr mem
    rw [split] at inSorted sorted
    rcases List.mem_append.mp inSorted with early | late
    · have := missed other early
      simp_all
    · rcases List.mem_cons.mp late with same | rest
      · exact same ▸ UInt64.le_refl _
      · have := (List.pairwise_append.mp sorted).2.1
        simpa [order] using (List.pairwise_cons.mp this).1 other rest
  · rename_i none
    refine .inr ⟨fun other mem => ?_, rfl⟩
    have := List.find?_eq_none.mp none other (List.mem_mergeSort.mpr mem)
    simpa using this

end Config

end EthLib.Consensus

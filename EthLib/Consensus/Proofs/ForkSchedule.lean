module

public import EthLib.Base.Proofs.Fork
public import EthLib.Consensus.ForkSchedule
public import Mathlib.Data.List.Nodup

/-!
# Proofs: the fork at an epoch

The fork at an epoch is the latest consensus fork that has started by then.

So it never moves back as the epoch grows, whatever the order of the configured epochs.

Heze changes neither the fork nor the version of anything before it.

The blob limit at an epoch is that of the latest schedule entry that has started by then.

So is the gas limit that the schedule of Gloas recommends.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

/-- The latest started entry of a schedule.

When an entry has started by the epoch, the result is a latest such entry.

Otherwise there is none. -/
theorem latestStarted_spec {α : Type} (first : α → Epoch) (entries : List α) (epoch : Epoch) :
    (∃ entry, latestStarted first entries epoch = some entry ∧ entry ∈ entries ∧
        first entry ≤ epoch ∧ ∀ other ∈ entries, first other ≤ epoch → first other ≤ first entry) ∨
      (latestStarted first entries epoch = none ∧ ∀ other ∈ entries, epoch < first other) := by
  let order := fun a b : α => decide (first b ≤ first a)
  have sorted : (entries.mergeSort order).Pairwise (fun a b => order a b) :=
    List.pairwise_mergeSort
      (fun a b c ab bc => by simp_all [order, UInt64.le_iff_toNat_le]; omega)
      (fun a b => by simp [order, UInt64.le_iff_toNat_le]; omega) _
  unfold latestStarted
  cases found : (entries.mergeSort order).find? (fun x => decide (first x ≤ epoch)) with
  | some entry =>
    obtain ⟨started, before, after, split, missed⟩ := List.find?_eq_some_iff_append.mp found
    have member : entry ∈ entries := by
      have : entry ∈ entries.mergeSort order := by
        rw [split]
        simp
      exact List.mem_mergeSort.mp this
    refine .inl ⟨entry, rfl, member, by simpa using started, fun other mem otherStarted => ?_⟩
    have inSorted : other ∈ entries.mergeSort order := List.mem_mergeSort.mpr mem
    rw [split] at inSorted sorted
    rcases List.mem_append.mp inSorted with early | late
    · have := missed other early
      simp_all
    · rcases List.mem_cons.mp late with same | rest
      · exact same ▸ UInt64.le_refl _
      · have := (List.pairwise_append.mp sorted).2.1
        simpa [order] using (List.pairwise_cons.mp this).1 other rest
  | none =>
    refine .inr ⟨rfl, fun other mem => ?_⟩
    have := List.find?_eq_none.mp found other (List.mem_mergeSort.mpr mem)
    simpa using this

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
  | .glamsterdam => some config.GLOAS_FORK_EPOCH
  | .hegota => some config.HEZE_FORK_EPOCH
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
  all_goals decide

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
  unfold getBlobParameters
  rcases latestStarted_spec (·.EPOCH) config.BLOB_SCHEDULE epoch with
    ⟨entry, found, member, started, latest⟩ | ⟨found, early⟩ <;> rw [found]
  · exact .inl ⟨entry, member, started, rfl, latest⟩
  · exact .inr ⟨early, rfl⟩

/-- The fork at an epoch is Gloas exactly from the first epoch of Gloas. -/
theorem forkAtEpoch_eq_glamsterdam_iff (epoch : Epoch) :
    config.forkAtEpoch epoch = .glamsterdam ↔
      config.GLOAS_FORK_EPOCH ≤ epoch ∧ epoch < config.HEZE_FORK_EPOCH := by
  unfold forkAtEpoch
  repeat' split
  all_goals simp_all [UInt64.not_le]

/-- The fork at an epoch is Heze exactly from the first epoch of Heze. -/
theorem forkAtEpoch_eq_hegota_iff (epoch : Epoch) :
    config.forkAtEpoch epoch = .hegota ↔ config.HEZE_FORK_EPOCH ≤ epoch := by
  unfold forkAtEpoch
  repeat' split
  all_goals simp_all

/-- Before the first epoch of Heze, the fork is the one of a configuration where Heze never starts.

So adding Heze changes no fork before it. -/
theorem forkAtEpoch_of_lt_heze {epoch : Epoch} (before : epoch < config.HEZE_FORK_EPOCH) :
    config.forkAtEpoch epoch =
      { config with HEZE_FORK_EPOCH := FAR_FUTURE_EPOCH }.forkAtEpoch epoch := by
  -- No epoch is below the first epoch of Heze and at the largest epoch.
  have never : ¬FAR_FUTURE_EPOCH ≤ epoch := by
    intro far
    have := config.HEZE_FORK_EPOCH.toNat_lt
    rw [UInt64.le_iff_toNat_le] at far
    rw [UInt64.lt_iff_toNat_lt] at before
    have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  simp only [forkAtEpoch, UInt64.not_le.mpr before, never, ite_false]

/-- The version of Heze is the one the configuration names. -/
theorem forkVersion_hegota : config.forkVersion .hegota = config.HEZE_FORK_VERSION := rfl

/-- A fork before Heze does not read the version of Heze. -/
theorem forkVersion_of_lt_hegota {fork : Fork} (before : fork < .hegota) (version : Version) :
    config.forkVersion fork = { config with HEZE_FORK_VERSION := version }.forkVersion fork := by
  have : ¬Fork.hegota ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  simp only [forkVersion, this, ite_false]

/-- The gas limit that the schedule recommends at an epoch.

When an entry has started by the epoch, it is the limit of a latest such entry.

Otherwise the schedule recommends nothing. -/
theorem getScheduledGasLimit_spec (epoch : Epoch) :
    (∃ entry ∈ config.GAS_LIMIT_SCHEDULE,
        entry.EPOCH ≤ epoch ∧ config.getScheduledGasLimit epoch = some entry.GAS_LIMIT ∧
        ∀ other ∈ config.GAS_LIMIT_SCHEDULE, other.EPOCH ≤ epoch → other.EPOCH ≤ entry.EPOCH) ∨
      ((∀ other ∈ config.GAS_LIMIT_SCHEDULE, epoch < other.EPOCH) ∧
        config.getScheduledGasLimit epoch = none) := by
  unfold getScheduledGasLimit
  rcases latestStarted_spec (·.EPOCH) config.GAS_LIMIT_SCHEDULE epoch with
    ⟨entry, found, member, started, latest⟩ | ⟨found, early⟩
  · exact .inl ⟨entry, member, started, by simp [found], latest⟩
  · exact .inr ⟨early, by simp [found]⟩

/-- An empty schedule recommends nothing. -/
theorem getScheduledGasLimit_nil (empty : config.GAS_LIMIT_SCHEDULE = []) (epoch : Epoch) :
    config.getScheduledGasLimit epoch = none := by
  rcases getScheduledGasLimit_spec (config := config) epoch with
    ⟨entry, member, -⟩ | ⟨-, found⟩
  · simp [empty] at member
  · exact found

/-- When every entry starts at or after Gloas, the schedule recommends nothing before Gloas.

So the check of the first epoch of Gloas that EIP-8261 adds changes nothing. -/
theorem getScheduledGasLimit_before_gloas
    (after : ∀ entry ∈ config.GAS_LIMIT_SCHEDULE, config.GLOAS_FORK_EPOCH ≤ entry.EPOCH)
    {epoch : Epoch} (before : epoch < config.GLOAS_FORK_EPOCH) :
    config.getScheduledGasLimit epoch = none := by
  rcases getScheduledGasLimit_spec (config := config) epoch with
    ⟨entry, member, started, -⟩ | ⟨-, found⟩
  · have := after entry member
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at before started this
    omega
  · exact found

/-- When the entries have distinct epochs, their order does not change the recommendation. -/
theorem getScheduledGasLimit_perm {other : Config}
    (perm : config.GAS_LIMIT_SCHEDULE.Perm other.GAS_LIMIT_SCHEDULE)
    (distinct : (config.GAS_LIMIT_SCHEDULE.map (·.EPOCH)).Nodup) (epoch : Epoch) :
    config.getScheduledGasLimit epoch = other.getScheduledGasLimit epoch := by
  rcases getScheduledGasLimit_spec (config := config) epoch with
    ⟨entry, member, entryStarted, found, latest⟩ | ⟨early, found⟩ <;>
  rcases getScheduledGasLimit_spec (config := other) epoch with
    ⟨entry', member', entryStarted', found', latest'⟩ | ⟨early', found'⟩
  · rw [found, found']
    have mem' : entry' ∈ config.GAS_LIMIT_SCHEDULE := perm.mem_iff.mpr member'
    have mem : entry ∈ other.GAS_LIMIT_SCHEDULE := perm.mem_iff.mp member
    have same : entry = entry' :=
      List.inj_on_of_nodup_map distinct member mem'
        (UInt64.le_antisymm (latest' entry mem entryStarted) (latest entry' mem' entryStarted'))
    rw [same]
  · exact absurd entryStarted (UInt64.not_le.mpr (early' entry (perm.mem_iff.mp member)))
  · exact absurd entryStarted' (UInt64.not_le.mpr (early entry' (perm.mem_iff.mpr member')))
  · rw [found, found']

end Config

end EthLib.Consensus

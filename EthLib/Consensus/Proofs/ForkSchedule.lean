module

public import EthLib.Base.Proofs.Fork
public import EthLib.Consensus.ForkSchedule
public import Mathlib.Data.List.Nodup

/-!
# Proofs: the fork at an epoch

The fork at an epoch is the latest consensus fork that has started by then.

So it never moves back as the epoch grows, whatever the order of the configured epochs.

The forks of the mainnet and minimal configurations start in the order of the timeline.

The checks of the two schedules accept exactly the schedules that meet the rules of their forks.
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

/-- When the entries have distinct first epochs, their order does not change the latest started. -/
theorem latestStarted_perm {α : Type} {first : α → Epoch} {entries others : List α}
    (perm : entries.Perm others) (distinct : (entries.map first).Nodup) (epoch : Epoch) :
    latestStarted first entries epoch = latestStarted first others epoch := by
  rcases latestStarted_spec first entries epoch with
    ⟨entry, found, member, entryStarted, latest⟩ | ⟨found, early⟩ <;>
  rcases latestStarted_spec first others epoch with
    ⟨entry', found', member', entryStarted', latest'⟩ | ⟨found', early'⟩
  · rw [found, found']
    have mem' : entry' ∈ entries := perm.mem_iff.mpr member'
    have mem : entry ∈ others := perm.mem_iff.mp member
    -- Both are latest among the same entries, so they share a first epoch, hence are equal.
    have same : entry = entry' :=
      List.inj_on_of_nodup_map distinct member mem'
        (UInt64.le_antisymm (latest' entry mem entryStarted) (latest entry' mem' entryStarted'))
    rw [same]
  · exact absurd entryStarted (UInt64.not_le.mpr (early' entry (perm.mem_iff.mp member)))
  · exact absurd entryStarted' (UInt64.not_le.mpr (early entry' (perm.mem_iff.mpr member')))
  · rw [found, found']

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

/-! ## Configurations whose forks start in order -/

/-- The consensus forks of a configuration start in the order of the timeline.

Forks may share a first epoch. -/
def ForkEpochsOrdered (config : Config) : Prop :=
  config.ALTAIR_FORK_EPOCH ≤ config.BELLATRIX_FORK_EPOCH ∧
    config.BELLATRIX_FORK_EPOCH ≤ config.CAPELLA_FORK_EPOCH ∧
    config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH ∧
    config.DENEB_FORK_EPOCH ≤ config.ELECTRA_FORK_EPOCH ∧
    config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH ∧
    config.FULU_FORK_EPOCH ≤ config.GLOAS_FORK_EPOCH ∧
    config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH

instance (config : Config) : Decidable config.ForkEpochsOrdered := by
  unfold ForkEpochsOrdered
  infer_instance

/-- The forks of the mainnet configuration start in order. -/
theorem forkEpochsOrdered_mainnet : mainnet.ForkEpochsOrdered := by decide

/-- The forks of the minimal configuration start in order. -/
theorem forkEpochsOrdered_minimal : minimal.ForkEpochsOrdered := by decide

/-- When the forks start in order, a later consensus fork never starts earlier. -/
theorem activationEpoch_le_of_le (ordered : config.ForkEpochsOrdered) {earlier later : Fork}
    {start finish : Epoch} (first : config.activationEpoch earlier = some start)
    (second : config.activationEpoch later = some finish) (le : earlier ≤ later) :
    start ≤ finish := by
  obtain ⟨ab, bc, cd, de, ef, fg, gh⟩ := ordered
  simp only [UInt64.le_iff_toNat_le] at ab bc cd de ef fg gh ⊢
  cases earlier <;> simp only [activationEpoch, reduceCtorEq, Option.some.injEq] at first <;>
    subst first <;>
    cases later <;> simp only [activationEpoch, reduceCtorEq, Option.some.injEq] at second <;>
    subst second <;>
    first
      | exact absurd le (by decide)
      | (simp only [UInt64.toNat_zero]; omega)
      | omega

/-- The next consensus fork is later, and starts at the epoch it comes with. -/
theorem nextFork_activationEpoch {fork next : Fork} {first : Epoch}
    (scheduled : config.nextFork fork = some (next, first)) :
    fork < next ∧ config.activationEpoch next = some first := by
  cases fork <;>
    simp only [nextFork, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at scheduled <;>
    obtain ⟨rfl, rfl⟩ := scheduled <;> exact ⟨by decide, rfl⟩

/-- A consensus fork before another one has a next consensus fork, at or before the other. -/
theorem exists_nextFork_le {fork later : Fork} {start finish : Epoch}
    (current : config.activationEpoch fork = some start)
    (target : config.activationEpoch later = some finish) (lt : fork < later) :
    ∃ next first, config.nextFork fork = some (next, first) ∧ next ≤ later := by
  cases fork <;> simp only [activationEpoch, reduceCtorEq] at current <;>
    cases later <;> simp only [activationEpoch, reduceCtorEq] at target <;>
    first
      | exact absurd lt (by decide)
      | exact ⟨_, _, rfl, by decide⟩

/-- The fork at an epoch is never one of BPO1 to BPO5, which change only the blob schedule. -/
theorem forkAtEpoch_ne_bpo (epoch : Epoch) :
    config.forkAtEpoch epoch ∉ [Fork.bpo1, .bpo2, .bpo3, .bpo4, .bpo5] := by
  obtain ⟨first, scheduled, -⟩ := activationEpoch_forkAtEpoch (config := config) epoch
  intro bpo
  simp only [List.mem_cons, List.not_mem_nil, or_false] at bpo
  rcases bpo with bpo | bpo | bpo | bpo | bpo <;> simp [bpo, activationEpoch] at scheduled

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

/-- The largest blob limit is one of the limits, and at least each of them. -/
theorem largestBlobLimit_spec :
    (config.largestBlobLimit = config.MAX_BLOBS_PER_BLOCK_ELECTRA ∨
        ∃ entry ∈ config.BLOB_SCHEDULE, config.largestBlobLimit = entry.MAX_BLOBS_PER_BLOCK) ∧
      config.MAX_BLOBS_PER_BLOCK_ELECTRA ≤ config.largestBlobLimit ∧
      ∀ entry ∈ config.BLOB_SCHEDULE, entry.MAX_BLOBS_PER_BLOCK ≤ config.largestBlobLimit := by
  unfold largestBlobLimit
  generalize config.MAX_BLOBS_PER_BLOCK_ELECTRA = start
  generalize config.BLOB_SCHEDULE = entries
  induction entries generalizing start with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨found, above, bounded⟩ := ih (max start head.MAX_BLOBS_PER_BLOCK)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
    -- One step keeps the larger of the two limits.
    have step : max start head.MAX_BLOBS_PER_BLOCK = start ∨
        max start head.MAX_BLOBS_PER_BLOCK = head.MAX_BLOBS_PER_BLOCK := by
      rw [UInt64.max_def]
      split <;> simp
    refine ⟨?_, UInt64.le_trans Std.left_le_max above, UInt64.le_trans Std.right_le_max above,
      bounded⟩
    rcases found with same | ⟨entry, member, same⟩
    · rcases step with kept | taken
      · exact .inl (same.trans kept)
      · exact .inr (.inl (same.trans taken))
    · exact .inr (.inr ⟨entry, member, same⟩)

/-- The blob limit at each epoch is at most the largest blob limit. -/
theorem getBlobParameters_le_largestBlobLimit (epoch : Epoch) :
    (config.getBlobParameters epoch).maxBlobsPerBlock ≤ config.largestBlobLimit := by
  obtain ⟨-, electra, entries⟩ := largestBlobLimit_spec (config := config)
  rcases getBlobParameters_spec epoch with ⟨entry, member, -, found, -⟩ | ⟨-, found⟩ <;>
    rw [found]
  · exact entries entry member
  · exact electra

/-- The rules that a valid blob schedule meets, and no others.

No two entries share a first epoch.

Each entry starts at or after the first epoch of Fulu.

Its limit is at most the largest number of blob commitments in a block. -/
theorem blobScheduleValid_iff (preset : Preset) :
    config.blobScheduleValid preset = true ↔
      (config.BLOB_SCHEDULE.map (·.EPOCH)).Nodup ∧
        ∀ entry ∈ config.BLOB_SCHEDULE, config.FULU_FORK_EPOCH ≤ entry.EPOCH ∧
          entry.MAX_BLOBS_PER_BLOCK ≤ preset.MAX_BLOB_COMMITMENTS_PER_BLOCK := by
  simp [blobScheduleValid, List.all_eq_true]

/-- With the same Electra epoch and limit, reordering distinct epochs keeps the blob parameters. -/
theorem getBlobParameters_perm {other : Config}
    (perm : config.BLOB_SCHEDULE.Perm other.BLOB_SCHEDULE)
    (electra : other.ELECTRA_FORK_EPOCH = config.ELECTRA_FORK_EPOCH)
    (limit : other.MAX_BLOBS_PER_BLOCK_ELECTRA = config.MAX_BLOBS_PER_BLOCK_ELECTRA)
    (distinct : (config.BLOB_SCHEDULE.map (·.EPOCH)).Nodup) (epoch : Epoch) :
    config.getBlobParameters epoch = other.getBlobParameters epoch := by
  unfold getBlobParameters
  rw [latestStarted_perm perm distinct, electra, limit]

/-- With a valid blob schedule, the limit of a started entry is at most the commitment bound.

That bound is the largest number of blob commitments in a block.

So a block within the limit of the schedule also fits its list of commitments. -/
theorem getBlobParameters_le_of_blobScheduleValid {preset : Preset}
    (valid : config.blobScheduleValid preset = true) {epoch : Epoch}
    (started : ∃ entry ∈ config.BLOB_SCHEDULE, entry.EPOCH ≤ epoch) :
    (config.getBlobParameters epoch).maxBlobsPerBlock ≤ preset.MAX_BLOB_COMMITMENTS_PER_BLOCK := by
  obtain ⟨-, bounded⟩ := (blobScheduleValid_iff preset).mp valid
  rcases getBlobParameters_spec (config := config) epoch with
    ⟨entry, member, -, found, -⟩ | ⟨early, -⟩
  · rw [found]
    exact (bounded entry member).2
  · obtain ⟨entry, member, before⟩ := started
    exact absurd before (UInt64.not_le.mpr (early entry member))

/-- Two entries with one first epoch make the blob limit depend on their order.

So the rule that the epochs are distinct is needed for the order to be free. -/
theorem getBlobParameters_sharedEpoch :
    { config with BLOB_SCHEDULE := [⟨5, 1⟩, ⟨5, 2⟩] }.getBlobParameters 5 = ⟨5, 1⟩ ∧
      { config with BLOB_SCHEDULE := [⟨5, 2⟩, ⟨5, 1⟩] }.getBlobParameters 5 = ⟨5, 2⟩ := by
  -- Both lists are already sorted by descending epoch, so the stable sort keeps them.
  simp only [getBlobParameters, latestStarted]
  rw [List.mergeSort_of_pairwise (by decide), List.mergeSort_of_pairwise (by decide)]
  simp

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
  unfold getScheduledGasLimit
  rw [latestStarted_perm perm distinct]

/-- The rules that a valid gas limit schedule meets, and no others.

No two entries share a first epoch, and each entry starts at or after the first epoch of Gloas. -/
theorem gasLimitScheduleValid_iff :
    config.gasLimitScheduleValid = true ↔
      (config.GAS_LIMIT_SCHEDULE.map (·.EPOCH)).Nodup ∧
        ∀ entry ∈ config.GAS_LIMIT_SCHEDULE, config.GLOAS_FORK_EPOCH ≤ entry.EPOCH := by
  simp [gasLimitScheduleValid, List.all_eq_true]

/-- The blob schedule of the mainnet configuration meets the rules of Fulu. -/
theorem blobScheduleValid_mainnet : mainnet.blobScheduleValid .mainnet = true := by decide

/-- The blob schedule of the minimal configuration meets the rules of Fulu. -/
theorem blobScheduleValid_minimal : minimal.blobScheduleValid .minimal = true := by decide

/-- The gas limit schedule of the mainnet configuration meets the rules of Gloas. -/
theorem gasLimitScheduleValid_mainnet : mainnet.gasLimitScheduleValid = true := by decide

/-- The gas limit schedule of the minimal configuration meets the rules of Gloas. -/
theorem gasLimitScheduleValid_minimal : minimal.gasLimitScheduleValid = true := by decide

end Config

end EthLib.Consensus

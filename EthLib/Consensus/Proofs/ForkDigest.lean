module

public import EthLib.Consensus.ForkDigest
public import EthLib.Consensus.Proofs.ForkSchedule
public import EthLib.Consensus.Proofs.Signing
public import Mathlib.Data.List.Find

/-!
# Proofs: the fork that a fork digest names

The fork digest can change only at a short list of epochs.

The fork and the digest at an epoch are those at the latest epoch of the list at or before it.

So the digest of every epoch is the digest of an epoch of the list.

An epoch that the search finds is in the list, and it has the digest.

A finite check of the configuration asks that the search read the right fork from each such digest.

On a chain that passes it, the search reads from a digest the fork at which it was computed.

The check is needed.

On mainnet with Altair given the version of genesis, Phase 0 and Altair share a digest.

There the check fails, and the search reads Phase 0 from the digest of Altair.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

namespace Config

variable {config : Config}

/-- Removing repeats from a sorted list keeps its members and makes it strictly increasing. -/
private theorem eraseDups_of_sorted : ∀ (epochs : List Epoch), epochs.Pairwise (· ≤ ·) →
    (∀ epoch, epoch ∈ epochs.eraseDups ↔ epoch ∈ epochs) ∧
      epochs.eraseDups.Pairwise (· < ·) ∧ epochs.eraseDups.length ≤ epochs.length
  | [], _ => by simp
  | first :: rest, sorted => by
    have later := eraseDups_of_sorted (rest.filter fun epoch => !epoch == first)
      ((List.pairwise_cons.mp sorted).2.filter _)
    rw [List.eraseDups_cons]
    refine ⟨fun epoch => ?_, ?_, ?_⟩
    · by_cases same : epoch = first <;> simp [later.1, same]
    · refine List.pairwise_cons.mpr ⟨fun epoch member => ?_, later.2.1⟩
      have kept := (later.1 epoch).mp member
      simp only [List.mem_filter] at kept
      have := (List.pairwise_cons.mp sorted).1 epoch kept.1
      grind
    · have := List.length_filter_le (fun epoch => !epoch == first) rest
      simp only [List.length_cons]
      omega
termination_by epochs => epochs.length
decreasing_by have := List.length_filter_le (fun epoch => !epoch == first) rest; simp_all; omega

/-- The epochs that the list sorts, before it removes repeats. -/
private abbrev candidates (config : Config) : List Epoch :=
  0 :: [config.ALTAIR_FORK_EPOCH, config.BELLATRIX_FORK_EPOCH, config.CAPELLA_FORK_EPOCH,
    config.DENEB_FORK_EPOCH, config.ELECTRA_FORK_EPOCH, config.FULU_FORK_EPOCH,
    config.GLOAS_FORK_EPOCH, config.HEZE_FORK_EPOCH] ++
      (config.BLOB_SCHEDULE.map (·.EPOCH)).filter (config.FULU_FORK_EPOCH ≤ ·)

/-- The list has the candidates as members, increases strictly, and is no longer than them. -/
private theorem digestEpochs_spec :
    (∀ epoch, epoch ∈ config.digestEpochs ↔ epoch ∈ candidates config) ∧
      config.digestEpochs.Pairwise (· < ·) ∧
      config.digestEpochs.length ≤ (candidates config).length := by
  have sorted := List.pairwise_mergeSort (le := fun a b : Epoch => decide (a ≤ b))
    (fun a b c ab bc => by simp_all [UInt64.le_iff_toNat_le]; omega)
    (fun a b => by simp [UInt64.le_iff_toNat_le]; omega) (candidates config)
  have := eraseDups_of_sorted _ (by simpa using sorted)
  simpa [digestEpochs] using this

/-- The fold of the latest start returns the seed or a member.

It is at or before the epoch when the seed is.

It is at least the seed, and at least each member at or before the epoch. -/
private theorem foldl_latest (epoch : Epoch) : ∀ (epochs : List Epoch) (seed : Epoch),
    let result := epochs.foldl (fun start next => if next ≤ epoch then max start next else start)
      seed
    (result = seed ∨ result ∈ epochs) ∧ (seed ≤ epoch → result ≤ epoch) ∧ seed ≤ result ∧
      ∀ start ∈ epochs, start ≤ epoch → start ≤ result
  | [], seed => by simp
  | next :: rest, seed => by
    have step : ((if next ≤ epoch then max seed next else seed) = seed ∨
        (if next ≤ epoch then max seed next else seed) = next) ∧
        (seed ≤ epoch → (if next ≤ epoch then max seed next else seed) ≤ epoch) ∧
        seed ≤ (if next ≤ epoch then max seed next else seed) ∧
        (next ≤ epoch → next ≤ (if next ≤ epoch then max seed next else seed)) := by
      by_cases started : next ≤ epoch <;> by_cases grows : seed ≤ next <;>
        simp only [UInt64.max_def, started, grows, ↓reduceIte, true_or, or_true, true_and,
          and_true, UInt64.le_refl, imp_self]
      all_goals simp_all [UInt64.le_iff_toNat_le]
      all_goals omega
    obtain ⟨mem, le, ge, latest⟩ := foldl_latest epoch rest
      (if next ≤ epoch then max seed next else seed)
    simp only [List.foldl_cons, List.mem_cons]
    generalize (if next ≤ epoch then max seed next else seed) = middle at *
    generalize List.foldl _ middle rest = result at *
    grind

/-- Epoch 0 is in the list. -/
theorem zero_mem_digestEpochs : (0 : Epoch) ∈ config.digestEpochs := by
  simp [digestEpochs_spec.1]

/-- The first epoch of each consensus fork from Altair to Heze is in the list. -/
theorem forkEpochs_mem_digestEpochs :
    config.ALTAIR_FORK_EPOCH ∈ config.digestEpochs ∧
      config.BELLATRIX_FORK_EPOCH ∈ config.digestEpochs ∧
      config.CAPELLA_FORK_EPOCH ∈ config.digestEpochs ∧
      config.DENEB_FORK_EPOCH ∈ config.digestEpochs ∧
      config.ELECTRA_FORK_EPOCH ∈ config.digestEpochs ∧
      config.FULU_FORK_EPOCH ∈ config.digestEpochs ∧
      config.GLOAS_FORK_EPOCH ∈ config.digestEpochs ∧
      config.HEZE_FORK_EPOCH ∈ config.digestEpochs := by
  simp [digestEpochs_spec.1]

/-- The first epoch of each blob schedule entry from the first epoch of Fulu is in the list. -/
theorem blobEpoch_mem_digestEpochs {entry : BlobScheduleEntry}
    (member : entry ∈ config.BLOB_SCHEDULE) (fulu : config.FULU_FORK_EPOCH ≤ entry.EPOCH) :
    entry.EPOCH ∈ config.digestEpochs := by
  rw [digestEpochs_spec.1]
  exact List.mem_append_right _
    (List.mem_filter.mpr ⟨List.mem_map_of_mem member, by simpa using fulu⟩)

/-- The list is strictly increasing. -/
theorem digestEpochs_sorted : config.digestEpochs.Pairwise (· < ·) := by
  exact digestEpochs_spec.2.1

/-- The list has at most nine epochs, plus one for each entry of the blob schedule. -/
theorem length_digestEpochs_le : config.digestEpochs.length ≤ 9 + config.BLOB_SCHEDULE.length := by
  have := (digestEpochs_spec (config := config)).2.2
  simp at this
  have := List.length_filter_le (config.FULU_FORK_EPOCH ≤ ·) (config.BLOB_SCHEDULE.map (·.EPOCH))
  simp at this
  omega

/-- The latest epoch of the list at or before an epoch is in the list. -/
theorem digestStart_mem (epoch : Epoch) : config.digestStart epoch ∈ config.digestEpochs := by
  rcases (foldl_latest epoch config.digestEpochs 0).1 with zero | member
  · rw [digestStart, zero]
    exact zero_mem_digestEpochs
  · exact member

/-- The latest epoch of the list at or before an epoch is at or before it. -/
theorem digestStart_le (epoch : Epoch) : config.digestStart epoch ≤ epoch := by
  exact (foldl_latest epoch config.digestEpochs 0).2.1 UInt64.zero_le

/-- Each epoch of the list at or before an epoch is at or before its latest such epoch. -/
theorem le_digestStart {start epoch : Epoch} (member : start ∈ config.digestEpochs)
    (before : start ≤ epoch) : start ≤ config.digestStart epoch := by
  exact (foldl_latest epoch config.digestEpochs 0).2.2.2 start member before

/-- Two epochs on the same side of every epoch of the list have the same fork. -/
theorem forkAtEpoch_eq_of_sameSide {first second : Epoch}
    (sameSide : ∀ start ∈ config.digestEpochs, start ≤ first ↔ start ≤ second) :
    config.forkAtEpoch first = config.forkAtEpoch second := by
  obtain ⟨altair, bellatrix, capella, deneb, electra, fulu, gloas, heze⟩ :=
    forkEpochs_mem_digestEpochs (config := config)
  simp only [forkAtEpoch, sameSide _ altair, sameSide _ bellatrix, sameSide _ capella,
    sameSide _ deneb, sameSide _ electra, sameSide _ fulu, sameSide _ gloas, sameSide _ heze]

/-- The list starts with epoch 0. -/
private theorem digestEpochs_eq_zero_cons : ∃ rest, config.digestEpochs = 0 :: rest := by
  have sorted := digestEpochs_sorted (config := config)
  have zero := zero_mem_digestEpochs (config := config)
  cases listed : config.digestEpochs with
  | nil => simp [listed] at zero
  | cons head rest =>
    rw [listed] at sorted zero
    rcases List.mem_cons.mp zero with same | later
    · exact ⟨rest, by rw [same]⟩
    · have := (List.pairwise_cons.mp sorted).1 0 later
      simp [UInt64.lt_iff_toNat_lt] at this

/-- The latest epoch of the list at or before an epoch is on its side of every epoch of the list. -/
private theorem sameSide_digestStart (epoch : Epoch) :
    ∀ start ∈ config.digestEpochs, start ≤ config.digestStart epoch ↔ start ≤ epoch :=
  fun _ member => ⟨fun before => UInt64.le_trans before (digestStart_le epoch),
    le_digestStart member⟩

/-- The fork at an epoch is the fork at the latest epoch of the list at or before it. -/
theorem forkAtEpoch_digestStart (epoch : Epoch) :
    config.forkAtEpoch (config.digestStart epoch) = config.forkAtEpoch epoch := by
  exact forkAtEpoch_eq_of_sameSide (sameSide_digestStart epoch)

end Config

variable {config : Config} {genesisValidatorsRoot : Root}

/-- From Fulu, two epochs on the same side of every epoch of the list have the same blob limit. -/
private theorem getBlobParameters_eq_of_sameSide {first second : Epoch}
    (sameSide : ∀ start ∈ config.digestEpochs, start ≤ first ↔ start ≤ second)
    (fulu : config.FULU_FORK_EPOCH ≤ first) :
    config.getBlobParameters first = config.getBlobParameters second := by
  have fuluMember := (Config.forkEpochs_mem_digestEpochs (config := config)).2.2.2.2.2.1
  have fulu' := (sameSide _ fuluMember).mp fulu
  unfold Config.getBlobParameters latestStarted
  rw [List.find?_congr fun entry member => ?_]
  by_cases early : entry.EPOCH < config.FULU_FORK_EPOCH
  · simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    simp only [decide_eq_decide]
    omega
  · have late := Config.blobEpoch_mem_digestEpochs (List.mem_mergeSort.mp member)
      (by simpa [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] using early)
    simpa using sameSide _ late

/-- Two epochs on the same side of every epoch of the list have the same fork digest. -/
theorem computeForkDigest_eq_of_sameSide {first second : Epoch}
    (sameSide : ∀ start ∈ config.digestEpochs, start ≤ first ↔ start ≤ second) :
    computeForkDigest config genesisValidatorsRoot first =
      computeForkDigest config genesisValidatorsRoot second := by
  have fulu := sameSide _ (Config.forkEpochs_mem_digestEpochs (config := config)).2.2.2.2.2.1
  unfold computeForkDigest Config.computeForkVersion
  rw [Config.forkAtEpoch_eq_of_sameSide sameSide]
  by_cases early : first < config.FULU_FORK_EPOCH
  · have early' : second < config.FULU_FORK_EPOCH := by
      simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
      omega
    simp only [early, early', ↓reduceIte]
  · have late' : ¬second < config.FULU_FORK_EPOCH := by
      simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
      omega
    rw [getBlobParameters_eq_of_sameSide sameSide
      (by simpa [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] using early)]
    simp only [early, late', ↓reduceIte]

/-- The fork digest at an epoch is the one at the latest epoch of the list at or before it. -/
theorem computeForkDigest_digestStart (epoch : Epoch) :
    computeForkDigest config genesisValidatorsRoot (config.digestStart epoch) =
      computeForkDigest config genesisValidatorsRoot epoch := by
  exact computeForkDigest_eq_of_sameSide (Config.sameSide_digestStart epoch)

/-- An epoch that the search finds is in the list, and it has the digest. -/
theorem forkOfDigest_sound {digest : ForkDigest} {start : Epoch}
    (found : forkOfDigest config genesisValidatorsRoot digest = some start) :
    start ∈ config.digestEpochs ∧
      computeForkDigest config genesisValidatorsRoot start = .ok digest := by
  refine ⟨List.mem_of_find?_eq_some found, ?_⟩
  have matched := List.find?_some found
  split at matched
  · next computed => simpa [computed] using matched
  · contradiction

/-- The search finds an epoch for the digest of every epoch. -/
theorem forkOfDigest_isSome {epoch : Epoch} {digest : ForkDigest}
    (computed : computeForkDigest config genesisValidatorsRoot epoch = .ok digest) :
    (forkOfDigest config genesisValidatorsRoot digest).isSome := by
  refine List.find?_isSome.mpr ⟨config.digestStart epoch, Config.digestStart_mem epoch, ?_⟩
  simp [computeForkDigest_digestStart, computed]

/-- On a chain that passes the check, the search reads back the fork at which a digest was computed.

This holds at every epoch, not only at those of the list. -/
theorem forkOfDigest_recovers {epoch : Epoch} {digest : ForkDigest}
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (computed : computeForkDigest config genesisValidatorsRoot epoch = .ok digest) :
    (forkOfDigest config genesisValidatorsRoot digest).map config.forkAtEpoch =
      some (config.forkAtEpoch epoch) := by
  have checked := List.all_eq_true.mp identify _ (Config.digestStart_mem epoch)
  rw [computeForkDigest_digestStart, computed] at checked
  rw [← Config.forkAtEpoch_digestStart epoch]
  simpa using checked

/-- Mainnet, with Altair given the version of genesis.

Phase 0 and Altair then share a digest. -/
def sharedVersionConfig : Config :=
  { Config.mainnet with ALTAIR_FORK_VERSION := Config.mainnet.GENESIS_FORK_VERSION }

/-- With Altair given the version of genesis, Altair's first epoch has the digest of epoch 0. -/
theorem computeForkDigest_sharedVersion_altair :
    computeForkDigest sharedVersionConfig genesisValidatorsRoot
        sharedVersionConfig.ALTAIR_FORK_EPOCH =
      computeForkDigest sharedVersionConfig genesisValidatorsRoot 0 := by
  have version : sharedVersionConfig.computeForkVersion sharedVersionConfig.ALTAIR_FORK_EPOCH =
      sharedVersionConfig.computeForkVersion 0 := by
    decide
  have altair : sharedVersionConfig.ALTAIR_FORK_EPOCH < sharedVersionConfig.FULU_FORK_EPOCH := by
    decide
  have zero : (0 : Epoch) < sharedVersionConfig.FULU_FORK_EPOCH := by decide
  unfold computeForkDigest
  rw [version]
  simp only [altair, zero, ↓reduceIte]

/-- With Altair given the version of genesis, the search reads Phase 0 from the digest of Altair. -/
theorem forkOfDigest_sharedVersion_altair {digest : ForkDigest}
    (computed : computeForkDigest sharedVersionConfig genesisValidatorsRoot
      sharedVersionConfig.ALTAIR_FORK_EPOCH = .ok digest) :
    (forkOfDigest sharedVersionConfig genesisValidatorsRoot digest).map
        sharedVersionConfig.forkAtEpoch = some .phase0 ∧
      sharedVersionConfig.forkAtEpoch sharedVersionConfig.ALTAIR_FORK_EPOCH = .altair := by
  have zero : computeForkDigest sharedVersionConfig genesisValidatorsRoot 0 = .ok digest := by
    rw [← computeForkDigest_sharedVersion_altair, computed]
  obtain ⟨rest, list⟩ := Config.digestEpochs_eq_zero_cons (config := sharedVersionConfig)
  have found : forkOfDigest sharedVersionConfig genesisValidatorsRoot digest = some 0 := by
    simp [forkOfDigest, list, zero]
  rw [found]
  exact ⟨by decide, by decide⟩

/-- With Altair given the version of genesis, the check fails.

This holds whatever the genesis validators root. -/
theorem digestsIdentify_sharedVersion :
    digestsIdentify sharedVersionConfig genesisValidatorsRoot = false := by
  obtain ⟨digest, computed⟩ := computeForkDigest_total sharedVersionConfig genesisValidatorsRoot
    sharedVersionConfig.ALTAIR_FORK_EPOCH
  obtain ⟨phase0, altair⟩ := forkOfDigest_sharedVersion_altair computed
  refine List.all_eq_false.mpr ⟨_, Config.forkEpochs_mem_digestEpochs.1, ?_⟩
  simp [computed, phase0, altair]

end EthLib.Consensus

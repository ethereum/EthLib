module

public import EthLib.Consensus.Enr
public import EthLib.Consensus.Proofs.ForkDigest
public import EthLib.Networking.Proofs.Enr.Consensus
public import EthLib.Networking.Proofs.Enr.V4

/-!
# Proofs: the consensus entries that a node writes

The digest stays the same at every epoch from the current one up to the next fork epoch.

At a BPO epoch, the fork does not change, so the next fork version is the current version.

A node reading a record built from these entries, at the writer's fork, gets them back.

A node never disconnects for a different next fork before the earlier next fork epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base
open Serialization.Ssz
open Networking.Enr
open Networking.Proofs.Enr.Consensus
open Cryptography.Secp256k1

/-! ## The next fork -/

/-- In a sorted list, the first epoch after an epoch comes at or before every other such epoch. -/
private theorem le_of_find? {epochs : List Epoch} (sorted : epochs.Pairwise (· < ·))
    {epoch first : Epoch} (h : epochs.find? (epoch < ·) = some first) {start : Epoch}
    (member : start ∈ epochs) (after : epoch < start) : first ≤ start := by
  obtain ⟨_, before, rest, rfl, skipped⟩ := List.find?_eq_some_iff_append.mp h
  rcases List.mem_append.mp member with early | late
  · -- The epochs before the first one are not after the epoch.
    have := skipped start early
    simp [after] at this
  · rcases List.mem_cons.mp late with rfl | later
    · exact UInt64.le_refl _
    · -- The list is sorted, so an epoch after the first one is larger.
      have := (List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 start later
      exact UInt64.le_of_lt this

/-- No epoch of the list after an epoch comes before the next fork epoch of its `eth2` value. -/
theorem nextForkEpoch_le_of_enrForkId {config : Config} {genesisValidatorsRoot : Root}
    {epoch : Epoch} {e : EnrForkId} (h : enrForkId config genesisValidatorsRoot epoch = .ok e)
    {start : Epoch} (member : start ∈ config.digestEpochs) (after : epoch < start) :
    e.nextForkEpoch ≤ start := by
  unfold enrForkId at h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  unfold Config.nextDigestEpoch at h
  cases hf : config.digestEpochs.find? (epoch < ·) with
  | none =>
    -- No epoch of the list is after the epoch, which the start contradicts.
    have := List.find?_eq_none.mp hf start member
    simp [after] at this
  | some first =>
    have hle := le_of_find? Config.digestEpochs_sorted hf member after
    by_cases far : first = FAR_FUTURE_EPOCH
    · simp only [hf, far, Option.filter, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [far] at hle
      exact hle
    · simp only [hf, far, Option.filter, ne_eq, not_false_eq_true, decide_true, ↓reduceIte,
        pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hle

/-- The digest is the same at every epoch from an epoch up to its next fork epoch. -/
theorem computeForkDigest_of_lt_nextForkEpoch {config : Config} {genesisValidatorsRoot : Root}
    {epoch : Epoch} {e : EnrForkId} (h : enrForkId config genesisValidatorsRoot epoch = .ok e)
    {later : Epoch} (from_ : epoch ≤ later) (before : later < e.nextForkEpoch) :
    computeForkDigest config genesisValidatorsRoot later =
      computeForkDigest config genesisValidatorsRoot epoch := by
  apply computeForkDigest_eq_of_sameSide
  intro start member
  constructor
  · intro early
    -- An epoch of the list after the epoch would be at or after the next fork epoch.
    refine Classical.byContradiction fun late => ?_
    have bound := nextForkEpoch_le_of_enrForkId h member (UInt64.not_le.mp late)
    exact absurd (UInt64.lt_of_lt_of_le before bound) (UInt64.not_lt.mpr early)
  · intro early
    exact UInt64.le_trans early from_

/-- The next digest epoch is the first epoch of the list after the epoch, and comes after it. -/
private theorem nextDigestEpoch_spec {config : Config} {epoch next : Epoch}
    (hnext : config.nextDigestEpoch epoch = some next) :
    config.digestEpochs.find? (epoch < ·) = some next ∧ next ∈ config.digestEpochs ∧
      epoch < next := by
  unfold Config.nextDigestEpoch at hnext
  have found := (Option.filter_eq_some_iff.mp hnext).1
  exact ⟨found, List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

/-- Another epoch of the list is before the next digest epoch exactly when it is before the epoch.
-/
private theorem le_next_iff {config : Config} {epoch next : Epoch}
    (hnext : config.nextDigestEpoch epoch = some next) {start : Epoch}
    (member : start ∈ config.digestEpochs) (other : start ≠ next) :
    start ≤ next ↔ start ≤ epoch := by
  obtain ⟨found, _, after⟩ := nextDigestEpoch_spec hnext
  constructor
  · intro early
    -- An epoch of the list after the epoch is at or after the next one, so it is the next one.
    refine Classical.byContradiction fun late => other ?_
    exact UInt64.le_antisymm early
      (le_of_find? Config.digestEpochs_sorted found member (UInt64.not_le.mp late))
  · intro early
    exact UInt64.le_of_lt (UInt64.lt_of_le_of_lt early after)

/-- When the next digest epoch is the first epoch of no consensus fork, the fork stays the same.

Such an epoch is a BPO epoch: the first epoch of a blob schedule entry. -/
theorem forkAtEpoch_nextDigestEpoch {config : Config} {epoch next : Epoch}
    (hnext : config.nextDigestEpoch epoch = some next)
    (notFork : next ∉ [config.ALTAIR_FORK_EPOCH, config.BELLATRIX_FORK_EPOCH,
      config.CAPELLA_FORK_EPOCH, config.DENEB_FORK_EPOCH, config.ELECTRA_FORK_EPOCH,
      config.FULU_FORK_EPOCH, config.GLOAS_FORK_EPOCH, config.HEZE_FORK_EPOCH]) :
    config.forkAtEpoch next = config.forkAtEpoch epoch := by
  obtain ⟨altair, bellatrix, capella, deneb, electra, fulu, gloas, heze⟩ :=
    Config.forkEpochs_mem_digestEpochs (config := config)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at notFork
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := notFork
  -- Each fork epoch is on the same side of both epochs, so the fork reads the same.
  simp only [Config.forkAtEpoch, le_next_iff hnext altair (Ne.symm n1),
    le_next_iff hnext bellatrix (Ne.symm n2), le_next_iff hnext capella (Ne.symm n3),
    le_next_iff hnext deneb (Ne.symm n4), le_next_iff hnext electra (Ne.symm n5),
    le_next_iff hnext fulu (Ne.symm n6), le_next_iff hnext gloas (Ne.symm n7),
    le_next_iff hnext heze (Ne.symm n8)]

/-- The next fork epoch of an `eth2` value is the next digest epoch, when one is planned. -/
theorem nextForkEpoch_of_nextDigestEpoch {config : Config} {genesisValidatorsRoot : Root}
    {epoch next : Epoch} {e : EnrForkId} (h : enrForkId config genesisValidatorsRoot epoch = .ok e)
    (hnext : config.nextDigestEpoch epoch = some next) : e.nextForkEpoch = next := by
  unfold enrForkId at h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  simp only [hnext, pure, Except.pure, Except.ok.injEq] at h
  subst h
  rfl

/-- At a BPO epoch, the next fork version of an `eth2` value is the current version.

A BPO epoch is a next digest epoch that is the first epoch of no consensus fork. -/
theorem nextForkVersion_of_nextDigestEpoch {config : Config} {genesisValidatorsRoot : Root}
    {epoch next : Epoch} {e : EnrForkId} (h : enrForkId config genesisValidatorsRoot epoch = .ok e)
    (hnext : config.nextDigestEpoch epoch = some next)
    (notFork : next ∉ [config.ALTAIR_FORK_EPOCH, config.BELLATRIX_FORK_EPOCH,
      config.CAPELLA_FORK_EPOCH, config.DENEB_FORK_EPOCH, config.ELECTRA_FORK_EPOCH,
      config.FULU_FORK_EPOCH, config.GLOAS_FORK_EPOCH, config.HEZE_FORK_EPOCH]) :
    e.nextForkVersion = config.computeForkVersion epoch := by
  unfold enrForkId at h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  simp only [hnext, pure, Except.pure, Except.ok.injEq] at h
  subst h
  -- The version reads only the fork, which is the same at both epochs.
  simp only [Config.computeForkVersion, forkAtEpoch_nextDigestEpoch hnext notFork]

/-! ## Reading back the written entries -/

/-- A record built from the consensus pairs of a node reads back its entries at the node's fork.

The sync committee subnets read back from Altair, the custody group count and `nfd` from Fulu. -/
theorem readEntries_consensusPairs {config : Config} {genesisValidatorsRoot : Root}
    {epoch : Epoch} {count : UInt64} [NeZero count.toNat] {attnets : Attnets count}
    {syncnets : Syncnets} {cgc : UInt64} {pairs : List (ByteArray × Serialization.Rlp.Item)}
    {eth2 : EnrForkId} {nfd : ForkDigest} {sk : Fn} {seq : UInt64} {r : Enr}
    (hp : consensusPairs config genesisValidatorsRoot epoch attnets syncnets cgc = .ok pairs)
    (heth2 : enrForkId config genesisValidatorsRoot epoch = .ok eth2)
    (hnfd : nextForkDigest config genesisValidatorsRoot epoch = .ok nfd)
    (hr : makeRecordV4 sk seq pairs = .ok r) :
    readEntries count (config.forkAtEpoch epoch) r = .ok ⟨eth2, some attnets,
      if .altair ≤ config.forkAtEpoch epoch then some syncnets else none,
      if .fusaka ≤ config.forkAtEpoch epoch then some cgc else none,
      if .fusaka ≤ config.forkAtEpoch epoch then some nfd else none⟩ := by
  simp only [consensusPairs, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at hp
  obtain ⟨eth2', h1, eth2Bytes, heb, attB, hab, synB, hsb, nfd', h2, hpairs⟩ := hp
  rw [heth2, Except.ok.injEq] at h1
  rw [hnfd, Except.ok.injEq] at h2
  subst h1 h2 hpairs
  -- The builder's own keys are other keys, so each consensus key reads from the pairs.
  have look (k : ConsensusKey) := get_of_makeRecordV4 (key := k.name.toUTF8) hr
    (by cases k <;> decide) (by cases k <;> decide)
  -- From Fulu on, the node writes the Fulu entries.
  have fulu (hf : Fork.fusaka ≤ config.forkAtEpoch epoch) : writesFuluEntries config epoch :=
    by simp [writesFuluEntries, hf]
  -- The sync committee subnets have four bits, so their bitvector reads back.
  have : NeZero SYNC_COMMITTEE_SUBNET_COUNT := ⟨by decide⟩
  apply readEntries_eq_ok_iff.mpr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- Each key appears once among the pairs, which a comparison of byte literals shows.
  · have l := look .eth2
    cases hw : writesFuluEntries config epoch <;>
      by_cases ha : Fork.altair ≤ config.forkAtEpoch epoch <;>
      simp +decide [hw, ha] at l <;>
      exact readSsz_eq_ok_some_iff.mpr ⟨_, l, heb⟩
  · have l := look .attnets
    cases hw : writesFuluEntries config epoch <;>
      by_cases ha : Fork.altair ≤ config.forkAtEpoch epoch <;>
      simp +decide [hw, ha] at l <;>
      exact readSsz_eq_ok_some_iff.mpr ⟨_, l, hab⟩
  -- The sync committee subnets are read and written from Altair.
  · by_cases ha : Fork.altair ≤ config.forkAtEpoch epoch
    · have l := look .syncnets
      cases hw : writesFuluEntries config epoch <;>
        simp +decide [hw, ha] at l <;>
        simp only [readAt, ConsensusKey.since, ha, ↓reduceIte] <;>
        exact readSsz_eq_ok_some_iff.mpr ⟨_, l, hsb⟩
    · simp [readAt, ConsensusKey.since, ha, pure, Except.pure]
  -- The custody group count and the next fork digest are read and written from Fulu.
  · by_cases hf : Fork.fusaka ≤ config.forkAtEpoch epoch
    · have l := look .cgc
      by_cases ha : Fork.altair ≤ config.forkAtEpoch epoch <;>
        simp +decide [fulu hf, ha] at l <;>
        simp only [hf, ↓reduceIte] <;>
        exact readRequiredAt_eq_ok_some_iff.mpr
          ⟨by simpa [ConsensusKey.since] using hf, readCgc_eq_ok_some_iff.mpr l⟩
    · simp [readRequiredAt, ConsensusKey.since, hf, pure, Except.pure]
  · by_cases hf : Fork.fusaka ≤ config.forkAtEpoch epoch
    · have l := look .nfd
      by_cases ha : Fork.altair ≤ config.forkAtEpoch epoch <;>
        simp +decide [fulu hf, ha] at l <;>
        simp only [hf, ↓reduceIte] <;>
        exact readRequiredAt_eq_ok_some_iff.mpr
          ⟨by simpa [ConsensusKey.since] using hf, readSsz_digest_eq_ok_some_iff.mpr l⟩
    · simp [readRequiredAt, ConsensusKey.since, hf, pure, Except.pure]

/-- Once Fulu has an epoch, a record built from the consensus pairs holds `cgc` and `nfd`. -/
private theorem lookup_fulu_of_consensusPairs {config : Config} {genesisValidatorsRoot : Root}
    {epoch : Epoch} {count : UInt64} {attnets : Attnets count} {syncnets : Syncnets} {cgc : UInt64}
    {pairs : List (ByteArray × Serialization.Rlp.Item)} {nfd : ForkDigest} {sk : Fn}
    {seq : UInt64} {r : Enr}
    (hp : consensusPairs config genesisValidatorsRoot epoch attnets syncnets cgc = .ok pairs)
    (hnfd : nextForkDigest config genesisValidatorsRoot epoch = .ok nfd)
    (hr : makeRecordV4 sk seq pairs = .ok r)
    (scheduled : config.FULU_FORK_EPOCH ≠ FAR_FUTURE_EPOCH) :
    lookup r .cgc = some (.scalar cgc.toNat) ∧ lookup r .nfd = some (.bytes ⟨nfd.toArray⟩) := by
  simp only [consensusPairs, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at hp
  obtain ⟨_, _, _, _, _, _, _, _, nfd', h2, hpairs⟩ := hp
  rw [hnfd, Except.ok.injEq] at h2
  subst h2 hpairs
  have hw : writesFuluEntries config epoch = true := by simp [writesFuluEntries, scheduled]
  have lCgc := get_of_makeRecordV4 (key := ConsensusKey.cgc.name.toUTF8) hr (by decide) (by decide)
  have lNfd := get_of_makeRecordV4 (key := ConsensusKey.nfd.name.toUTF8) hr (by decide) (by decide)
  -- Each key appears once among the pairs, which a comparison of byte literals shows.
  by_cases ha : Fork.altair ≤ config.forkAtEpoch epoch <;>
    simp +decide [hw, ha] at lCgc lNfd <;>
    exact ⟨lCgc, lNfd⟩

/-- Once Fulu has an epoch, a record built from the consensus pairs holds the `cgc` written.

This holds at every epoch, before Fulu too, as the Fulu networking text requires. -/
theorem lookup_cgc_of_consensusPairs {config : Config} {genesisValidatorsRoot : Root}
    {epoch : Epoch} {count : UInt64} {attnets : Attnets count} {syncnets : Syncnets} {cgc : UInt64}
    {pairs : List (ByteArray × Serialization.Rlp.Item)} {nfd : ForkDigest} {sk : Fn}
    {seq : UInt64} {r : Enr}
    (hp : consensusPairs config genesisValidatorsRoot epoch attnets syncnets cgc = .ok pairs)
    (hnfd : nextForkDigest config genesisValidatorsRoot epoch = .ok nfd)
    (hr : makeRecordV4 sk seq pairs = .ok r)
    (scheduled : config.FULU_FORK_EPOCH ≠ FAR_FUTURE_EPOCH) :
    lookup r .cgc = some (.scalar cgc.toNat) :=
  (lookup_fulu_of_consensusPairs hp hnfd hr scheduled).1

/-- Once Fulu has an epoch, a record built from the consensus pairs holds the `nfd` written.

This holds at every epoch, before Fulu too, as the Fulu networking text requires. -/
theorem lookup_nfd_of_consensusPairs {config : Config} {genesisValidatorsRoot : Root}
    {epoch : Epoch} {count : UInt64} {attnets : Attnets count} {syncnets : Syncnets} {cgc : UInt64}
    {pairs : List (ByteArray × Serialization.Rlp.Item)} {nfd : ForkDigest} {sk : Fn}
    {seq : UInt64} {r : Enr}
    (hp : consensusPairs config genesisValidatorsRoot epoch attnets syncnets cgc = .ok pairs)
    (hnfd : nextForkDigest config genesisValidatorsRoot epoch = .ok nfd)
    (hr : makeRecordV4 sk seq pairs = .ok r)
    (scheduled : config.FULU_FORK_EPOCH ≠ FAR_FUTURE_EPOCH) :
    lookup r .nfd = some (.bytes ⟨nfd.toArray⟩) :=
  (lookup_fulu_of_consensusPairs hp hnfd hr scheduled).2

/-! ## Peers -/

/-- With the same digest, a node never disconnects before the earlier next fork epoch. -/
theorem mayDisconnect_of_lt {localId remoteId : EnrForkId} {localNfd remoteNfd : Option ForkDigest}
    {epoch : Epoch} (same : localId.forkDigest = remoteId.forkDigest)
    (before : epoch < min localId.nextForkEpoch remoteId.nextForkEpoch) :
    mayDisconnect localId remoteId localNfd remoteNfd epoch = false := by
  have : ¬ min localId.nextForkEpoch remoteId.nextForkEpoch ≤ epoch := UInt64.not_le.mpr before
  simp [mayDisconnect, same, this]

/-- With the same digest and other entries, a node may disconnect from the earlier next fork epoch.
-/
theorem mayDisconnect_of_le {localId remoteId : EnrForkId} {localNfd remoteNfd : Option ForkDigest}
    {epoch : Epoch} (differ : ¬ (localId = remoteId ∧ localNfd = remoteNfd))
    (boundary : min localId.nextForkEpoch remoteId.nextForkEpoch ≤ epoch) :
    mayDisconnect localId remoteId localNfd remoteNfd epoch = true := by
  simp only [mayDisconnect, differ, boundary, ite_false, decide_true, ite_self]

/-- A node may disconnect from a peer whose digest differs, at any epoch. -/
theorem mayDisconnect_of_ne {localId remoteId : EnrForkId} {localNfd remoteNfd : Option ForkDigest}
    {epoch : Epoch} (differ : localId.forkDigest ≠ remoteId.forkDigest) :
    mayDisconnect localId remoteId localNfd remoteNfd epoch = true := by
  simp [mayDisconnect, differ]

/-- A node never disconnects from a peer with the same entries. -/
theorem mayDisconnect_self (id : EnrForkId) (nfd : Option ForkDigest) (epoch : Epoch) :
    mayDisconnect id id nfd nfd epoch = false := by
  simp [mayDisconnect]

end EthLib.Consensus

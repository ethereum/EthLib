module

public import EthLib.Consensus.LightClient.Sync
public import EthLib.Serialization.Proofs.Ssz.BranchRandomOracle
import EthLib.Consensus.Proofs.Containers.SyncCommittee
import EthLib.Consensus.Proofs.LightClient.Authenticate

/-!
# Proofs: two sync committees of one state root in the random oracle model

A bootstrap proves its current sync committee with a branch against a state root.

An update proves its next sync committee the same way.

An adversary outputs a state root and two committees with a branch each.

The generalized index of the branches is fixed before the run.

It wins with two different committees, if both branches pass the check at that index.

The experiment roots both committees and climbs both branches, with the oracle as the node hash.

Each win exposes two different queried inputs with one answer, so the birthday bound applies.

The count grows with the size of a committee and the depth of the index.

At mainnet, an adversary of `q` calls gives a bound of `(q + 2050 + 2 * depth)^2 / 2^256`.

The depth of both indices is 5 before Electra, 6 from Electra and 11 from Gloas.

With SHA-256 as the node hash, a win is two different committees that the branch check accepts.

That result needs a committee of at least one member.

Two accepted bootstraps with one state root and slot and different committees give one.

So do two such updates that pass the check of the next committee.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Serialization.Ssz.RandomOracle
open OracleComp OracleSpec ENNReal
open Cryptography.Merkle.RandomOracle (Collision experimentWith experimentWith_queryBound
  prEvent_experimentWith_le)

variable {preset : Preset}

/-- What the adversary outputs: one state root, and two sync committees with a branch each. -/
structure SyncCommitteeClaim (preset : Preset) where
  /-- The state root that both branches must reach. -/
  root : Root
  /-- The first committee. -/
  first : SyncCommittee preset
  /-- The nodes of the branch of the first committee, from the committee up. -/
  firstBranch : List Bytes32
  /-- The second committee. -/
  second : SyncCommittee preset
  /-- The nodes of the branch of the second committee, from the committee up. -/
  secondBranch : List Bytes32

/-- What the committee experiment reports: the claim, and the climbs of both branches.

The climbs are absent when the index names no node, or a root of a committee cannot be read. -/
structure SyncCommitteeOutcome (preset : Preset) where
  /-- The state root, the two committees and their branches. -/
  claim : SyncCommitteeClaim preset
  /-- The subtree index, the roots of the committees, the climbed nodes and their roots. -/
  climbs : Option BranchOutcome

/-- The extraction for sync committees, with a node hash in any monad.

It roots both committees, then climbs the last nodes of each branch, as many as the depth.

The depth is the base-2 logarithm of the index, as in the check of a normalized branch. -/
def extractSyncCommittees {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray)
    (preset : Preset) (gindex : Nat) (claim : SyncCommitteeClaim preset) :
    m (SyncCommitteeOutcome preset) := do
  let firstRoot ← (hashTreeRootM (Hasher.ofHash hash) (SszType.desc (SyncCommittee preset))
    (SszType.toValue claim.first)).run
  let secondRoot ← (hashTreeRootM (Hasher.ofHash hash) (SszType.desc (SyncCommittee preset))
    (SszType.toValue claim.second)).run
  let climbs ← (match getSubtreeIndex gindex, firstRoot >>= toChunk, secondRoot >>= toChunk with
    | .ok index, .ok firstLeaf, .ok secondLeaf => do
      let climbs ← extractBranches hash (Nat.log2 gindex)
        ⟨index, firstLeaf, claim.firstBranch.drop (claim.firstBranch.length - Nat.log2 gindex),
          secondLeaf, claim.secondBranch.drop (claim.secondBranch.length - Nat.log2 gindex)⟩
      pure (some climbs)
    | _, _, _ => pure none)
  return ⟨claim, climbs⟩

/-- The adversary wins: two different committees whose branches climb to the claimed state root.

Each branch needs at least as many nodes as the depth, and zero nodes in front of that many. -/
def SyncCommitteeWins (gindex : Nat) (outcome : SyncCommitteeOutcome preset) : Prop :=
  outcome.claim.first ≠ outcome.claim.second ∧
    Nat.log2 gindex ≤ outcome.claim.firstBranch.length ∧
    Nat.log2 gindex ≤ outcome.claim.secondBranch.length ∧
    (∀ node ∈ outcome.claim.firstBranch.take
      (outcome.claim.firstBranch.length - Nat.log2 gindex), node = Vector.replicate 32 0) ∧
    (∀ node ∈ outcome.claim.secondBranch.take
      (outcome.claim.secondBranch.length - Nat.log2 gindex), node = Vector.replicate 32 0) ∧
    ∃ climbs, outcome.climbs = some climbs ∧
      climbs.firstRoot = .ok outcome.claim.root ∧ climbs.secondRoot = .ok outcome.claim.root

/-- The root of a sync committee hashes the root of its keys with that of its aggregate key.

The root of the aggregate key is one hash, and a failed root of the keys fails the committee.

It holds for a hash in any lawful monad. -/
theorem hashTreeRootM_syncCommittee {m : Type → Type} [Monad m] [LawfulMonad m]
    (hash : ByteArray → m ByteArray) (committee : SyncCommittee preset) :
    (hashTreeRootM (Hasher.ofHash hash) (SszType.desc (SyncCommittee preset))
        (SszType.toValue committee)).run = (do
      match ← (hashTreeRootM (Hasher.ofHash hash)
          (.vector (SszType.desc (Vector UInt8 48)) preset.SYNC_COMMITTEE_SIZE.toNat)
          (.seq (committee.pubkeys.toList.map SszType.toValue))).run with
      | .ok keys =>
        let aggregate ← hash ⟨committee.aggregatePubkey.toArray ++ Array.replicate 16 0⟩
        return .ok (← hash ⟨keys ++ aggregate.data⟩).data
      | .error error => return .error error) := by
  have aggregate : (hashTreeRootAtM (Hasher.ofHash hash) 2 (.byteVector 48)
      (.bytes committee.aggregatePubkey.toArray)).run = _ :=
    hashTreeRootAtM_bytes48 (Hasher.ofHash hash) 1 committee.aggregatePubkey
  show (hashTreeRootAtM (Hasher.ofHash hash) 3 (.container ["pubkeys", "aggregate_pubkey"]
    [.vector (.byteVector 48) preset.SYNC_COMMITTEE_SIZE.toNat, .byteVector 48])
    (.seq [.seq (committee.pubkeys.toList.map SszType.toValue),
      .bytes committee.aggregatePubkey.toArray])).run = _
  unfold hashTreeRootAtM
  simp only [merkleLayout, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, liftM_pure, pure_bind, List.zip_cons_cons, List.zip_nil_left,
    List.map_cons, List.map_nil, MerkleLayout.nesting, layoutChunksAtM_eq, Leaves.count,
    Option.getD_none, List.drop_zero, Nat.sub_zero, List.take_succ_cons, List.take_zero,
    List.mapM_cons, List.mapM_nil]
  simp only [ExceptT.run_bind, bind_assoc, aggregate, pure_bind]
  refine bind_congr fun keys => ?_
  cases keys
  · simp
  · simp only [hashLayoutChunksM, hashLayoutFromM, merkleizeBoundedUncheckedM,
      merkleizeBoundedFromM, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte, bind_pure,
      ExceptT.run_lift,
      show depthFor 2 = 1 from depthFor_pow 1]
    simp [subtreeAtM_unfold, combineM_eq, padded, Hasher.ofHash]
    rfl

/-- Two equal replayed roots of sync committees come from equal committees, or the cache collides.

The chase runs from the root down, through the roots of the keys and of the aggregate key. -/
private theorem collision_or_eq_of_hashTreeRootM_syncCommittee {cache : HashOracle.QueryCache}
    {first second : SyncCommittee preset} {root : Bytes}
    (hfirst : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (SszType.desc (SyncCommittee preset)) (SszType.toValue first)).run = some (.ok root))
    (hsecond : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (SszType.desc (SyncCommittee preset)) (SszType.toValue second)).run = some (.ok root)) :
    Collision cache ∨ first = second := by
  obtain ⟨keys₁, aggregate₁⟩ := first
  obtain ⟨keys₂, aggregate₂⟩ := second
  rw [hashTreeRootM_syncCommittee] at hfirst hsecond
  simp only [simulateQ_bind] at hfirst hsecond
  obtain ⟨keysRoot₁, hkeys₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨keysRoot₂, hkeys₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  cases keysRoot₁ with
  | error => simp at hfirst
  | ok node₁ =>
  cases keysRoot₂ with
  | error => simp at hsecond
  | ok node₂ =>
  simp only [simulateQ_bind, simulateQ_pure] at hfirst hsecond
  obtain ⟨digest₁, hdigest₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨top₁, htop₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨digest₂, hdigest₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨top₂, htop₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  -- Each step: one answer of two hashes gives one message, or a collision of the cache.
  refine (collision_or_eq_of_queryHash htop₁ htop₂
    (Except.ok.inj (Option.some.inj (hfirst.trans hsecond.symm)))).elim .inl fun top => ?_
  obtain ⟨rfl, sameAggregate⟩ := Array.append_inj' top
    ((size_of_queryHash hdigest₁).trans (size_of_queryHash hdigest₂).symm)
  refine (collision_or_eq_of_queryHash hdigest₁ hdigest₂ sameAggregate).elim .inl fun key => ?_
  refine (collision_or_eq_of_hashTreeRootM_bytes48Vector (by simp) (by simp) hkeys₁
    hkeys₂).elim .inl fun keys => .inr ?_
  simp only [SyncCommittee.mk.injEq]
  exact ⟨Vector.toList_inj.mp keys, Vector.toArray_inj.mp ((Array.append_left_inj _).mp key)⟩

/-- A replayed winning committee extraction exposes a collision of the cache.

Two different committees with one root collide below that root.

Two different roots that climb to one state root give the collision of the two climbs. -/
theorem collision_of_extractSyncCommittees {gindex : Nat} {cache : HashOracle.QueryCache}
    {claim : SyncCommitteeClaim preset} {outcome : SyncCommitteeOutcome preset}
    (hrun : simulateQ cache.toPartialImpl (extractSyncCommittees queryHash preset gindex claim) =
      some outcome)
    (hwins : SyncCommitteeWins gindex outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  simp only [extractSyncCommittees, simulateQ_bind] at hrun
  obtain ⟨firstRoot, hfirst, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨secondRoot, hsecond, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨climbs, hclimbs, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [simulateQ_pure] at hrun
  cases hrun
  obtain ⟨differ, firstLong, secondLong, -, -, climbed, present, firstClimbed, secondClimbed⟩ :=
    hwins
  dsimp only at differ firstLong secondLong present firstClimbed secondClimbed
  subst present
  split at hclimbs
  · rename_i index firstLeaf secondLeaf _ hfirstLeaf hsecondLeaf
    simp only [simulateQ_bind, simulateQ_pure] at hclimbs
    obtain ⟨_, hbranches, hclimbs⟩ := Option.bind_eq_some_iff.mp hclimbs
    cases hclimbs
    by_cases sameLeaf : firstLeaf = secondLeaf
    · -- One root of two different committees, so the chase down both roots finds a collision.
      subst sameLeaf
      rw [eq_ok_of_bind_toChunk hfirstLeaf] at hfirst
      rw [eq_ok_of_bind_toChunk hsecondLeaf] at hsecond
      exact (collision_or_eq_of_hashTreeRootM_syncCommittee hfirst hsecond).elim id
        fun same => absurd same differ
    · -- Two different roots climb to one state root, so the climbs collide.
      have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hbranches
      simp only [extractBranches, evalWithAnswerFn_bind, evalWithAnswerFn_climbBranchM,
        evalWithAnswerFn_pure] at hout
      subst hout
      exact collision_of_extractBranches hbranches ⟨sameLeaf, by simp; omega, by simp; omega, _,
        firstClimbed, secondClimbed⟩
  · simp only [simulateQ_pure] at hclimbs
    cases hclimbs

/-- The root of a sync committee makes at most `size + width + 1` oracle calls.

The tree of the keys has `width` leaves, the least power of two at least `size`. -/
private theorem hashTreeRootM_syncCommittee_queryBound (committee : SyncCommittee preset) :
    IsQueryBoundP (hashTreeRootM (Hasher.ofHash queryHash) (SszType.desc (SyncCommittee preset))
      (SszType.toValue committee)).run (fun _ => True)
      (preset.SYNC_COMMITTEE_SIZE.toNat + 2 ^ depthFor preset.SYNC_COMMITTEE_SIZE.toNat + 1) := by
  rw [hashTreeRootM_syncCommittee]
  have tree := Nat.one_le_two_pow (n := depthFor preset.SYNC_COMMITTEE_SIZE.toNat)
  refine (isQueryBoundP_bind (m := 2) (hashTreeRootM_bytes48Vector_queryBound (by simp))
    fun keys _ => ?_).mono (by omega)
  cases keys
  · exact isQueryBoundP_pure _ _ _
  · simp [queryHash]

/-- The extraction makes at most `2 * (size + width + 1) + 2 * depth` oracle calls.

A committee has `size` keys in a tree of `width` leaves, and `depth` is the depth of the index. -/
theorem extractSyncCommittees_queryBound (preset : Preset) (gindex : Nat)
    (claim : SyncCommitteeClaim preset) :
    IsQueryBoundP (extractSyncCommittees queryHash preset gindex claim) (fun _ => True)
      (2 * (preset.SYNC_COMMITTEE_SIZE.toNat + 2 ^ depthFor preset.SYNC_COMMITTEE_SIZE.toNat + 1) +
        2 * Nat.log2 gindex) := by
  unfold extractSyncCommittees
  refine (isQueryBoundP_bind (hashTreeRootM_syncCommittee_queryBound _) fun _ _ =>
    isQueryBoundP_bind (hashTreeRootM_syncCommittee_queryBound _) fun _ _ =>
      isQueryBoundP_bind (n := 2 * Nat.log2 gindex) (m := 0) ?_
        fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)
  split
  · exact (isQueryBoundP_bind (extractBranches_queryBound _ _) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by omega)
  · exact isQueryBoundP_pure _ _ _

/-- The experiment makes at most `q + 2 * (size + width + 1) + 2 * depth` oracle calls.

It needs the adversary to make at most `q` oracle calls. -/
theorem experimentWith_extractSyncCommittees_queryBound (preset : Preset) (gindex : Nat)
    {adversary : OracleComp (unifSpec + HashOracle) (SyncCommitteeClaim preset)}
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    IsQueryBoundP (experimentWith (extractSyncCommittees queryHash preset gindex) adversary)
      (fun t => t.isRight = true) (q + 2 * (preset.SYNC_COMMITTEE_SIZE.toNat +
        2 ^ depthFor preset.SYNC_COMMITTEE_SIZE.toNat + 1) + 2 * Nat.log2 gindex) :=
  (experimentWith_queryBound hq (extractSyncCommittees_queryBound preset gindex)).mono
    (by omega)

/-- An adversary that outputs two sync committees wins with probability at most `Q^2 / N`.

A win is two different committees whose branches, past zero front nodes, climb to the root.

`Q` bounds the oracle calls of the whole experiment, repeats included, and `N` counts digests.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_syncCommitteeWins_le [SampleableType Hash32] (preset : Preset) (gindex : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) (SyncCommitteeClaim preset)) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractSyncCommittees queryHash preset gindex) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractSyncCommittees queryHash preset gindex) adversary)).run ∅}[
        SyncCommitteeWins gindex z.1] ≤ Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  prEvent_experimentWith_le (extractSyncCommittees queryHash preset gindex)
    (SyncCommitteeWins gindex) collision_of_extractSyncCommittees adversary hQ

/-- The same bound for an adversary of `q` oracle calls and 32 uniform bytes per answer.

A win has probability at most `Q^2 / 2^256`, with `Q = q + 2 * (size + width + 1) + 2 * depth`.

It needs the adversary to make at most `q` oracle calls. -/
theorem prEvent_syncCommitteeWins_le_of_adversary (preset : Preset) (gindex : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) (SyncCommitteeClaim preset))
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractSyncCommittees queryHash preset gindex) adversary)).run ∅}[
        SyncCommitteeWins gindex z.1] ≤
      (q + 2 * (preset.SYNC_COMMITTEE_SIZE.toNat +
        2 ^ depthFor preset.SYNC_COMMITTEE_SIZE.toNat + 1) + 2 * Nat.log2 gindex : Nat) *
        (((q + 2 * (preset.SYNC_COMMITTEE_SIZE.toNat +
          2 ^ depthFor preset.SYNC_COMMITTEE_SIZE.toNat + 1) + 2 * Nat.log2 gindex : Nat) :
            ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_syncCommitteeWins_le preset gindex adversary
    (experimentWith_extractSyncCommittees_queryBound preset gindex hq)
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- At mainnet, a win has probability at most `(q + 2050 + 2 * depth)^2 / 2^256`.

There a committee has 512 members, and `depth` is the base-2 logarithm of the index.

It needs the adversary to make at most `q` oracle calls. -/
theorem prEvent_syncCommitteeWins_le_mainnet (gindex : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) (SyncCommitteeClaim .mainnet))
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractSyncCommittees queryHash .mainnet gindex) adversary)).run ∅}[
        SyncCommitteeWins gindex z.1] ≤
      (q + 2050 + 2 * Nat.log2 gindex : Nat) *
        (((q + 2050 + 2 * Nat.log2 gindex : Nat) : ℝ≥0∞) / 2 ^ 256) := by
  have count : 2 * (Preset.mainnet.SYNC_COMMITTEE_SIZE.toNat +
      2 ^ depthFor Preset.mainnet.SYNC_COMMITTEE_SIZE.toNat + 1) = 2050 := by
    rw [show Preset.mainnet.SYNC_COMMITTEE_SIZE.toNat = 2 ^ 9 from rfl, depthFor_pow]
    rfl
  have bound := prEvent_syncCommitteeWins_le_of_adversary .mainnet gindex adversary hq
  rw [count] at bound
  exact bound

/-- With SHA-256, the extraction roots each committee and reads the index as the spec does.

It needs a committee of at least one member. -/
theorem extractSyncCommittees_sha256 [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] (gindex : Nat)
    (claim : SyncCommitteeClaim preset) :
    (extractSyncCommittees (m := Id) Cryptography.Hash.Sha256.hash preset gindex claim).run =
      ⟨claim, match getSubtreeIndex gindex, SszType.hashTreeRoot claim.first,
          SszType.hashTreeRoot claim.second with
        | .ok index, .ok firstLeaf, .ok secondLeaf =>
          some (extractBranches (m := Id) Cryptography.Hash.Sha256.hash (Nat.log2 gindex)
            ⟨index, firstLeaf, claim.firstBranch.drop (claim.firstBranch.length - Nat.log2 gindex),
              secondLeaf,
              claim.secondBranch.drop (claim.secondBranch.length - Nat.log2 gindex)⟩).run
        | _, _, _ => none⟩ := by
  simp only [extractSyncCommittees, ofHash_sha256, SszType.hashTreeRoot_eq]
  rfl

/-- With SHA-256 as the node hash, a win is two different committees that the branch check accepts.

The step from SHA-256 to the oracle is the idealisation of the model, not a theorem.

It needs a committee of at least one member, and holds at every index. -/
theorem syncCommitteeWins_sha256_iff [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] {gindex : Nat}
    {claim : SyncCommitteeClaim preset} :
    SyncCommitteeWins gindex
        (extractSyncCommittees (m := Id) Cryptography.Hash.Sha256.hash preset gindex claim).run ↔
      claim.first ≠ claim.second ∧ ∃ firstLeaf secondLeaf,
        SszType.hashTreeRoot claim.first = .ok firstLeaf ∧
        SszType.hashTreeRoot claim.second = .ok secondLeaf ∧
        isValidNormalizedMerkleBranch firstLeaf claim.firstBranch gindex claim.root = .ok true ∧
        isValidNormalizedMerkleBranch secondLeaf claim.secondBranch gindex claim.root =
          .ok true := by
  rw [extractSyncCommittees_sha256]
  simp only [SyncCommitteeWins]
  refine and_congr_right fun _ => ?_
  -- The climbs keep every node after the front, since that rest has at most the depth.
  have whole : ∀ branch : List Bytes32,
      (branch.drop (branch.length - Nat.log2 gindex)).take (Nat.log2 gindex) =
        branch.drop (branch.length - Nat.log2 gindex) :=
    fun _ => List.take_of_length_le (by simp only [List.length_drop]; omega)
  have long : ∀ length : Nat, length - (length - Nat.log2 gindex) = Nat.log2 gindex ↔
      Nat.log2 gindex ≤ length := fun _ => by omega
  by_cases zero : gindex = 0
  · subst zero
    simp [getSubtreeIndex, gindexDepth, isValidNormalizedMerkleBranch, bind, Except.bind]
  · have depthIs : gindexDepth gindex = .ok (Nat.log2 gindex) := by
      simp [gindexDepth]
      omega
    cases first : SszType.hashTreeRoot claim.first <;>
      cases second : SszType.hashTreeRoot claim.second <;>
      simp [getSubtreeIndex, depthIs, isValidNormalizedMerkleBranch, bind, Except.bind, pure,
        Except.pure, extractBranches_sha256, whole, isValidMerkleBranch_eq_true_iff,
        toChunk_ok_iff, long]
    exact ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨⟨c, a, e⟩, d, b, f⟩,
      fun ⟨⟨c, a, e⟩, d, b, f⟩ => ⟨a, b, c, d, e, f⟩⟩

/-- Two accepted bootstraps with one state root and slot, and different committees, win.

The node hash is SHA-256, at the index of the current committee at that slot.

It needs a committee of at least one member. -/
theorem syncCommitteeWins_of_initializeLightClientStore [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    {fork : Fork} {config : Config} {firstTrusted secondTrusted : Root}
    {first second : LightClientBootstrap preset fork}
    {firstStore secondStore : LightClientStore preset fork}
    (firstAccepted : initializeLightClientStore config firstTrusted first = .ok firstStore)
    (secondAccepted : initializeLightClientStore config secondTrusted second = .ok secondStore)
    (sameRoot : first.header.beacon.stateRoot = second.header.beacon.stateRoot)
    (sameSlot : first.header.beacon.slot = second.header.beacon.slot)
    (differ : first.currentSyncCommittee ≠ second.currentSyncCommittee) :
    ∃ gindex, currentSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
        first.header.beacon.slot = .ok gindex ∧
      SyncCommitteeWins gindex (extractSyncCommittees (m := Id) Cryptography.Hash.Sha256.hash
        preset gindex ⟨first.header.beacon.stateRoot, first.currentSyncCommittee,
          first.currentSyncCommitteeBranch.toList, second.currentSyncCommittee,
          second.currentSyncCommitteeBranch.toList⟩).run := by
  obtain ⟨-, -, gindex, firstLeaf, indexed, firstRooted, firstValid⟩ :=
    initializeLightClientStore_proves firstAccepted
  obtain ⟨-, -, other, secondLeaf, otherIndexed, secondRooted, secondValid⟩ :=
    initializeLightClientStore_proves secondAccepted
  rw [← sameSlot, indexed, Except.ok.injEq] at otherIndexed
  subst otherIndexed
  rw [← sameRoot] at secondValid
  exact ⟨gindex, indexed, syncCommitteeWins_sha256_iff.mpr ⟨differ, firstLeaf, secondLeaf,
    firstRooted, secondRooted, firstValid, secondValid⟩⟩

/-- Two updates with one attested state root and slot, and different next committees, win.

It needs both to pass the check of the next committee.

The node hash is SHA-256, at the index of the next committee at that slot.

It needs a committee of at least one member. -/
theorem syncCommitteeWins_of_validateNextSyncCommitteeBranch
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] {fork : Fork} {config : Config}
    {first second : LightClientUpdate preset fork}
    (firstAccepted : validateNextSyncCommitteeBranch config first = .ok ())
    (secondAccepted : validateNextSyncCommitteeBranch config second = .ok ())
    (sameRoot : first.attestedHeader.beacon.stateRoot = second.attestedHeader.beacon.stateRoot)
    (sameSlot : first.attestedHeader.beacon.slot = second.attestedHeader.beacon.slot)
    (differ : first.nextSyncCommittee ≠ second.nextSyncCommittee) :
    ∃ gindex, nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
        first.attestedHeader.beacon.slot = .ok gindex ∧
      SyncCommitteeWins gindex (extractSyncCommittees (m := Id) Cryptography.Hash.Sha256.hash
        preset gindex ⟨first.attestedHeader.beacon.stateRoot, first.nextSyncCommittee,
          first.nextSyncCommitteeBranch.toList, second.nextSyncCommittee,
          second.nextSyncCommitteeBranch.toList⟩).run := by
  obtain ⟨gindex, firstLeaf, indexed, firstRooted, firstValid⟩ :=
    validateNextSyncCommitteeBranch_proves firstAccepted
  obtain ⟨other, secondLeaf, otherIndexed, secondRooted, secondValid⟩ :=
    validateNextSyncCommitteeBranch_proves secondAccepted
  rw [← sameSlot, indexed, Except.ok.injEq] at otherIndexed
  subst otherIndexed
  rw [← sameRoot] at secondValid
  exact ⟨gindex, indexed, syncCommitteeWins_sha256_iff.mpr ⟨differ, firstLeaf, secondLeaf,
    firstRooted, secondRooted, firstValid, secondValid⟩⟩

end EthLib.Consensus

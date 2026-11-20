module

public import EthLib.Consensus.LightClient.Sync
public import EthLib.Serialization.Proofs.Ssz.BranchRandomOracle
import EthLib.Consensus.Proofs.Containers.Misc
import EthLib.Consensus.Proofs.LightClient.Authenticate

/-!
# Proofs: two finalized headers of one state root in the random oracle model

An update proves its finalized header by a branch against the attested state root.

The leaf of the branch is the root of the beacon header, or zero bytes at the genesis slot.

An adversary outputs a state root and two beacon headers with a branch each.

The generalized index of the branches is fixed before the run.

The experiment reads both leaves as the check does, and climbs both branches.

Every hash of the experiment is an oracle call.

The adversary wins with two different headers, if both branches pass the check at that index.

A header at the genesis slot has the zero leaf, so such a win also needs two different leaves.

Each win exposes two different queried inputs with one answer, so the birthday bound applies.

The count grows with the depth of the index alone.

An adversary of `q` calls gives a bound of `(q + 14 + 2 * depth)^2 / 2^256`.

The depth of the index is 6 before Electra, 7 from Electra and 9 from Gloas.

With SHA-256 as the node hash, a win is two different headers whose branches the check accepts.

Two updates that prove finality and pass the finality check give a win with SHA-256.

That result needs one attested state root and slot, and two different finalized headers.

It also needs the root of neither finalized header to be zero bytes.

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

/-- What the adversary outputs: one state root, and two finalized headers with a branch each. -/
structure FinalityClaim where
  /-- The state root that both branches must reach. -/
  root : Root
  /-- The first finalized header. -/
  first : BeaconBlockHeader
  /-- The nodes of the branch of the first header, from its leaf up. -/
  firstBranch : List Bytes32
  /-- The second finalized header. -/
  second : BeaconBlockHeader
  /-- The nodes of the branch of the second header, from its leaf up. -/
  secondBranch : List Bytes32

/-- What the finality experiment reports: the claim, and the climbs of both branches.

The climbs are absent when the index names no node, or a leaf cannot be read. -/
structure FinalityOutcome where
  /-- The state root, the two headers and their branches. -/
  claim : FinalityClaim
  /-- The subtree index, the two leaves, the climbed nodes and their roots. -/
  climbs : Option BranchOutcome

/-- The leaf of a finalized header as the finality check reads it, with a node hash in any monad.

It is zero bytes at the genesis slot, and the root of the header at any later slot. -/
def finalizedLeafM {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray)
    (header : BeaconBlockHeader) : m (Except Err Bytes) :=
  if header.slot = GENESIS_SLOT then pure (.ok zeroBytes32.toArray)
  else (hashTreeRootM (Hasher.ofHash hash) (SszType.desc BeaconBlockHeader)
    (SszType.toValue header)).run

/-- The extraction for finalized headers, with a node hash in any monad.

It reads both leaves, then climbs the last nodes of each branch, as many as the depth.

The depth is the base-2 logarithm of the index, as in the check of a normalized branch. -/
def extractFinality {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray)
    (gindex : Nat) (claim : FinalityClaim) : m FinalityOutcome := do
  let firstRoot ← finalizedLeafM hash claim.first
  let secondRoot ← finalizedLeafM hash claim.second
  let climbs ← (match getSubtreeIndex gindex, firstRoot >>= toChunk, secondRoot >>= toChunk with
    | .ok index, .ok firstLeaf, .ok secondLeaf => do
      let climbs ← extractBranches hash (Nat.log2 gindex)
        ⟨index, firstLeaf, claim.firstBranch.drop (claim.firstBranch.length - Nat.log2 gindex),
          secondLeaf, claim.secondBranch.drop (claim.secondBranch.length - Nat.log2 gindex)⟩
      pure (some climbs)
    | _, _, _ => pure none)
  return ⟨claim, climbs⟩

/-- The adversary wins: two different headers whose branches climb to the claimed state root.

Each branch needs at least as many nodes as the depth, and zero nodes in front of that many.

The two leaves must differ, unless neither header is at the genesis slot. -/
def FinalityWins (gindex : Nat) (outcome : FinalityOutcome) : Prop :=
  outcome.claim.first ≠ outcome.claim.second ∧
    Nat.log2 gindex ≤ outcome.claim.firstBranch.length ∧
    Nat.log2 gindex ≤ outcome.claim.secondBranch.length ∧
    (∀ node ∈ outcome.claim.firstBranch.take
      (outcome.claim.firstBranch.length - Nat.log2 gindex), node = Vector.replicate 32 0) ∧
    (∀ node ∈ outcome.claim.secondBranch.take
      (outcome.claim.secondBranch.length - Nat.log2 gindex), node = Vector.replicate 32 0) ∧
    ∃ climbs, outcome.climbs = some climbs ∧
      (climbs.claim.firstLeaf ≠ climbs.claim.secondLeaf ∨
        outcome.claim.first.slot ≠ GENESIS_SLOT ∧ outcome.claim.second.slot ≠ GENESIS_SLOT) ∧
      climbs.firstRoot = .ok outcome.claim.root ∧ climbs.secondRoot = .ok outcome.claim.root

/-- The root of a beacon block header is seven hashes.

The slot and the proposer index are their 8 bytes and 24 zero bytes, and share one hash.

The parent and state roots share one hash, and the body root takes one with a zero node.

One hash joins two zero nodes, and three more join those four digests.

It holds for a hash in any lawful monad. -/
theorem hashTreeRootM_beaconBlockHeader {m : Type → Type} [Monad m] [LawfulMonad m]
    (hash : ByteArray → m ByteArray) (header : BeaconBlockHeader) :
    (hashTreeRootM (Hasher.ofHash hash) (SszType.desc BeaconBlockHeader)
      (SszType.toValue header)).run = (do
      let indices ← hash ⟨uintBytes 8 header.slot.toNat ++ Array.replicate 24 0 ++
        (uintBytes 8 header.proposerIndex.toNat ++ Array.replicate 24 0)⟩
      let roots ← hash ⟨header.parentRoot.toArray ++ header.stateRoot.toArray⟩
      let left ← hash ⟨indices.data ++ roots.data⟩
      let body ← hash ⟨header.bodyRoot.toArray ++ zeroChunk⟩
      let zero ← hash ⟨zeroChunk ++ zeroChunk⟩
      let right ← hash ⟨body.data ++ zero.data⟩
      let root ← hash ⟨left.data ++ right.data⟩
      return .ok root.data) := by
  -- The roots of the five fields, each stated for its SSZ shape.
  have slot : (hashTreeRootAtM (Hasher.ofHash hash) 1 (.uint 8)
      (.uint header.slot.toNat)).run = _ :=
    hashTreeRootM_uint64 (Hasher.ofHash hash) header.slot
  have proposer : (hashTreeRootAtM (Hasher.ofHash hash) 1 (.uint 8)
      (.uint header.proposerIndex.toNat)).run = _ :=
    hashTreeRootM_uint64 (Hasher.ofHash hash) header.proposerIndex
  have parent : (hashTreeRootAtM (Hasher.ofHash hash) 1 (.byteVector 32)
      (.bytes header.parentRoot.toArray)).run = _ :=
    hashTreeRootM_bytes32 (Hasher.ofHash hash) header.parentRoot
  have state : (hashTreeRootAtM (Hasher.ofHash hash) 1 (.byteVector 32)
      (.bytes header.stateRoot.toArray)).run = _ :=
    hashTreeRootM_bytes32 (Hasher.ofHash hash) header.stateRoot
  have body : (hashTreeRootAtM (Hasher.ofHash hash) 1 (.byteVector 32)
      (.bytes header.bodyRoot.toArray)).run = _ :=
    hashTreeRootM_bytes32 (Hasher.ofHash hash) header.bodyRoot
  show (hashTreeRootAtM (Hasher.ofHash hash) 2 (.container ["slot", "proposer_index",
    "parent_root", "state_root", "body_root"] [.uint 8, .uint 8, .byteVector 32, .byteVector 32,
    .byteVector 32]) (.seq [.uint header.slot.toNat, .uint header.proposerIndex.toNat,
      .bytes header.parentRoot.toArray, .bytes header.stateRoot.toArray,
      .bytes header.bodyRoot.toArray])).run = _
  unfold hashTreeRootAtM
  simp only [merkleLayout, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, liftM_pure, pure_bind, List.zip_cons_cons, List.zip_nil_left,
    List.map_cons, List.map_nil, MerkleLayout.nesting, layoutChunksAtM_eq, Leaves.count,
    Option.getD_none, List.drop_zero, Nat.sub_zero, List.take_succ_cons, List.take_zero,
    List.mapM_cons, List.mapM_nil]
  simp only [ExceptT.run_bind, bind_assoc, slot, proposer, parent, state, body, pure_bind]
  simp only [hashLayoutChunksM, hashLayoutFromM, merkleizeBoundedUncheckedM,
    merkleizeBoundedFromM, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte, bind_pure,
    ExceptT.run_lift,
    show depthFor 5 = 3 by simp [depthFor]]
  simp [subtreeAtM_unfold, combineM_eq, padded, Hasher.ofHash, zeroRootM]
  rfl

/-- Two equal replayed roots of beacon headers come from equal headers, or the cache collides.

The chase runs from the root down, since two hashes with one answer have one message or collide. -/
private theorem collision_or_eq_of_hashTreeRootM_beaconBlockHeader
    {cache : HashOracle.QueryCache} {first second : BeaconBlockHeader} {root : Except Err Bytes}
    (hfirst : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (SszType.desc BeaconBlockHeader) (SszType.toValue first)).run = some root)
    (hsecond : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (SszType.desc BeaconBlockHeader) (SszType.toValue second)).run = some root) :
    Collision cache ∨ first = second := by
  obtain ⟨slot₁, proposer₁, parent₁, state₁, body₁⟩ := first
  obtain ⟨slot₂, proposer₂, parent₂, state₂, body₂⟩ := second
  rw [hashTreeRootM_beaconBlockHeader] at hfirst hsecond
  simp only [simulateQ_bind, simulateQ_pure] at hfirst hsecond
  obtain ⟨indices₁, hindices₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨roots₁, hroots₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨left₁, hleft₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨bodyRoot₁, hbody₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨zero₁, -, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨right₁, hright₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨top₁, htop₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨indices₂, hindices₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨roots₂, hroots₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨left₂, hleft₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨bodyRoot₂, hbody₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨zero₂, -, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨right₂, hright₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨top₂, htop₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  -- Each step: one answer of two hashes gives one message, or a collision of the cache.
  refine (collision_or_eq_of_queryHash htop₁ htop₂
    (Except.ok.inj (Option.some.inj (hfirst.trans hsecond.symm)))).elim .inl fun top => ?_
  obtain ⟨sameLeft, sameRight⟩ := Array.append_inj top
    ((size_of_queryHash hleft₁).trans (size_of_queryHash hleft₂).symm)
  refine (collision_or_eq_of_queryHash hleft₁ hleft₂ sameLeft).elim .inl fun left => ?_
  obtain ⟨sameIndices, sameRoots⟩ := Array.append_inj left
    ((size_of_queryHash hindices₁).trans (size_of_queryHash hindices₂).symm)
  refine (collision_or_eq_of_queryHash hindices₁ hindices₂ sameIndices).elim .inl
    fun indices => ?_
  refine (collision_or_eq_of_queryHash hroots₁ hroots₂ sameRoots).elim .inl fun roots => ?_
  refine (collision_or_eq_of_queryHash hright₁ hright₂ sameRight).elim .inl fun right => ?_
  obtain ⟨sameBody, -⟩ := Array.append_inj right
    ((size_of_queryHash hbody₁).trans (size_of_queryHash hbody₂).symm)
  refine (collision_or_eq_of_queryHash hbody₁ hbody₂ sameBody).elim .inl fun body => ?_
  -- No step collides, so every field of the two headers is equal.
  refine .inr ?_
  obtain ⟨sameSlot, sameProposer⟩ := Array.append_inj indices (by simp [uintBytes_size])
  obtain ⟨sameParent, sameState⟩ := Array.append_inj roots (by simp)
  have slots := uintBytes_injective (by simpa using slot₁.toNat_lt)
    (by simpa using slot₂.toNat_lt) ((Array.append_left_inj _).mp sameSlot)
  have proposers := uintBytes_injective (by simpa using proposer₁.toNat_lt)
    (by simpa using proposer₂.toNat_lt) ((Array.append_left_inj _).mp sameProposer)
  simp only [BeaconBlockHeader.mk.injEq]
  exact ⟨UInt64.toNat_inj.mp slots, UInt64.toNat_inj.mp proposers,
    Vector.toArray_inj.mp sameParent, Vector.toArray_inj.mp sameState,
    Vector.toArray_inj.mp ((Array.append_left_inj _).mp body)⟩

/-- A replayed winning finality extraction exposes a collision of the cache.

Two different leaves that climb to one state root give the collision of the two climbs.

One leaf for two different headers comes from two roots, which collide below that leaf. -/
theorem collision_of_extractFinality {gindex : Nat} {cache : HashOracle.QueryCache}
    {claim : FinalityClaim} {outcome : FinalityOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractFinality queryHash gindex claim) =
      some outcome)
    (hwins : FinalityWins gindex outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  simp only [extractFinality, simulateQ_bind] at hrun
  obtain ⟨firstRoot, hfirst, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨secondRoot, hsecond, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨climbs, hclimbs, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [simulateQ_pure] at hrun
  cases hrun
  obtain ⟨differ, firstLong, secondLong, -, -, climbed, present, leaves, firstClimbed,
    secondClimbed⟩ := hwins
  dsimp only at differ firstLong secondLong present leaves firstClimbed secondClimbed
  subst present
  split at hclimbs
  · rename_i index firstLeaf secondLeaf _ hfirstLeaf hsecondLeaf
    simp only [simulateQ_bind, simulateQ_pure] at hclimbs
    obtain ⟨_, hbranches, hclimbs⟩ := Option.bind_eq_some_iff.mp hclimbs
    cases hclimbs
    -- The replayed climbs start from the two leaves that the extraction read.
    have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hbranches
    simp only [extractBranches, evalWithAnswerFn_bind, evalWithAnswerFn_climbBranchM,
      evalWithAnswerFn_pure] at hout
    subst hout
    by_cases sameLeaf : firstLeaf = secondLeaf
    · -- One leaf, so neither header is at the genesis slot, and the leaf roots both headers.
      subst sameLeaf
      obtain ⟨firstLater, secondLater⟩ := leaves.resolve_left (not_not.mpr rfl)
      rw [eq_ok_of_bind_toChunk hfirstLeaf] at hfirst
      rw [eq_ok_of_bind_toChunk hsecondLeaf] at hsecond
      unfold finalizedLeafM at hfirst hsecond
      rw [ite_eq_right firstLater] at hfirst
      rw [ite_eq_right secondLater] at hsecond
      exact (collision_or_eq_of_hashTreeRootM_beaconBlockHeader hfirst hsecond).elim id
        fun same => absurd same differ
    · -- Two different leaves climb to one state root, so the climbs collide.
      exact collision_of_extractBranches hbranches ⟨sameLeaf, by simp; omega, by simp; omega, _,
        firstClimbed, secondClimbed⟩
  · simp only [simulateQ_pure] at hclimbs
    cases hclimbs

/-- The leaf of a finalized header makes at most seven oracle calls, and none at genesis. -/
private theorem finalizedLeafM_queryBound (header : BeaconBlockHeader) :
    IsQueryBoundP (finalizedLeafM queryHash header) (fun _ => True) 7 := by
  unfold finalizedLeafM
  split
  · exact isQueryBoundP_pure _ _ _
  · rw [hashTreeRootM_beaconBlockHeader]
    simp [queryHash]

/-- The extraction makes at most `14 + 2 * depth` oracle calls, where `depth` is that of the index.

Each leaf takes at most seven calls, and each climb one call per climbed node. -/
theorem extractFinality_queryBound (gindex : Nat) (claim : FinalityClaim) :
    IsQueryBoundP (extractFinality queryHash gindex claim) (fun _ => True)
      (14 + 2 * Nat.log2 gindex) := by
  unfold extractFinality
  refine (isQueryBoundP_bind (finalizedLeafM_queryBound _) fun _ _ =>
    isQueryBoundP_bind (finalizedLeafM_queryBound _) fun _ _ =>
      isQueryBoundP_bind (n := 2 * Nat.log2 gindex) (m := 0) ?_
        fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)
  split
  · exact (isQueryBoundP_bind (extractBranches_queryBound _ _) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by omega)
  · exact isQueryBoundP_pure _ _ _

/-- The experiment makes at most `q + 14 + 2 * depth` oracle calls.

It needs the adversary to make at most `q` oracle calls. -/
theorem experimentWith_extractFinality_queryBound (gindex : Nat)
    {adversary : OracleComp (unifSpec + HashOracle) FinalityClaim} {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    IsQueryBoundP (experimentWith (extractFinality queryHash gindex) adversary)
      (fun t => t.isRight = true) (q + 14 + 2 * Nat.log2 gindex) :=
  (experimentWith_queryBound hq (extractFinality_queryBound gindex)).mono (by omega)

/-- An adversary that outputs two finalized headers wins with probability at most `Q^2 / N`.

A win is two different headers whose branches, past zero front nodes, climb to the root.

The leaves must also differ, when a header is at the genesis slot.

`Q` bounds the oracle calls of the whole experiment, repeats included, and `N` counts digests.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_finalityWins_le [SampleableType Hash32] (gindex : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) FinalityClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractFinality queryHash gindex) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractFinality queryHash gindex) adversary)).run ∅}[
        FinalityWins gindex z.1] ≤ Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  prEvent_experimentWith_le (extractFinality queryHash gindex) (FinalityWins gindex)
    collision_of_extractFinality adversary hQ

/-- The same bound for an adversary of `q` oracle calls and 32 uniform bytes per answer.

A win has probability at most `(q + 14 + 2 * depth)^2 / 2^256`.

It needs the adversary to make at most `q` oracle calls. -/
theorem prEvent_finalityWins_le_of_adversary (gindex : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) FinalityClaim) {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractFinality queryHash gindex) adversary)).run ∅}[
        FinalityWins gindex z.1] ≤
      (q + 14 + 2 * Nat.log2 gindex : Nat) *
        (((q + 14 + 2 * Nat.log2 gindex : Nat) : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_finalityWins_le gindex adversary
    (experimentWith_extractFinality_queryBound gindex hq)
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- With SHA-256, the extraction reads each leaf and the index as the finality check does. -/
theorem extractFinality_sha256 (gindex : Nat) (claim : FinalityClaim) :
    (extractFinality (m := Id) Cryptography.Hash.Sha256.hash gindex claim).run =
      ⟨claim, match getSubtreeIndex gindex,
          (if claim.first.slot = GENESIS_SLOT then .ok zeroBytes32
            else SszType.hashTreeRoot claim.first),
          (if claim.second.slot = GENESIS_SLOT then .ok zeroBytes32
            else SszType.hashTreeRoot claim.second) with
        | .ok index, .ok firstLeaf, .ok secondLeaf =>
          some (extractBranches (m := Id) Cryptography.Hash.Sha256.hash (Nat.log2 gindex)
            ⟨index, firstLeaf, claim.firstBranch.drop (claim.firstBranch.length - Nat.log2 gindex),
              secondLeaf,
              claim.secondBranch.drop (claim.secondBranch.length - Nat.log2 gindex)⟩).run
        | _, _, _ => none⟩ := by
  have read : ∀ header : BeaconBlockHeader,
      (finalizedLeafM (m := Id) Cryptography.Hash.Sha256.hash header).run >>= toChunk =
        if header.slot = GENESIS_SLOT then .ok zeroBytes32 else SszType.hashTreeRoot header := by
    intro header
    unfold finalizedLeafM
    split
    · show toChunk zeroBytes32.toArray = .ok zeroBytes32
      exact toChunk_ok_iff.mpr rfl
    · simp only [ofHash_sha256, SszType.hashTreeRoot_eq]
      rfl
  simp only [extractFinality, ← read]
  rfl

/-- With SHA-256 as the node hash, a win is two different headers whose branches the check accepts.

Each leaf is read as the check reads it, zero bytes at the genesis slot and the root otherwise.

The two leaves must differ, unless neither header is at the genesis slot.

The step from SHA-256 to the oracle is the idealisation of the model, not a theorem. -/
theorem finalityWins_sha256_iff {gindex : Nat} {claim : FinalityClaim} :
    FinalityWins gindex
        (extractFinality (m := Id) Cryptography.Hash.Sha256.hash gindex claim).run ↔
      claim.first ≠ claim.second ∧ ∃ firstLeaf secondLeaf,
        (if claim.first.slot = GENESIS_SLOT then .ok zeroBytes32
          else SszType.hashTreeRoot claim.first) = .ok firstLeaf ∧
        (if claim.second.slot = GENESIS_SLOT then .ok zeroBytes32
          else SszType.hashTreeRoot claim.second) = .ok secondLeaf ∧
        (firstLeaf ≠ secondLeaf ∨
          claim.first.slot ≠ GENESIS_SLOT ∧ claim.second.slot ≠ GENESIS_SLOT) ∧
        isValidNormalizedMerkleBranch firstLeaf claim.firstBranch gindex claim.root = .ok true ∧
        isValidNormalizedMerkleBranch secondLeaf claim.secondBranch gindex claim.root =
          .ok true := by
  rw [extractFinality_sha256]
  simp only [FinalityWins]
  refine and_congr_right fun _ => ?_
  -- The climbs keep every node after the front, since that rest has at most the depth.
  have whole : ∀ branch : List Bytes32,
      (branch.drop (branch.length - Nat.log2 gindex)).take (Nat.log2 gindex) =
        branch.drop (branch.length - Nat.log2 gindex) :=
    fun _ => List.take_of_length_le (by simp only [List.length_drop]; omega)
  have long : ∀ length : Nat, length - (length - Nat.log2 gindex) = Nat.log2 gindex ↔
      Nat.log2 gindex ≤ length := fun _ => by omega
  generalize (if claim.first.slot = GENESIS_SLOT then (.ok zeroBytes32 : Except Err Bytes32)
    else SszType.hashTreeRoot claim.first) = first
  generalize (if claim.second.slot = GENESIS_SLOT then (.ok zeroBytes32 : Except Err Bytes32)
    else SszType.hashTreeRoot claim.second) = second
  by_cases zero : gindex = 0
  · subst zero
    simp [getSubtreeIndex, gindexDepth, isValidNormalizedMerkleBranch, bind, Except.bind]
  · have depthIs : gindexDepth gindex = .ok (Nat.log2 gindex) := by
      simp [gindexDepth]
      omega
    cases first <;> cases second <;>
      simp [getSubtreeIndex, depthIs, isValidNormalizedMerkleBranch, bind, Except.bind, pure,
        Except.pure, extractBranches_sha256, whole, isValidMerkleBranch_eq_true_iff,
        toChunk_ok_iff, long]
    exact ⟨fun ⟨a, b, c, d, e, g, h⟩ => ⟨e, ⟨c, a, g⟩, d, b, h⟩,
      fun ⟨e, ⟨c, a, g⟩, d, b, h⟩ => ⟨a, b, c, d, e, g, h⟩⟩

/-- Two updates with one attested state root and slot, and different finalized headers, win.

It needs both to prove finality and to pass the finality check.

It needs the root of neither finalized header to be zero bytes, the leaf of the genesis slot.

The node hash is SHA-256, at the index of the finalized root at that slot. -/
theorem finalityWins_of_validateFinality {fork : Fork} {config : Config}
    {first second : LightClientUpdate preset fork}
    (firstAccepted : validateFinality config first = .ok ())
    (secondAccepted : validateFinality config second = .ok ())
    (firstFinality : first.isFinalityUpdate = true)
    (secondFinality : second.isFinalityUpdate = true)
    (sameRoot : first.attestedHeader.beacon.stateRoot = second.attestedHeader.beacon.stateRoot)
    (sameSlot : first.attestedHeader.beacon.slot = second.attestedHeader.beacon.slot)
    (differ : first.finalizedHeader.beacon ≠ second.finalizedHeader.beacon)
    (firstNonzero : SszType.hashTreeRoot first.finalizedHeader.beacon ≠ .ok zeroBytes32)
    (secondNonzero : SszType.hashTreeRoot second.finalizedHeader.beacon ≠ .ok zeroBytes32) :
    ∃ gindex, finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
        first.attestedHeader.beacon.slot = .ok gindex ∧
      FinalityWins gindex (extractFinality (m := Id) Cryptography.Hash.Sha256.hash gindex
        ⟨first.attestedHeader.beacon.stateRoot, first.finalizedHeader.beacon,
          first.finalityBranch.toList, second.finalizedHeader.beacon,
          second.finalityBranch.toList⟩).run := by
  obtain ⟨gindex, firstLeaf, indexed, firstRead, firstValid⟩ :=
    validateFinality_proves firstAccepted firstFinality
  obtain ⟨other, secondLeaf, otherIndexed, secondRead, secondValid⟩ :=
    validateFinality_proves secondAccepted secondFinality
  rw [← sameSlot, indexed, Except.ok.injEq] at otherIndexed
  subst otherIndexed
  rw [← sameRoot] at secondValid
  refine ⟨gindex, indexed, finalityWins_sha256_iff.mpr ⟨differ, firstLeaf, secondLeaf, ?_, ?_, ?_,
    firstValid, secondValid⟩⟩
  · rcases firstRead with ⟨genesis, rfl⟩ | ⟨later, rooted⟩
    · simp [genesis]
    · simp [later, rooted]
  · rcases secondRead with ⟨genesis, rfl⟩ | ⟨later, rooted⟩
    · simp [genesis]
    · simp [later, rooted]
  -- One leaf with a header at the genesis slot needs a zero root, or the two empty headers.
  rcases firstRead with ⟨firstGenesis, rfl⟩ | ⟨firstLater, firstRooted⟩ <;>
    rcases secondRead with ⟨secondGenesis, rfl⟩ | ⟨secondLater, secondRooted⟩
  · exact absurd ((validateFinality_beacon_of_genesis firstAccepted firstGenesis).trans
      (validateFinality_beacon_of_genesis secondAccepted secondGenesis).symm) differ
  · exact .inl fun same => secondNonzero (same ▸ secondRooted)
  · exact .inl fun same => firstNonzero (same.symm ▸ firstRooted)
  · exact .inr ⟨firstLater, secondLater⟩

end EthLib.Consensus

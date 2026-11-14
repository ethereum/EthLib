module

public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Serialization.Proofs.Ssz.BranchRandomOracle

/-!
# Proofs: two blob sidecars of one index and one body root in the random oracle model

The preset and the fork are fixed before the run.

An adversary queries the oracle, then outputs two blob sidecars.

The experiment roots both KZG commitments, with the oracle as the node hash.

It reads the subtree index from the blob index of the first sidecar, as the inclusion check does.

Then it climbs both inclusion proofs from their commitment roots at that index, with the oracle.

The climbs take the depth of the inclusion proof, which the preset fixes.

The adversary wins when the sidecars have one index, one body root and different commitments.

A win also needs both climbs to reach that body root.

Each win exposes two different queried messages with one answer, so the birthday bound applies.

Equal roots of two different commitments are one answer to their two different messages.

Two different commitment roots that climb to one body root give a collision of the climbs.

A win has probability at most `Q^2 / N`, where `N` is the number of digests.

`Q` bounds the oracle calls of the whole experiment, the adversary's and the extraction's.

An adversary of at most `q` calls gives `Q = q + 2 + 2 * depth`, with `depth` that of the proofs.

At the mainnet depth of 17, a win has probability at most `(q + 36)^2 / 2^256`.

With SHA-256 as the node hash, a win is two such sidecars that the inclusion check accepts.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Serialization.Ssz.RandomOracle
open OracleComp OracleSpec ENNReal
open Cryptography.Kzg (KZGCommitment)
open Cryptography.Merkle.RandomOracle (Collision experimentWith prEvent_experimentWith_le)

/-- What the blob experiment reports: the two sidecars, and the climbs of their proofs.

The climbs are absent when the subtree index or a commitment root cannot be read. -/
structure BlobOutcome (preset : Preset) where
  /-- The first sidecar of the adversary. -/
  first : BlobSidecar preset
  /-- The second sidecar of the adversary. -/
  second : BlobSidecar preset
  /-- The index, the commitment roots, the proofs and the roots that the proofs climb to. -/
  climbs : Option BranchOutcome

/-- The extraction for blob sidecars, with a node hash in any monad.

It roots both commitments, then reads the subtree index from the blob index of the first sidecar.

Then it climbs both proofs from their roots, at that index and at the depth of the proof.

The preset fixes that depth, and the fork fixes the place of the commitments in the body.

The experiment runs it with the oracle. -/
def extractBlobSidecars {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray)
    (preset : Preset) (fork : Fork) (claim : BlobSidecar preset × BlobSidecar preset) :
    m (BlobOutcome preset) := do
  let firstRoot ← (hashTreeRootM (Hasher.ofHash hash) (SszType.desc KZGCommitment)
    (SszType.toValue claim.1.kzgCommitment)).run
  let secondRoot ← (hashTreeRootM (Hasher.ofHash hash) (SszType.desc KZGCommitment)
    (SszType.toValue claim.2.kzgCommitment)).run
  let climbs ← (match blobKzgCommitmentGindex preset fork claim.1.index.toNat >>= getSubtreeIndex,
      firstRoot >>= toChunk, secondRoot >>= toChunk with
    | .ok index, .ok firstLeaf, .ok secondLeaf => do
      let climbs ← extractBranches hash preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat
        ⟨index, firstLeaf, claim.1.kzgCommitmentInclusionProof.toList, secondLeaf,
          claim.2.kzgCommitmentInclusionProof.toList⟩
      pure (some climbs)
    | _, _, _ => pure none)
  return ⟨claim.1, claim.2, climbs⟩

/-- The adversary wins: two sidecars with one index and one body root carry different commitments.

A win also needs both proofs to climb from the roots of their commitments to that body root. -/
def BlobWins {preset : Preset} (outcome : BlobOutcome preset) : Prop :=
  outcome.first.index = outcome.second.index ∧
    outcome.first.signedBlockHeader.message.bodyRoot =
      outcome.second.signedBlockHeader.message.bodyRoot ∧
    outcome.first.kzgCommitment ≠ outcome.second.kzgCommitment ∧
    ∃ climbs, outcome.climbs = some climbs ∧
      climbs.firstRoot = .ok outcome.first.signedBlockHeader.message.bodyRoot ∧
      climbs.secondRoot = .ok outcome.second.signedBlockHeader.message.bodyRoot

/-- The 48 bytes of a commitment and 16 zero bytes form its two packed nodes. -/
private theorem packBytes_kzgCommitment (commitment : KZGCommitment) :
    padded zeroChunk (Serialization.Ssz.packBytes commitment.toArray) 0 ++
        padded zeroChunk (Serialization.Ssz.packBytes commitment.toArray) 1 =
      commitment.toArray ++ Array.replicate 16 0 := by
  have size : commitment.toArray.size = 48 := commitment.size_toArray
  simp [padded, Serialization.Ssz.packBytes, size, bytesPerChunk, ← Array.append_assoc,
    Array.extract_append_extract, Array.extract_eq_self_of_le]

/-- A perfect tree of depth 1 over two nodes is one hash of the two nodes, with any hasher. -/
private theorem subtreeAtM_two {m : Type → Type} [Monad m] [LawfulMonad m] (hasher : Hasher m)
    {chunks : Array Bytes} (count : chunks.size = 2) :
    subtreeAtM hasher chunks 1 0 =
      combineM hasher.hash (padded zeroChunk chunks 0) (padded zeroChunk chunks 1) := by
  simp only [subtreeAtM, count]
  simp

/-- The root of a commitment is one hash of its 48 bytes and 16 zero bytes.

It holds for a hasher in any lawful monad. -/
theorem hashTreeRootM_kzgCommitment {m : Type → Type} [Monad m] [LawfulMonad m]
    (hasher : Hasher m) (commitment : KZGCommitment) :
    (hashTreeRootM hasher (SszType.desc KZGCommitment) (SszType.toValue commitment)).run = (do
      return .ok (← hasher.hash ⟨commitment.toArray ++ Array.replicate 16 0⟩).data) := by
  have size : commitment.toArray.size = 48 := commitment.size_toArray
  have count : (Serialization.Ssz.packBytes commitment.toArray).size = 2 := by
    simp [size, bytesPerChunk]
  show (hashTreeRootAtM hasher 1 (.byteVector 48) (.bytes commitment.toArray)).run = _
  simp only [hashTreeRootAtM, merkleLayout, size, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, liftM_pure, pure_bind]
  simp only [layoutChunksAtM, MerkleLayout.packing, Option.getD_none, Leaves.count,
    Array.extract_size, pure_bind, bind_pure, merkleizeBoundedUncheckedM, Nat.lt_irrefl,
    ↓reduceIte, ExceptT.run_lift]
  rw [count, show depthFor 2 = 1 from depthFor_pow 1, subtreeAtM_two hasher count, combineM,
    packBytes_kzgCommitment]
  simp only [map_bind, map_pure]

/-- A replayed commitment root caches its message, and is the answer of the table to it.

It needs the table to agree with the cache. -/
private theorem cached_of_hashTreeRootM_kzgCommitment {cache : HashOracle.QueryCache}
    {f : QueryImpl HashOracle Id} (hf : cache.AgreesWithFn f) {commitment : KZGCommitment}
    {root : Except Err Bytes}
    (hrun : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (SszType.desc KZGCommitment) (SszType.toValue commitment)).run = some root) :
    cache ⟨commitment.toArray ++ Array.replicate 16 0⟩ =
        some (f ⟨commitment.toArray ++ Array.replicate 16 0⟩) ∧
      root = .ok (tableHash f ⟨commitment.toArray ++ Array.replicate 16 0⟩).data := by
  have heval := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  rw [hashTreeRootM_kzgCommitment] at hrun heval
  simp only [Hasher.ofHash, evalWithAnswerFn_bind, evalWithAnswerFn_queryHash,
    evalWithAnswerFn_pure] at heval
  simp only [Hasher.ofHash, simulateQ_bind] at hrun
  obtain ⟨_, hquery, -⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨digest, hdigest⟩ := cached_of_queryHash hquery
  exact ⟨by rw [hdigest, hf hdigest], heval.symm⟩

/-- A replayed winning blob extraction exposes a collision of the cache.

Two different commitments with one root give two different messages with one answer.

Two different roots that climb to one body root give the collision of the two climbs.

It holds for every preset and fork. -/
theorem collision_of_extractBlobSidecars {preset : Preset} {fork : Fork}
    {cache : HashOracle.QueryCache} {claim : BlobSidecar preset × BlobSidecar preset}
    {outcome : BlobOutcome preset}
    (hrun : simulateQ cache.toPartialImpl (extractBlobSidecars queryHash preset fork claim) =
      some outcome)
    (hwins : BlobWins outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  simp only [extractBlobSidecars, simulateQ_bind] at hrun
  obtain ⟨firstRoot, hfirst, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨secondRoot, hsecond, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨climbs, hclimbs, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [simulateQ_pure] at hrun
  cases hrun
  obtain ⟨-, sameRoot, differ, climbed, present, firstClimbed, secondClimbed⟩ := hwins
  dsimp only at sameRoot differ present firstClimbed secondClimbed
  subst present
  obtain ⟨firstCached, rfl⟩ := cached_of_hashTreeRootM_kzgCommitment hf hfirst
  obtain ⟨secondCached, rfl⟩ := cached_of_hashTreeRootM_kzgCommitment hf hsecond
  split at hclimbs
  · rename_i index firstLeaf secondLeaf _ hfirstLeaf hsecondLeaf
    simp only [simulateQ_bind, simulateQ_pure] at hclimbs
    obtain ⟨_, hbranches, hclimbs⟩ := Option.bind_eq_some_iff.mp hclimbs
    cases hclimbs
    simp only [bind, Except.bind, toChunk_ok_iff] at hfirstLeaf hsecondLeaf
    by_cases sameLeaf : firstLeaf = secondLeaf
    · -- One root of two different commitments is one answer to two different messages.
      subst sameLeaf
      refine collision_of_cached (fun same => differ ?_) ?_ firstCached secondCached
      · exact Vector.toArray_inj.mp ((Array.append_left_inj _).mp same)
      · exact congrArg ByteArray.mk (hfirstLeaf.trans hsecondLeaf.symm)
    · -- Two different roots climb to one body root, so the search over the climbs finds one.
      have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hbranches
      simp only [extractBranches, evalWithAnswerFn_bind, evalWithAnswerFn_climbBranchM,
        evalWithAnswerFn_pure] at hout
      subst hout
      exact collision_of_extractBranches hbranches ⟨sameLeaf, by simp, by simp, _, firstClimbed,
        sameRoot ▸ secondClimbed⟩
  · simp only [simulateQ_pure] at hclimbs
    cases hclimbs

/-- The root of a commitment makes one oracle call. -/
private theorem hashTreeRootM_kzgCommitment_queryBound (commitment : KZGCommitment) :
    IsQueryBoundP (hashTreeRootM (Hasher.ofHash queryHash) (SszType.desc KZGCommitment)
      (SszType.toValue commitment)).run (fun _ => True) 1 := by
  rw [hashTreeRootM_kzgCommitment]
  simp [Hasher.ofHash, queryHash]

/-- The extraction makes at most `2 + 2 * depth` oracle calls, with `depth` that of the proofs.

It makes one call per commitment root, and climbs at most `depth` nodes of each proof. -/
theorem extractBlobSidecars_queryBound (preset : Preset) (fork : Fork)
    (claim : BlobSidecar preset × BlobSidecar preset) :
    IsQueryBoundP (extractBlobSidecars queryHash preset fork claim) (fun _ => True)
      (2 + 2 * preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat) := by
  unfold extractBlobSidecars
  refine (isQueryBoundP_bind (hashTreeRootM_kzgCommitment_queryBound _) fun _ _ =>
    isQueryBoundP_bind (hashTreeRootM_kzgCommitment_queryBound _) fun _ _ =>
      isQueryBoundP_bind (n := 2 * preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat) (m := 0) ?_
        fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)
  split
  · exact (isQueryBoundP_bind (extractBranches_queryBound _ _) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by omega)
  · exact isQueryBoundP_pure _ _ _

/-- The experiment makes at most `q + 2 + 2 * depth` oracle calls, with `depth` that of the proofs.

It needs the adversary to make at most `q` oracle calls.

The extraction makes one call per commitment root and at most one per climbed node. -/
theorem experimentWith_extractBlobSidecars_queryBound (preset : Preset) (fork : Fork)
    {adversary : OracleComp (unifSpec + HashOracle) (BlobSidecar preset × BlobSidecar preset)}
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    IsQueryBoundP (experimentWith (extractBlobSidecars queryHash preset fork) adversary)
      (fun t => t.isRight = true)
      (q + 2 + 2 * preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat) :=
  (isQueryBoundP_bind hq fun claim _ => IsQueryBoundP.liftComp_subSpec
    (fun _ => iff_of_true trivial rfl) (extractBlobSidecars_queryBound preset fork claim)).mono
    (by omega)

/-- An adversary that outputs two blob sidecars wins with probability at most `Q^2 / N`.

It wins when the sidecars have one index, one body root and different commitments.

A win also needs both proofs to climb from their commitment roots to that body root.

The roots are computed with the oracle as the node hash, and `N` is the number of digests.

It needs `Q` to bound the oracle calls of the whole experiment, repeats included.

The extraction adds one call per commitment root and at most one per climbed node.

The oracle cache starts empty, and the adversary's private sampling is not counted.

It holds for every preset and fork. -/
theorem prEvent_blobWins_le [SampleableType Hash32] (preset : Preset) (fork : Fork)
    (adversary : OracleComp (unifSpec + HashOracle) (BlobSidecar preset × BlobSidecar preset))
    {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractBlobSidecars queryHash preset fork) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBlobSidecars queryHash preset fork) adversary)).run ∅}[
        BlobWins z.1] ≤ Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  prEvent_experimentWith_le (extractBlobSidecars queryHash preset fork) BlobWins
    collision_of_extractBlobSidecars adversary hQ

/-- The same bound for 32 uniform bytes per answer: probability at most `Q^2 / 2^256`. -/
theorem prEvent_blobWins_le_two_pow (preset : Preset) (fork : Fork)
    (adversary : OracleComp (unifSpec + HashOracle) (BlobSidecar preset × BlobSidecar preset))
    {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractBlobSidecars queryHash preset fork) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBlobSidecars queryHash preset fork) adversary)).run ∅}[
        BlobWins z.1] ≤ Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_blobWins_le preset fork adversary hQ
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- The same bound with the adversary's oracle calls `q` counted alone.

A win has probability at most `(q + 2 + 2 * depth)^2 / 2^256`, with `depth` that of the proofs. -/
theorem prEvent_blobWins_le_of_adversary (preset : Preset) (fork : Fork)
    (adversary : OracleComp (unifSpec + HashOracle) (BlobSidecar preset × BlobSidecar preset))
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBlobSidecars queryHash preset fork) adversary)).run ∅}[
        BlobWins z.1] ≤
      (q + 2 + 2 * preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat : Nat) *
        (((q + 2 + 2 * preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat : Nat) : ℝ≥0∞) /
          2 ^ 256) :=
  prEvent_blobWins_le_two_pow preset fork adversary
    (experimentWith_extractBlobSidecars_queryBound preset fork hq)

/-- At the mainnet depth of 17, a win has probability at most `(q + 36)^2 / 2^256`.

It needs the adversary to make at most `q` oracle calls, and it holds for every fork. -/
theorem prEvent_blobWins_le_mainnet (fork : Fork)
    (adversary : OracleComp (unifSpec + HashOracle)
      (BlobSidecar .mainnet × BlobSidecar .mainnet))
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBlobSidecars queryHash .mainnet fork) adversary)).run ∅}[
        BlobWins z.1] ≤ (q + 36 : Nat) * (((q + 36 : Nat) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_blobWins_le_of_adversary .mainnet fork adversary hq

/-- With SHA-256 in the identity monad, the extraction reads the commitment roots of the spec. -/
theorem extractBlobSidecars_sha256 (preset : Preset) (fork : Fork)
    (claim : BlobSidecar preset × BlobSidecar preset) :
    (extractBlobSidecars (m := Id) Cryptography.Hash.Sha256.hash preset fork claim).run =
      ⟨claim.1, claim.2,
        match blobKzgCommitmentGindex preset fork claim.1.index.toNat >>= getSubtreeIndex,
            SszType.hashTreeRoot claim.1.kzgCommitment,
            SszType.hashTreeRoot claim.2.kzgCommitment with
        | .ok index, .ok firstLeaf, .ok secondLeaf =>
          some (extractBranches (m := Id) Cryptography.Hash.Sha256.hash
            preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat
            ⟨index, firstLeaf, claim.1.kzgCommitmentInclusionProof.toList, secondLeaf,
              claim.2.kzgCommitmentInclusionProof.toList⟩).run
        | _, _, _ => none⟩ := by
  simp only [extractBlobSidecars, ofHash_sha256]
  rfl

/-- With SHA-256 as the node hash, a win is two sidecars that the inclusion check accepts.

The two sidecars have one index and one body root, and different commitments.

The roots of the outcome are then computed with SHA-256, not with the oracle.

The step from SHA-256 to the oracle is the idealisation of the model, not a theorem.

It holds for every preset and fork. -/
theorem blobWins_sha256_iff {preset : Preset} {fork : Fork}
    {claim : BlobSidecar preset × BlobSidecar preset} :
    BlobWins (extractBlobSidecars (m := Id) Cryptography.Hash.Sha256.hash preset fork claim).run ↔
      claim.1.index = claim.2.index ∧
        claim.1.signedBlockHeader.message.bodyRoot =
          claim.2.signedBlockHeader.message.bodyRoot ∧
        claim.1.kzgCommitment ≠ claim.2.kzgCommitment ∧
        verifyBlobSidecarInclusionProof preset fork claim.1 = true ∧
        verifyBlobSidecarInclusionProof preset fork claim.2 = true := by
  rw [extractBlobSidecars_sha256]
  simp only [BlobWins]
  refine and_congr_right fun sameIndex => and_congr_right fun sameRoot =>
    and_congr_right fun _ => ?_
  -- Both checks read the subtree index of one blob index, and climb to one body root.
  unfold verifyBlobSidecarInclusionProof
  rw [← sameIndex, ← sameRoot]
  -- A proof of the inclusion depth keeps all its nodes, so the extraction climbs all of them.
  have whole : ∀ (sidecar : BlobSidecar preset),
      sidecar.kzgCommitmentInclusionProof.toList.take
          preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat =
        sidecar.kzgCommitmentInclusionProof.toList :=
    fun _ => List.take_of_length_le (by simp)
  cases read : blobKzgCommitmentGindex preset fork claim.1.index.toNat with
  | error => simp [bind, Except.bind]
  | ok gindex =>
    cases subtree : getSubtreeIndex gindex <;>
      cases firstRoot : SszType.hashTreeRoot claim.1.kzgCommitment <;>
      cases secondRoot : SszType.hashTreeRoot claim.2.kzgCommitment <;>
      simp [bind, Except.bind, subtree, extractBranches_sha256, whole,
        isValidMerkleBranch_eq_true_iff, toChunk_ok_iff]

end EthLib.Consensus

module

public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Serialization.Proofs.Ssz.BranchRandomOracle
import EthLib.Serialization.Proofs.Ssz.Typed.ForkKind

/-!
# Proofs: two data column headers of one body root in the random oracle model

An adversary outputs two partial data column headers, for a preset and a fork fixed before the run.

It wins with one body root and different lists of commitments, if both proofs reach that root.

The experiment roots both lists, then climbs both proofs as the inclusion check does.

Every hash is an oracle call.

Only the forks from Deneb and before Gloas put the list in the body, where the climbs can run.

A win exposes two different queried messages with one answer, so the birthday bound applies.

A win has probability at most `Q^2 / N`, where `Q` bounds all oracle calls and `N` counts digests.

The collision, the bound and the count of the extraction need a fork before Gloas.

At such a fork the list has a limit, the most blob commitments of a block.

The count grows with that limit and the depth of the proofs, not with the commitments.

At mainnet, an adversary of `q` calls gives a bound of `(q + 16392)^2 / 2^256` before Gloas.

At a fork before Deneb or from Gloas no outcome wins, and a win has probability zero.

With SHA-256 as the node hash, a win is two such headers that the inclusion check accepts.

That result holds at every preset and fork.

Before Gloas a data column sidecar carries the three fields of a partial header.

They are the commitments, the block header and the proof.

An adversary that outputs two sidecars gets the same bound, through the headers they carry.

With SHA-256, its win is two sidecars that the inclusion check of a sidecar accepts.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Serialization.Ssz.RandomOracle
open OracleComp OracleSpec ENNReal
open Cryptography.Merkle.RandomOracle (Collision experimentWith experimentWith_queryBound
  prEvent_experimentWith_le prEvent_experimentWith_eq_zero)

/-- What the column experiment reports: the two headers, and the climbs of their proofs.

The climbs are absent when the subtree index or a root of commitments cannot be read. -/
structure ColumnOutcome (preset : Preset) (fork : Fork) where
  /-- The first header of the adversary. -/
  first : PartialDataColumnHeader preset fork
  /-- The second header of the adversary. -/
  second : PartialDataColumnHeader preset fork
  /-- The index, the roots of the commitments, the proofs and the roots that the proofs reach. -/
  climbs : Option BranchOutcome

/-- The extraction for partial data column headers, with a node hash in any monad.

It roots both lists of commitments, then reads the subtree index of the list in the body.

Then it climbs both proofs from their roots, at that index and at the depth of the proof.

The preset fixes that depth, and the fork fixes the place of the list in the body.

The experiment runs it with the oracle. -/
def extractColumnHeaders {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray)
    (preset : Preset) (fork : Fork)
    (claim : PartialDataColumnHeader preset fork × PartialDataColumnHeader preset fork) :
    m (ColumnOutcome preset fork) := do
  let firstRoot ← (hashTreeRootM (Hasher.ofHash hash)
    (SszType.desc (BlobKZGCommitments preset fork)) (SszType.toValue claim.1.kzgCommitments)).run
  let secondRoot ← (hashTreeRootM (Hasher.ofHash hash)
    (SszType.desc (BlobKZGCommitments preset fork)) (SszType.toValue claim.2.kzgCommitments)).run
  let climbs ← (match blobKzgCommitmentsGindex preset fork >>= getSubtreeIndex,
      firstRoot >>= toChunk, secondRoot >>= toChunk with
    | .ok index, .ok firstLeaf, .ok secondLeaf => do
      let climbs ← extractBranches hash preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat
        ⟨index, firstLeaf, claim.1.kzgCommitmentsInclusionProof.toList, secondLeaf,
          claim.2.kzgCommitmentsInclusionProof.toList⟩
      pure (some climbs)
    | _, _, _ => pure none)
  return ⟨claim.1, claim.2, climbs⟩

/-- The adversary wins: two headers with one body root carry different lists of commitments.

A win also needs both proofs to climb from the roots of their lists to that body root. -/
def ColumnWins {preset : Preset} {fork : Fork} (outcome : ColumnOutcome preset fork) : Prop :=
  outcome.first.signedBlockHeader.message.bodyRoot =
      outcome.second.signedBlockHeader.message.bodyRoot ∧
    outcome.first.kzgCommitments ≠ outcome.second.kzgCommitments ∧
    ∃ climbs, outcome.climbs = some climbs ∧
      climbs.firstRoot = .ok outcome.first.signedBlockHeader.message.bodyRoot ∧
      climbs.secondRoot = .ok outcome.second.signedBlockHeader.message.bodyRoot

/-- A replayed winning column extraction exposes a collision of the cache.

Two different lists with one root give two different messages with one answer.

Two different roots that climb to one body root give the collision of the two climbs.

It needs a fork before Gloas, where the list of commitments has a limit. -/
theorem collision_of_extractColumnHeaders {preset : Preset} {fork : Fork}
    (beforeGloas : fork < .glamsterdam) {cache : HashOracle.QueryCache}
    {claim : PartialDataColumnHeader preset fork × PartialDataColumnHeader preset fork}
    {outcome : ColumnOutcome preset fork}
    (hrun : simulateQ cache.toPartialImpl (extractColumnHeaders queryHash preset fork claim) =
      some outcome)
    (hwins : ColumnWins outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  simp only [extractColumnHeaders, simulateQ_bind] at hrun
  obtain ⟨firstRoot, hfirst, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨secondRoot, hsecond, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨climbs, hclimbs, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [simulateQ_pure] at hrun
  cases hrun
  obtain ⟨sameRoot, differ, climbed, present, firstClimbed, secondClimbed⟩ := hwins
  dsimp only at sameRoot differ present firstClimbed secondClimbed
  subst present
  split at hclimbs
  · rename_i index firstLeaf secondLeaf _ hfirstLeaf hsecondLeaf
    simp only [simulateQ_bind, simulateQ_pure] at hclimbs
    obtain ⟨_, hbranches, hclimbs⟩ := Option.bind_eq_some_iff.mp hclimbs
    cases hclimbs
    by_cases sameLeaf : firstLeaf = secondLeaf
    · -- One root of two different lists is one answer to two different messages.
      rw [eq_ok_of_bind_toChunk hfirstLeaf, desc_forkList beforeGloas] at hfirst
      rw [eq_ok_of_bind_toChunk hsecondLeaf, desc_forkList beforeGloas, ← sameLeaf] at hsecond
      -- A list of commitments is its array, since the bound on its size is a proof.
      have lists : claim.1.kzgCommitments.data.toList ≠ claim.2.kzgCommitments.data.toList := by
        intro same
        apply differ
        have data : ∀ {first second : BlobKZGCommitments preset fork},
            first.data = second.data → first = second := by
          intro first second same
          cases first
          cases second
          cases same
          rfl
        exact data (Array.toList_inj.mp same)
      exact collision_of_hashTreeRootM_bytes48List
        (Nat.lt_trans (UInt64.toNat_lt preset.MAX_BLOB_COMMITMENTS_PER_BLOCK) (by decide)) lists
        hfirst hsecond
    · -- Two different roots climb to one body root, so the search finds a collision of the climbs.
      have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hbranches
      simp only [extractBranches, evalWithAnswerFn_bind, evalWithAnswerFn_climbBranchM,
        evalWithAnswerFn_pure] at hout
      subst hout
      exact collision_of_extractBranches hbranches ⟨sameLeaf, by simp, by simp, _, firstClimbed,
        sameRoot ▸ secondClimbed⟩
  · simp only [simulateQ_pure] at hclimbs
    cases hclimbs

/-- The generalized index of the list is the error of a missing field when the body has no list.

It needs a fork before Deneb or from Gloas. -/
theorem blobKzgCommitmentsGindex_of_lt_dencun_or_glamsterdam_le {preset : Preset} {fork : Fork}
    (outside : fork < .dencun ∨ .glamsterdam ≤ fork) :
    blobKzgCommitmentsGindex preset fork =
      .error (.noSuchField (BeaconBlockBody.names fork).length) := by
  cases fork <;> first | exact absurd outside (by decide) | rfl

/-- A replayed column extraction never wins when the body has no list of commitments.

The extraction then reads no subtree index, so it climbs neither proof.

It needs a fork before Deneb or from Gloas. -/
theorem not_columnWins_of_extractColumnHeaders {preset : Preset} {fork : Fork}
    (outside : fork < .dencun ∨ .glamsterdam ≤ fork) {cache : HashOracle.QueryCache}
    {claim : PartialDataColumnHeader preset fork × PartialDataColumnHeader preset fork}
    {outcome : ColumnOutcome preset fork}
    (hrun : simulateQ cache.toPartialImpl (extractColumnHeaders queryHash preset fork claim) =
      some outcome) :
    ¬ColumnWins outcome := by
  intro hwins
  simp only [extractColumnHeaders, simulateQ_bind] at hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨climbs, hclimbs, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [simulateQ_pure] at hrun
  cases hrun
  obtain ⟨-, -, climbed, present, -⟩ := hwins
  dsimp only at present
  subst present
  split at hclimbs
  · -- The lookup of the list fails, so no subtree index is read.
    rename_i _ _ _ located _ _
    rw [blobKzgCommitmentsGindex_of_lt_dencun_or_glamsterdam_le outside] at located
    simp [bind, Except.bind] at located
  · simp only [simulateQ_pure] at hclimbs
    cases hclimbs

/-- The extraction makes at most `2 * (limit + width) + 2 * depth` oracle calls.

Here `limit` is the most commitments of a block, and `depth` is that of the proofs.

The tree of a list has `width` leaves, the least power of two at least `limit`.

The root of a list makes one call per commitment, at most one per inner node, and one for the count.

Each climb takes at most `depth` nodes of its proof.

It needs a fork before Gloas, where the list of commitments has a limit. -/
theorem extractColumnHeaders_queryBound (preset : Preset) {fork : Fork}
    (beforeGloas : fork < .glamsterdam)
    (claim : PartialDataColumnHeader preset fork × PartialDataColumnHeader preset fork) :
    IsQueryBoundP (extractColumnHeaders queryHash preset fork claim) (fun _ => True)
      (2 * (preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat +
        2 ^ depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) +
        2 * preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat) := by
  unfold extractColumnHeaders
  rw [desc_forkList beforeGloas]
  refine (isQueryBoundP_bind (hashTreeRootM_bytes48List_queryBound _
    claim.1.kzgCommitments.data.toList) fun _ _ =>
      isQueryBoundP_bind (hashTreeRootM_bytes48List_queryBound _
        claim.2.kzgCommitments.data.toList) fun _ _ =>
        isQueryBoundP_bind (n := 2 * preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat) (m := 0) ?_
          fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)
  split
  · exact (isQueryBoundP_bind (extractBranches_queryBound _ _) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by omega)
  · exact isQueryBoundP_pure _ _ _

/-- The experiment makes at most `q + 2 * (limit + width) + 2 * depth` oracle calls.

Here `limit`, `width` and `depth` are those of the count of the extraction.

It needs a fork before Gloas, and the adversary to make at most `q` oracle calls.

The extraction roots both lists, then climbs at most `depth` nodes of each proof. -/
theorem experimentWith_extractColumnHeaders_queryBound (preset : Preset) {fork : Fork}
    (beforeGloas : fork < .glamsterdam)
    {adversary : OracleComp (unifSpec + HashOracle)
      (PartialDataColumnHeader preset fork × PartialDataColumnHeader preset fork)}
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    IsQueryBoundP (experimentWith (extractColumnHeaders queryHash preset fork) adversary)
      (fun t => t.isRight = true)
      (q + 2 * (preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat +
        2 ^ depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) +
        2 * preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat) :=
  (experimentWith_queryBound hq (extractColumnHeaders_queryBound preset beforeGloas)).mono
    (by omega)

/-- An adversary that outputs two headers wins with probability at most `Q^2 / N`.

A win is one body root, different lists of commitments, and both proofs climbing to that root.

`Q` bounds the oracle calls of the whole experiment, repeats included, and `N` counts digests.

The oracle cache starts empty, and the adversary's private sampling is not counted.

It needs a fork before Gloas, where the list of commitments has a limit. -/
theorem prEvent_columnWins_le [SampleableType Hash32] (preset : Preset) {fork : Fork}
    (beforeGloas : fork < .glamsterdam)
    (adversary : OracleComp (unifSpec + HashOracle)
      (PartialDataColumnHeader preset fork × PartialDataColumnHeader preset fork))
    {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractColumnHeaders queryHash preset fork) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractColumnHeaders queryHash preset fork) adversary)).run ∅}[
        ColumnWins z.1] ≤ Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  prEvent_experimentWith_le (extractColumnHeaders queryHash preset fork) ColumnWins
    (collision_of_extractColumnHeaders beforeGloas) adversary hQ

/-- The same bound for 32 uniform bytes per answer: probability at most `Q^2 / 2^256`.

It needs a fork before Gloas, and `Q` to bound the oracle calls of the whole experiment. -/
theorem prEvent_columnWins_le_two_pow (preset : Preset) {fork : Fork}
    (beforeGloas : fork < .glamsterdam)
    (adversary : OracleComp (unifSpec + HashOracle)
      (PartialDataColumnHeader preset fork × PartialDataColumnHeader preset fork))
    {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractColumnHeaders queryHash preset fork) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractColumnHeaders queryHash preset fork) adversary)).run ∅}[
        ColumnWins z.1] ≤ Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_columnWins_le preset beforeGloas adversary hQ
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- The same bound with the adversary's oracle calls `q` counted alone.

A win has probability at most `Q^2 / 2^256`, with `Q = q + 2 * (limit + width) + 2 * depth`.

Here `limit` is the most commitments of a block, and `depth` is that of the proofs.

The tree of a list has `width` leaves, the least power of two at least `limit`.

It needs a fork before Gloas, and the adversary to make at most `q` oracle calls. -/
theorem prEvent_columnWins_le_of_adversary (preset : Preset) {fork : Fork}
    (beforeGloas : fork < .glamsterdam)
    (adversary : OracleComp (unifSpec + HashOracle)
      (PartialDataColumnHeader preset fork × PartialDataColumnHeader preset fork))
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractColumnHeaders queryHash preset fork) adversary)).run ∅}[
        ColumnWins z.1] ≤
      (q + 2 * (preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat +
        2 ^ depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) +
        2 * preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat : Nat) *
        (((q + 2 * (preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat +
          2 ^ depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) +
          2 * preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat : Nat) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_columnWins_le_two_pow preset beforeGloas adversary
    (experimentWith_extractColumnHeaders_queryBound preset beforeGloas hq)

/-- At mainnet, a win has probability at most `(q + 16392)^2 / 2^256`.

There a list holds at most 4096 commitments, and a proof has 4 nodes.

It needs a fork before Gloas, and the adversary to make at most `q` oracle calls. -/
theorem prEvent_columnWins_le_mainnet {fork : Fork} (beforeGloas : fork < .glamsterdam)
    (adversary : OracleComp (unifSpec + HashOracle)
      (PartialDataColumnHeader .mainnet fork × PartialDataColumnHeader .mainnet fork))
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractColumnHeaders queryHash .mainnet fork) adversary)).run ∅}[
        ColumnWins z.1] ≤ (q + 16392 : Nat) * (((q + 16392 : Nat) : ℝ≥0∞) / 2 ^ 256) := by
  have count : 2 * (Preset.mainnet.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat +
      2 ^ depthFor Preset.mainnet.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) +
      2 * Preset.mainnet.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat = 16392 := by
    rw [show Preset.mainnet.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat = 2 ^ 12 from rfl, depthFor_pow]
    rfl
  have bound := prEvent_columnWins_le_of_adversary .mainnet beforeGloas adversary hq
  rw [Nat.add_assoc, count] at bound
  exact bound

/-- An adversary that outputs two headers wins with probability zero when the body has no list.

Every outcome of the experiment is a replay of the extraction, and no replay wins.

The oracle cache starts empty, and no count of oracle calls is needed.

It needs a fork before Deneb or from Gloas. -/
theorem prEvent_columnWins_eq_zero [SampleableType Hash32] (preset : Preset) {fork : Fork}
    (outside : fork < .dencun ∨ .glamsterdam ≤ fork)
    (adversary : OracleComp (unifSpec + HashOracle)
      (PartialDataColumnHeader preset fork × PartialDataColumnHeader preset fork)) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractColumnHeaders queryHash preset fork) adversary)).run ∅}[
        ColumnWins z.1] = 0 :=
  prEvent_experimentWith_eq_zero _ _ (not_columnWins_of_extractColumnHeaders outside) adversary

/-- With SHA-256, the extraction roots each list and reads the index as the spec does. -/
theorem extractColumnHeaders_sha256 (preset : Preset) (fork : Fork)
    (claim : PartialDataColumnHeader preset fork × PartialDataColumnHeader preset fork) :
    (extractColumnHeaders (m := Id) Cryptography.Hash.Sha256.hash preset fork claim).run =
      ⟨claim.1, claim.2,
        match blobKzgCommitmentsGindex preset fork >>= getSubtreeIndex,
            SszType.hashTreeRoot claim.1.kzgCommitments,
            SszType.hashTreeRoot claim.2.kzgCommitments with
        | .ok index, .ok firstLeaf, .ok secondLeaf =>
          some (extractBranches (m := Id) Cryptography.Hash.Sha256.hash
            preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat
            ⟨index, firstLeaf, claim.1.kzgCommitmentsInclusionProof.toList, secondLeaf,
              claim.2.kzgCommitmentsInclusionProof.toList⟩).run
        | _, _, _ => none⟩ := by
  simp only [extractColumnHeaders, ofHash_sha256]
  rfl

/-- With SHA-256 as the node hash, a win is two headers that the inclusion check accepts.

The two headers have one body root, and different lists of commitments.

The roots of the outcome are then computed with SHA-256, not with the oracle.

The step from SHA-256 to the oracle is the idealisation of the model, not a theorem.

It holds for every preset and fork. -/
theorem columnWins_sha256_iff {preset : Preset} {fork : Fork}
    {claim : PartialDataColumnHeader preset fork × PartialDataColumnHeader preset fork} :
    ColumnWins (extractColumnHeaders (m := Id) Cryptography.Hash.Sha256.hash preset fork
        claim).run ↔
      claim.1.signedBlockHeader.message.bodyRoot = claim.2.signedBlockHeader.message.bodyRoot ∧
        claim.1.kzgCommitments ≠ claim.2.kzgCommitments ∧
        verifyKzgCommitmentsInclusionProof preset claim.1.kzgCommitments
          claim.1.kzgCommitmentsInclusionProof
          claim.1.signedBlockHeader.message.bodyRoot = true ∧
        verifyKzgCommitmentsInclusionProof preset claim.2.kzgCommitments
          claim.2.kzgCommitmentsInclusionProof
          claim.2.signedBlockHeader.message.bodyRoot = true := by
  rw [extractColumnHeaders_sha256]
  simp only [ColumnWins]
  refine and_congr_right fun sameRoot => and_congr_right fun _ => ?_
  -- Both checks read the subtree index of the list in the body, and climb to one body root.
  unfold verifyKzgCommitmentsInclusionProof
  rw [← sameRoot]
  -- A proof of the inclusion depth keeps all its nodes, so the extraction climbs all of them.
  have whole : ∀ (header : PartialDataColumnHeader preset fork),
      header.kzgCommitmentsInclusionProof.toList.take
          preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat =
        header.kzgCommitmentsInclusionProof.toList :=
    fun _ => List.take_of_length_le (by simp)
  cases read : blobKzgCommitmentsGindex preset fork with
  | error => simp [bind, Except.bind]
  | ok gindex =>
    cases subtree : getSubtreeIndex gindex <;>
      cases firstRoot : SszType.hashTreeRoot claim.1.kzgCommitments <;>
      cases secondRoot : SszType.hashTreeRoot claim.2.kzgCommitments <;>
      simp [bind, Except.bind, subtree, extractBranches_sha256, whole,
        isValidMerkleBranch_eq_true_iff, toChunk_ok_iff]

/-- The header that a sidecar carries: its commitments, its signed block header and their proof.

It needs a fork before Gloas, where a sidecar carries all three. -/
def DataColumnSidecar.partialHeader {preset : Preset} {fork : Fork}
    (beforeGloas : fork < .glamsterdam) (sidecar : DataColumnSidecar preset fork) :
    PartialDataColumnHeader preset fork :=
  ⟨sidecar.kzgCommitments beforeGloas, sidecar.signedBlockHeader beforeGloas,
    sidecar.kzgCommitmentsInclusionProof beforeGloas⟩

/-- An adversary that outputs two sidecars wins with probability at most `Q^2 / 2^256`.

The experiment takes the header that each sidecar carries, and runs the extraction on the two.

So a win reads the commitments, the proof and the body root of each sidecar, and no other field.

Here `Q = q + 2 * (limit + width) + 2 * depth`, as in the bound for two headers.

It needs a fork before Gloas, and the adversary to make at most `q` oracle calls. -/
theorem prEvent_columnWins_le_of_sidecars (preset : Preset) {fork : Fork}
    (beforeGloas : fork < .glamsterdam)
    (adversary : OracleComp (unifSpec + HashOracle)
      (DataColumnSidecar preset fork × DataColumnSidecar preset fork))
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractColumnHeaders queryHash preset fork)
        (Prod.map (·.partialHeader beforeGloas) (·.partialHeader beforeGloas) <$>
          adversary))).run ∅}[
        ColumnWins z.1] ≤
      (q + 2 * (preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat +
        2 ^ depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) +
        2 * preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat : Nat) *
        (((q + 2 * (preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat +
          2 ^ depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) +
          2 * preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat : Nat) : ℝ≥0∞) / 2 ^ 256) :=
  -- Taking the headers makes no oracle call, so the adversary keeps its count.
  prEvent_columnWins_le_of_adversary preset beforeGloas _ (by rw [isQueryBoundP_map_iff]; exact hq)

/-- With SHA-256 as the node hash, a win of two sidecars is two that the inclusion check accepts.

The two sidecars have one body root, and different lists of commitments.

It needs a fork before Gloas, where a sidecar carries the proof. -/
theorem columnWins_sha256_iff_of_sidecars {preset : Preset} {fork : Fork}
    (beforeGloas : fork < .glamsterdam)
    {claim : DataColumnSidecar preset fork × DataColumnSidecar preset fork} :
    ColumnWins (extractColumnHeaders (m := Id) Cryptography.Hash.Sha256.hash preset fork
        (claim.1.partialHeader beforeGloas, claim.2.partialHeader beforeGloas)).run ↔
      (claim.1.signedBlockHeader beforeGloas).message.bodyRoot =
          (claim.2.signedBlockHeader beforeGloas).message.bodyRoot ∧
        claim.1.kzgCommitments beforeGloas ≠ claim.2.kzgCommitments beforeGloas ∧
        verifyDataColumnSidecarInclusionProof preset beforeGloas claim.1 = true ∧
        verifyDataColumnSidecarInclusionProof preset beforeGloas claim.2 = true :=
  columnWins_sha256_iff

end EthLib.Consensus

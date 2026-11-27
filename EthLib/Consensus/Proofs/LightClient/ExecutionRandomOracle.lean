module

public import EthLib.Consensus.Proofs.LightClient.Execution
public import EthLib.Serialization.Proofs.Ssz.BranchRandomOracle

/-!
# Proofs: two execution headers of one body root in the random oracle model

An adversary wins with two different execution headers whose branches climb to one body root.

Each branch climbs from node 25, as the light client check does from Capella to Fulu.

At a fork from Deneb, the check climbs so only at a slot from Deneb.

Every hash of the experiment is an oracle call.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Serialization.Ssz.RandomOracle
open OracleComp OracleSpec ENNReal
open Cryptography.Merkle.RandomOracle (Collision experimentWith experimentWith_queryBound
  prEvent_experimentWith_le)

variable {preset : Preset} {fork : Fork}

/-- What the adversary outputs: one body root, and two execution headers with a branch each. -/
structure ExecutionClaim (preset : Preset) (fork : Fork) where
  /-- The body root that both branches must reach. -/
  root : Root
  /-- The first execution payload header. -/
  first : ExecutionPayloadHeader preset fork
  /-- The nodes of the branch of the first header, from its root up. -/
  firstBranch : List Bytes32
  /-- The second execution payload header. -/
  second : ExecutionPayloadHeader preset fork
  /-- The nodes of the branch of the second header, from its root up. -/
  secondBranch : List Bytes32

/-- What the execution experiment reports: the claim, the roots of both headers and the climbs.

The climbs are absent when a root cannot be read as one node. -/
structure ExecutionOutcome (preset : Preset) (fork : Fork) where
  /-- The body root, the two headers and their branches. -/
  claim : ExecutionClaim preset fork
  /-- The two headers as values, with their roots under the oracle. -/
  roots : Outcome
  /-- The index, the two leaves, the climbed nodes and their roots. -/
  climbs : Option BranchOutcome

/-- The extraction for execution headers.

It roots both headers as the whole-value experiment does, then climbs both branches. -/
def extractExecution (claim : ExecutionClaim preset fork) :
    OracleComp HashOracle (ExecutionOutcome preset fork) := do
  -- Each root is computed with the oracle, and every hash input of both is queried again.
  let roots ← extract (SszType.desc (ExecutionPayloadHeader preset fork))
    (SszType.toValue claim.first) (SszType.toValue claim.second)
  let climbs ← (match roots.firstRoot >>= toChunk, roots.secondRoot >>= toChunk with
    | .ok firstLeaf, .ok secondLeaf => do
      -- Node 25 is at depth 4 and has index 9 among the nodes of its depth.
      let climbs ← extractBranches queryHash (Nat.log2 EXECUTION_PAYLOAD_GINDEX)
        ⟨EXECUTION_PAYLOAD_GINDEX % 2 ^ Nat.log2 EXECUTION_PAYLOAD_GINDEX, firstLeaf,
          claim.firstBranch, secondLeaf, claim.secondBranch⟩
      pure (some climbs)
    | _, _ => pure none)
  return ⟨claim, roots, climbs⟩

/-- The adversary wins: two different execution headers whose branches climb to the body root.

Each branch has one node per level below node 25. -/
def ExecutionWins (outcome : ExecutionOutcome preset fork) : Prop :=
  outcome.claim.first ≠ outcome.claim.second ∧
    outcome.claim.firstBranch.length = Nat.log2 EXECUTION_PAYLOAD_GINDEX ∧
    outcome.claim.secondBranch.length = Nat.log2 EXECUTION_PAYLOAD_GINDEX ∧
    ∃ climbs, outcome.climbs = some climbs ∧
      climbs.firstRoot = .ok outcome.claim.root ∧ climbs.secondRoot = .ok outcome.claim.root

/-- A replayed winning execution extraction exposes a collision of the cache.

Two different leaves that climb to one body root give the collision of the two climbs.

One leaf for two different headers gives the collision of the whole-value experiment. -/
theorem collision_of_extractExecution [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    {cache : HashOracle.QueryCache} {claim : ExecutionClaim preset fork}
    {outcome : ExecutionOutcome preset fork}
    (hrun : simulateQ cache.toPartialImpl (extractExecution claim) = some outcome)
    (hwins : ExecutionWins outcome) : Collision cache := by
  simp only [extractExecution, simulateQ_bind] at hrun
  obtain ⟨roots, hroots, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨climbs, hclimbs, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [simulateQ_pure] at hrun
  cases hrun
  obtain ⟨differ, firstLong, secondLong, climbed, present, firstClimbed, secondClimbed⟩ := hwins
  dsimp only at differ firstLong secondLong present firstClimbed secondClimbed
  subst present
  split at hclimbs
  · rename_i firstLeaf secondLeaf hfirstLeaf hsecondLeaf
    simp only [simulateQ_bind, simulateQ_pure] at hclimbs
    obtain ⟨_, hbranches, hclimbs⟩ := Option.bind_eq_some_iff.mp hclimbs
    cases hclimbs
    -- The climbs start from the two leaves that the extraction read.
    obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
    have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hbranches
    simp only [extractBranches, evalWithAnswerFn_bind, evalWithAnswerFn_climbBranchM,
      evalWithAnswerFn_pure] at hout
    subst hout
    by_cases sameLeaf : firstLeaf = secondLeaf
    · -- One leaf roots both headers, so the whole-value experiment wins.
      subst sameLeaf
      -- The extraction of the values reports the two headers it was given.
      have reported := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hroots
      rw [evalWithAnswerFn_extract] at reported
      subst reported
      refine collision_of_extract hroots ⟨LawfulSszType.wellFormed, ?_, ?_, ?_, ?_, ?_,
        ⟨firstLeaf.toArray⟩, eq_ok_of_bind_toChunk hfirstLeaf,
        eq_ok_of_bind_toChunk hsecondLeaf⟩
      · exact LawfulSszType.fits _
      · exact LawfulSszType.fits _
      · exact ExecutionPayloadHeader.commitmentSized _
      · exact ExecutionPayloadHeader.commitmentSized _
      · -- Two different headers are two different values.
        intro same
        have read := congrArg (SszType.ofValue (α := ExecutionPayloadHeader preset fork)) same
        rw [LawfulSszType.ofValue_toValue, LawfulSszType.ofValue_toValue] at read
        exact differ (Except.ok.inj read)
    · -- Two different leaves climb to one body root, so the climbs collide.
      exact collision_of_extractBranches hbranches ⟨sameLeaf, firstLong, secondLong, _,
        firstClimbed, secondClimbed⟩
  · simp only [simulateQ_pure] at hclimbs
    cases hclimbs

/-- The extraction makes the oracle calls of the roots and at most 8 more, one per climbed node.

It needs the whole-value extraction to make at most `n` calls on every two headers. -/
theorem extractExecution_queryBound {n : Nat}
    (hroots : ∀ first second : ExecutionPayloadHeader preset fork,
      IsQueryBoundP (extract (SszType.desc (ExecutionPayloadHeader preset fork))
        (SszType.toValue first) (SszType.toValue second)) (fun _ => True) n)
    (claim : ExecutionClaim preset fork) :
    IsQueryBoundP (extractExecution claim) (fun _ => True) (n + 8) := by
  unfold extractExecution
  refine (isQueryBoundP_bind (hroots _ _) fun _ _ =>
    isQueryBoundP_bind (n := 2 * Nat.log2 EXECUTION_PAYLOAD_GINDEX) (m := 0) ?_
      fun _ _ => isQueryBoundP_pure _ _ 0).mono (by simp [EXECUTION_PAYLOAD_GINDEX])
  split
  · exact (isQueryBoundP_bind (extractBranches_queryBound _ _) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by omega)
  · exact isQueryBoundP_pure _ _ _

/-- An adversary that outputs two execution headers wins with probability at most `Q^2 / N`.

`Q` bounds the oracle calls of the whole experiment, repeats included, and `N` counts the digests.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_executionWins_le [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    (adversary : OracleComp (unifSpec + HashOracle) (ExecutionClaim preset fork)) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith extractExecution adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl (experimentWith extractExecution adversary)).run ∅}[
      ExecutionWins z.1] ≤ Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  -- Each win exposes two different queried inputs with one answer, so the birthday bound applies.
  prEvent_experimentWith_le extractExecution ExecutionWins collision_of_extractExecution
    adversary hQ

/-- The same bound for an adversary of `q` oracle calls and 32 uniform bytes per answer.

A win has probability at most `(q + n + 8)^2 / 2^256`.

It assumes that the whole-value extraction makes at most `n` calls on every two headers. -/
theorem prEvent_executionWins_le_of_adversary [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    {n : Nat}
    (hroots : ∀ first second : ExecutionPayloadHeader preset fork,
      IsQueryBoundP (extract (SszType.desc (ExecutionPayloadHeader preset fork))
        (SszType.toValue first) (SszType.toValue second)) (fun _ => True) n)
    (adversary : OracleComp (unifSpec + HashOracle) (ExecutionClaim preset fork)) {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl (experimentWith extractExecution adversary)).run ∅}[
      ExecutionWins z.1] ≤ (q + n + 8 : Nat) * (((q + n + 8 : Nat) : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_executionWins_le (Q := q + n + 8) adversary
    ((experimentWith_queryBound hq (extractExecution_queryBound hroots)).mono (by omega))
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- With SHA-256 as the answer table, a win is two different headers whose branches are valid.

The branch check accepts each branch, from the root of its header at node 25 to the body root.

The step from SHA-256 to the oracle is the idealisation of the model, not a theorem. -/
theorem executionWins_sha256_iff [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    {claim : ExecutionClaim preset fork} :
    ExecutionWins (evalWithAnswerFn sha256Answers (extractExecution claim)) ↔
      claim.first ≠ claim.second ∧ ∃ firstLeaf secondLeaf,
        SszType.hashTreeRoot claim.first = .ok firstLeaf ∧
        SszType.hashTreeRoot claim.second = .ok secondLeaf ∧
        isValidMerkleBranch firstLeaf claim.firstBranch (Nat.log2 EXECUTION_PAYLOAD_GINDEX)
          (EXECUTION_PAYLOAD_GINDEX % 2 ^ Nat.log2 EXECUTION_PAYLOAD_GINDEX) claim.root = true ∧
        isValidMerkleBranch secondLeaf claim.secondBranch (Nat.log2 EXECUTION_PAYLOAD_GINDEX)
          (EXECUTION_PAYLOAD_GINDEX % 2 ^ Nat.log2 EXECUTION_PAYLOAD_GINDEX) claim.root =
            true := by
  -- With SHA-256 as the table, each leaf is the root of its header.
  have read : ∀ header : ExecutionPayloadHeader preset fork,
      Bind.bind (m := Except Err) (hashTreeRootM (Hasher.ofHash (m := Id)
        (tableHash sha256Answers)) (SszType.desc (ExecutionPayloadHeader preset fork))
          (SszType.toValue header)).run toChunk = SszType.hashTreeRoot header := by
    intro header
    rw [tableHash_sha256Answers, ofHash_sha256, SszType.hashTreeRoot_eq]
    rfl
  simp only [extractExecution, evalWithAnswerFn_bind, evalWithAnswerFn_extract, read]
  generalize SszType.hashTreeRoot claim.first = first
  generalize SszType.hashTreeRoot claim.second = second
  -- Without both leaves the extraction climbs nothing, and the check has no leaf to climb from.
  cases first with
  | error => simp [ExecutionWins]
  | ok firstLeaf =>
    cases second with
    | error => simp [ExecutionWins]
    | ok secondLeaf =>
      -- The climbs, run with the SHA-256 table, are the climbs of the check.
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, extractBranches,
        evalWithAnswerFn_climbBranchM, tableHash_sha256Answers]
      simp only [ExecutionWins, Option.some.injEq, exists_eq_left', Except.ok.injEq,
        isValidMerkleBranch_eq_true_iff, toChunk_ok_iff]
      -- A branch of 4 nodes keeps all of them, so the extraction climbs the whole branch.
      constructor
      · rintro ⟨differ, firstCount, secondCount, firstClimbed, secondClimbed⟩
        rw [List.take_of_length_le firstCount.le] at firstClimbed
        rw [List.take_of_length_le secondCount.le] at secondClimbed
        exact ⟨differ, _, _, rfl, rfl, ⟨firstCount, firstClimbed⟩, secondCount, secondClimbed⟩
      · rintro ⟨differ, _, _, rfl, rfl, ⟨firstCount, firstClimbed⟩, secondCount, secondClimbed⟩
        refine ⟨differ, firstCount, secondCount, ?_, ?_⟩
        · rw [List.take_of_length_le firstCount.le]
          exact firstClimbed
        · rw [List.take_of_length_le secondCount.le]
          exact secondClimbed

/-- Two valid headers with one body root and different execution headers win, with SHA-256.

The fork is from Capella to Fulu, and each slot is from Capella, and from Deneb at Deneb or later.

The branches of the claim are those of the two headers. -/
theorem executionWins_of_isValidLightClientHeader [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    {config : Config} (capella : .shapella ≤ fork) (beforeGloas : fork < .glamsterdam)
    {first second : LightClientHeader preset fork}
    (firstValid : isValidLightClientHeader config first = .ok true)
    (secondValid : isValidLightClientHeader config second = .ok true)
    (firstStarted : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset first.beacon.slot)
    (secondStarted : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset second.beacon.slot)
    (firstFull : .dencun ≤ fork →
      config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset first.beacon.slot)
    (secondFull : .dencun ≤ fork →
      config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset second.beacon.slot)
    (sameRoot : first.beacon.bodyRoot = second.beacon.bodyRoot)
    (differ : first.execution ⟨capella, beforeGloas⟩ ≠ second.execution ⟨capella, beforeGloas⟩) :
    ExecutionWins (evalWithAnswerFn sha256Answers (extractExecution
      ⟨first.beacon.bodyRoot, first.execution ⟨capella, beforeGloas⟩,
        (first.executionBranch capella).toList, second.execution ⟨capella, beforeGloas⟩,
        (second.executionBranch capella).toList⟩)) := by
  -- Each header climbs from its execution root, which is the root of its execution header.
  obtain ⟨firstLeaf, firstRead, firstClimbs⟩ :=
    isValidLightClientHeader_executionBranch capella beforeGloas firstValid firstStarted
  obtain ⟨firstRoot, firstRooted, firstExecution⟩ :=
    getLcExecutionRoot_execution capella beforeGloas firstStarted firstFull
  rw [firstExecution, Except.ok.injEq] at firstRead
  subst firstRead
  obtain ⟨secondLeaf, secondRead, secondClimbs⟩ :=
    isValidLightClientHeader_executionBranch capella beforeGloas secondValid secondStarted
  obtain ⟨secondRoot, secondRooted, secondExecution⟩ :=
    getLcExecutionRoot_execution capella beforeGloas secondStarted secondFull
  rw [secondExecution, Except.ok.injEq] at secondRead
  subst secondRead
  rw [← sameRoot] at secondClimbs
  exact executionWins_sha256_iff.mpr ⟨differ, _, _, firstRooted, secondRooted, firstClimbs,
    secondClimbs⟩

end EthLib.Consensus

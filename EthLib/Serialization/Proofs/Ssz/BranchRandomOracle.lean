module

public import EthLib.Serialization.Proofs.Ssz.RandomOracle
public import EthLib.Serialization.Proofs.Ssz.Merkle.Branch

/-!
# Proofs: two branches of one root in the random oracle model

An adversary that makes queries outputs one index and two leaves, each with a branch.

The depth of the branches is fixed before the run.

The adversary wins when the leaves differ, both branches have that depth, and both reach one root.

The experiment climbs both branches as the branch check does, with the oracle as the node hash.

Each win exposes two different queried inputs with one answer, so the birthday bound applies.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2.

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Serialization.Ssz.RandomOracle

open EthLib.Base
open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Merkle.RandomOracle (Collision experimentWith prEvent_experimentWith_le)

/-- What the adversary outputs: one index, and two leaves with a branch each. -/
structure BranchClaim where
  /-- The index of both leaves among the nodes of their depth. -/
  index : Nat
  /-- The first leaf. -/
  firstLeaf : Vector UInt8 32
  /-- The nodes of the first branch, from the leaf up. -/
  firstBranch : List (Vector UInt8 32)
  /-- The second leaf. -/
  secondLeaf : Vector UInt8 32
  /-- The nodes of the second branch, from the leaf up. -/
  secondBranch : List (Vector UInt8 32)

/-- What the branch experiment reports: the claim and the roots of its two branches. -/
structure BranchOutcome where
  /-- The index, leaves and branches of the adversary. -/
  claim : BranchClaim
  /-- The root that the first branch climbs to, as a node. -/
  firstRoot : Except Err (Vector UInt8 32)
  /-- The root that the second branch climbs to, as a node. -/
  secondRoot : Except Err (Vector UInt8 32)

/-- The extraction for branches, with a node hash in any monad.

It climbs the first `depth` nodes of each branch from its leaf, as the branch check does.

The experiment runs it with the oracle. -/
def extractBranches {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray) (depth : Nat)
    (claim : BranchClaim) : m BranchOutcome := do
  let firstRoot ← climbBranchM hash claim.index 0 claim.firstLeaf.toArray
    ((claim.firstBranch.take depth).map Vector.toArray)
  let secondRoot ← climbBranchM hash claim.index 0 claim.secondLeaf.toArray
    ((claim.secondBranch.take depth).map Vector.toArray)
  return ⟨claim, toChunk firstRoot, toChunk secondRoot⟩

/-- The adversary wins: two different leaves at one index climb to one root.

A win also needs both branches to have `depth` nodes. -/
def BranchWins (depth : Nat) (outcome : BranchOutcome) : Prop :=
  outcome.claim.firstLeaf ≠ outcome.claim.secondLeaf ∧
    outcome.claim.firstBranch.length = depth ∧ outcome.claim.secondBranch.length = depth ∧
    ∃ root, outcome.firstRoot = .ok root ∧ outcome.secondRoot = .ok root

/-- A climb, run against a full answer table, is the climb with that table. -/
theorem evalWithAnswerFn_climbBranchM (f : QueryImpl HashOracle Id) (index level : Nat)
    (node : Bytes) (branch : List Bytes) :
    evalWithAnswerFn f (climbBranchM queryHash index level node branch) =
      (climbBranchM (m := Id) (tableHash f) index level node branch).run := by
  unfold climbBranchM
  rw [Cryptography.Merkle.climb_map_monad (fun _ _ => combineM queryHash)
    (fun {β} (x : OracleComp HashOracle β) => (evalWithAnswerFn f x : Id β))
    (fun _ => rfl) (fun _ _ => evalWithAnswerFn_bind _ _ _)]
  exact congrArg (fun hash => Cryptography.Merkle.climb hash level (index >>> level) node branch)
    (by funext _ _ left right; exact evalWithAnswerFn_combineM f left right)

/-- A replayed climb caches every message it hashes, with the answer of the table.

It needs the table to agree with the cache. -/
theorem cached_of_climbBranchM {cache : HashOracle.QueryCache} {f : QueryImpl HashOracle Id}
    (hf : cache.AgreesWithFn f) {index level : Nat} {node root : Bytes} {branch : List Bytes}
    (hrun : simulateQ cache.toPartialImpl (climbBranchM queryHash index level node branch) =
      some root) :
    ∀ x ∈ branchMessages index level node branch (tableHash f),
      cache (ByteArray.mk x) = some (f (ByteArray.mk x)) := by
  -- Each level queries its pair, and the levels above climb from the parent of the table.
  have climbed : ∀ (branch : List Bytes) (level j : Nat) (node : Bytes) {root : Bytes},
      simulateQ cache.toPartialImpl
          (Cryptography.Merkle.climb (fun _ _ => combineM queryHash) level j node branch) =
        some root →
      ∀ x ∈ Cryptography.Merkle.climbPairs (fun _ _ => combineM (m := Id) (tableHash f)) level j
          node branch,
        cache (ByteArray.mk (x.1 ++ x.2)) = some (f (ByteArray.mk (x.1 ++ x.2))) := by
    intro branch
    induction branch with
    | nil =>
      intro _ _ _ _ _ x hx
      simp [Cryptography.Merkle.climbPairs] at hx
    | cons sibling rest ih =>
      intro level j node root hrun x hx
      simp only [Cryptography.Merkle.climb, simulateQ_bind] at hrun
      obtain ⟨parent, hparent, hrun⟩ := Option.bind_eq_some_iff.mp hrun
      -- The replayed parent is the parent with the table, which agrees with the cache.
      have heval := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hparent
      rw [evalWithAnswerFn_combineM] at heval
      simp only [Cryptography.Merkle.climbPairs, List.mem_cons] at hx
      rcases hx with rfl | hx
      · -- This level queried its pair, so the cache holds the answer of the table.
        simp only [combineM, simulateQ_bind] at hparent
        obtain ⟨_, hquery, -⟩ := Option.bind_eq_some_iff.mp hparent
        obtain ⟨digest, hdigest⟩ := cached_of_queryHash hquery
        rw [hdigest, hf hdigest]
      · rw [← heval] at hrun
        exact ih (level + 1) (j / 2) _ hrun x hx
  intro x hx
  simp only [branchMessages, List.mem_map] at hx
  obtain ⟨pair, hpair, rfl⟩ := hx
  exact climbed branch level (index >>> level) node hrun pair hpair

/-- A replayed winning branch extraction exposes a collision of the cache.

The search over the two climbs finds it, run with a table that extends the cache. -/
theorem collision_of_extractBranches {depth : Nat} {cache : HashOracle.QueryCache}
    {claim : BranchClaim} {outcome : BranchOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractBranches queryHash depth claim) = some outcome)
    (hwins : BranchWins depth outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed climb.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  simp only [extractBranches, evalWithAnswerFn_bind, evalWithAnswerFn_climbBranchM,
    evalWithAnswerFn_pure] at hout
  subst hout
  obtain ⟨hleaves, hfirst, hsecond, root, hroot₁, hroot₂⟩ := hwins
  dsimp only at hleaves hfirst hsecond hroot₁ hroot₂
  rw [toChunk_ok_iff] at hroot₁ hroot₂
  -- Under the table, the leaves are equal, or the search over the two climbs finds a collision.
  rcases climbBranchM_binding (tableHash f) (by simp [hfirst, hsecond])
      (hroot₁.trans hroot₂.symm) with hsame | hfound
  · exact absurd (Vector.toArray_inj.mp hsame) hleaves
  · obtain ⟨⟨a, b⟩, hab⟩ := Option.isSome_iff_exists.mp hfound
    -- Every leaf and every branch node is a 32-byte vector.
    have widths : ∀ (nodes : List (Vector UInt8 32)),
        ∀ node ∈ nodes.map Vector.toArray, node.size = bytesPerChunk := by
      intro nodes node member
      obtain ⟨vector, -, rfl⟩ := List.mem_map.mp member
      exact vector.size_toArray
    obtain ⟨-, -, hdistinct, hequal⟩ := findBranchCollision_valid_of_width (tableHash f)
      (tableHash_size f) (by simp) (by simp) (widths _) (widths _) hab
    obtain ⟨ha, hb⟩ := findBranchCollision_mem hab
    -- Both climbs were replayed, so the cache gives their messages the answers of the table.
    simp only [extractBranches, simulateQ_bind] at hrun
    obtain ⟨_, hrun₁, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨_, hrun₂, -⟩ := Option.bind_eq_some_iff.mp hrun
    exact collision_of_cached hdistinct hequal (cached_of_climbBranchM hf hrun₁ a ha)
      (cached_of_climbBranchM hf hrun₂ b hb)

/-- Two different leaves at one index with one root, at probability at most `Q^2 / N`.

A win needs both branches to have `depth` nodes, and `N` is the number of digests.

The roots are computed with the oracle as the node hash.

`Q` bounds the oracle calls of the whole experiment, repeats included.

The extraction climbs each branch with one call per node, so it adds at most `2 * depth` calls.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_branchWins_le [SampleableType Hash32] (depth : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) BranchClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractBranches queryHash depth) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBranches queryHash depth) adversary)).run ∅}[BranchWins depth z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  prEvent_experimentWith_le (extractBranches queryHash depth) (BranchWins depth)
    collision_of_extractBranches adversary hQ

/-- The same bound for 32 uniform bytes per answer: probability at most `Q^2 / 2^256`. -/
theorem prEvent_branchWins_le_two_pow (depth : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) BranchClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractBranches queryHash depth) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBranches queryHash depth) adversary)).run ∅}[BranchWins depth z.1] ≤
      Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_branchWins_le depth adversary hQ
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- With SHA-256 in the identity monad, the extraction climbs as the branch check does. -/
theorem extractBranches_sha256 (depth : Nat) (claim : BranchClaim) :
    (extractBranches (m := Id) Cryptography.Hash.Sha256.hash depth claim).run =
      ⟨claim, toChunk (climbBranch claim.index 0 claim.firstLeaf.toArray
          ((claim.firstBranch.take depth).map Vector.toArray)),
        toChunk (climbBranch claim.index 0 claim.secondLeaf.toArray
          ((claim.secondBranch.take depth).map Vector.toArray))⟩ :=
  rfl

/-- With SHA-256 as the node hash, a win is two valid branches of two different leaves.

The two branches have one depth, one index and one root.

The roots of the outcome are then computed with SHA-256, not with the oracle.

The step from SHA-256 to the oracle is the idealisation of the model, not a theorem. -/
theorem branchWins_sha256_iff {depth : Nat} {claim : BranchClaim} :
    BranchWins depth (extractBranches (m := Id) Cryptography.Hash.Sha256.hash depth claim).run ↔
      claim.firstLeaf ≠ claim.secondLeaf ∧ ∃ root,
        isValidMerkleBranch claim.firstLeaf claim.firstBranch depth claim.index root = true ∧
        isValidMerkleBranch claim.secondLeaf claim.secondBranch depth claim.index root = true := by
  rw [extractBranches_sha256]
  simp only [BranchWins, isValidMerkleBranch_eq_true_iff, toChunk_ok_iff]
  -- A branch of `depth` nodes keeps all of them, so the extraction climbs the whole branch.
  constructor
  · rintro ⟨differ, firstCount, secondCount, root, firstClimbed, secondClimbed⟩
    rw [List.take_of_length_le firstCount.le] at firstClimbed
    rw [List.take_of_length_le secondCount.le] at secondClimbed
    exact ⟨differ, root, ⟨firstCount, firstClimbed⟩, secondCount, secondClimbed⟩
  · rintro ⟨differ, root, ⟨firstCount, firstClimbed⟩, secondCount, secondClimbed⟩
    refine ⟨differ, firstCount, secondCount, root, ?_, ?_⟩
    · rw [List.take_of_length_le firstCount.le]
      exact firstClimbed
    · rw [List.take_of_length_le secondCount.le]
      exact secondClimbed

end EthLib.Serialization.Ssz.RandomOracle

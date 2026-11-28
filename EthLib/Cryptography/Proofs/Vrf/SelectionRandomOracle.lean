module

public import EthLib.Cryptography.Proofs.Vrf.Oracle
public import EthLib.Cryptography.Proofs.Vrf.Verify
public import EthLib.Cryptography.Proofs.Vrf.Selection
public import EthLib.Cryptography.Proofs.Merkle.QueryBound
public import EthLib.Cryptography.Proofs.Merkle.RandomOracle.Collision

/-!
# Proofs: the collision search of a selection in the random oracle model

One term of the selection bound is the chance that its collision search finds a pair.

This module bounds that chance in an experiment of its own, with the tree hash one random oracle.

The selection bound takes the tree hash as Keccak-256 itself, and no theorem composes the two.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants
open OracleSpec OracleComp ENNReal
open EthLib.Cryptography.Merkle.RandomOracle (Collision collision_of_replay_findCollision
  experimentWith experimentWith_queryBound prEvent_experimentWith_le)

/-! ## The experiment -/

/-- What the adversary outputs: the secrets of a tree, an index, and an opening at that index. -/
structure SelectionClaim where
  /-- The secrets of the tree. -/
  secrets : UInt32 → Digest
  /-- The index of the opening. -/
  index : UInt32
  /-- The opening that the adversary returns at that index. -/
  revealed : Opening

/-- The search of an opening against the honest one, with `H` in place of Keccak-256. -/
def extractCollision {m : Type → Type} [Monad m] (H : ByteArray → m Digest)
    (claim : SelectionClaim) : m (Option (ByteArray × ByteArray)) := do
  -- The honest opening of the tree at the index.
  let honest ← openingWith H claim.secrets claim.index
  -- The collision search of the two openings, with each hash a call to `H`.
  searchHashCollisionWith H claim.index claim.revealed honest

/-- With any function as the hash, the extraction is the collision search with that function.

That search compares the opening with the honest opening that the function builds, at the index. -/
theorem extractCollision_pure (H : ByteArray → Digest) (claim : SelectionClaim) :
    (extractCollision (m := Id) (fun x => pure (H x)) claim).run =
      findHashCollisionWith H claim.index claim.revealed
        (openingWith (m := Id) (fun x => pure (H x)) claim.secrets claim.index).run :=
  -- In the identity monad each hash call is a value, so both sides are one search of two climbs.
  rfl

/-- With Keccak-256 as the hash, the extraction is the search of the selection bound.

That search compares the opening with the honest opening of the specification, at the index. -/
theorem extractCollision_keccak256 (claim : SelectionClaim) :
    (extractCollision (m := Id) (fun x => pure (hash x)) claim).run =
      findHashCollision claim.index claim.revealed (opening claim.secrets claim.index) :=
  extractCollision_pure hash claim

/-- A run of the selection game collides exactly when the extraction finds a pair.

The extraction runs with Keccak-256, on the secrets, the index and the opening of the run. -/
theorem Selection.collides_iff_extractCollision (z : Selection) :
    z.Collides ↔ (extractCollision (m := Id) (fun x => pure (hash x))
      ⟨z.secrets, z.index, z.revealed⟩).run.isSome := by
  rw [extractCollision_keccak256]
  rfl

/-! ## The search replayed from a cache -/

/-- A replayed extraction that finds a pair exposes a collision of the cache.

The pair is two node inputs of one level of the search, or else the two leaf inputs. -/
theorem collision_of_extractCollision {cache : HashSpec.QueryCache} {claim : SelectionClaim}
    {found : Option (ByteArray × ByteArray)}
    (hrun : simulateQ cache.toPartialImpl (extractCollision oracleHash claim) = some found)
    (hfound : found.isSome) : Collision cache := by
  -- The replay ran the honest opening, the two leaf hashes, then the search, each from the cache.
  simp only [extractCollision, searchHashCollisionWith, simulateQ_bind] at hrun
  obtain ⟨honest, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨leaf, hleaf, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨leaf', hleaf', hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨search, hsearch, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [simulateQ_pure] at hrun
  obtain rfl := Option.some.inj hrun
  -- Each leaf hash read the answer of its leaf input from the cache.
  simp only [oracleHash, simulateQ_spec_query, QueryCache.toPartialImpl_apply] at hleaf hleaf'
  cases search with
  | some c =>
    -- The replayed search stopped at a level whose two node inputs share one cached answer.
    exact collision_of_replay_findCollision (input := fun _ left right => nodeInput left right)
      (fun _ _ _ _ h => by
        simpa only [nodeWith, oracleHash, simulateQ_spec_query, QueryCache.toPartialImpl_apply]
          using h)
      (fun _ _ _ _ _ h => nodeInput_inj.mp h) _ _ _ _ _ c hsearch
  | none =>
    -- The search found no node pair, so the pair is the two leaf inputs.
    by_cases hleaves : claim.revealed.secret ≠ honest.secret ∧ leaf = leaf'
    · -- Two different secrets give two different leaf inputs, read with one cached answer.
      refine ⟨leafInput claim.revealed.secret, leafInput honest.secret, leaf,
        fun he => hleaves.1 (leafInput_inj.mp he), hleaf, ?_⟩
      rw [hleaves.2]
      exact hleaf'
    · simp [hleaves] at hfound

/-! ## The search with answered hashes -/

/-- Run with answers that give each hash the value `G`, the extraction is the one over `G`. -/
theorem simulateQ_extractCollision_of_pure {ι : Type} {spec : OracleSpec ι} {r : Type → Type}
    [Monad r] [LawfulMonad r] (impl : QueryImpl spec r) {H : ByteArray → OracleComp spec Digest}
    {G : ByteArray → Digest} (hH : ∀ x, simulateQ impl (H x) = pure (G x))
    (claim : SelectionClaim) :
    simulateQ impl (extractCollision H claim) =
      pure (extractCollision (m := Id) (fun x => pure (G x)) claim).run := by
  -- The honest opening runs to the honest opening over `G`.
  have hopen : simulateQ impl (openingWith H claim.secrets claim.index) =
      pure (openingWith (m := Id) (fun x => pure (G x)) claim.secrets claim.index).run := by
    simp only [openingWith, simulateQ_bind, simulateQ_pure, pure_bind, Id.run_bind, Id.run_pure,
      Merkle.simulateQ_path_of_pure impl (nodeWith H) (leafWith H claim.secrets)
        (fun _ left right => G (nodeInput left right))
        (fun j => G (leafInput (claim.secrets (UInt32.ofNat j)))) (fun _ _ _ => hH _)
        (fun _ => hH _)]
    rfl
  -- Then the two leaves and the search run over `G`.
  simp only [extractCollision, searchHashCollisionWith, simulateQ_bind, simulateQ_pure, hopen, hH,
    pure_bind, Id.run_bind, Id.run_pure, Merkle.simulateQ_findCollision_of_pure impl (nodeWith H)
      (fun _ left right => G (nodeInput left right)) (fun _ _ _ => hH _)]
  rfl

/-! ## The bound -/

section Count

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
  {H : ByteArray → OracleComp spec Digest}

/-- With at most one counted call per hash, the honest opening makes at most `2^(h + 1) - 2` calls.

Here `h` is the height of the tree. -/
theorem isQueryBoundP_openingWith (hleaf : ∀ s, IsQueryBoundP (H (leafInput s)) p 1)
    (hnode : ∀ l r, IsQueryBoundP (H (nodeInput l r)) p 1) (secrets : UInt32 → Digest)
    (i : UInt32) :
    IsQueryBoundP (openingWith H secrets i) p (2 ^ (VRF_TREE_HEIGHT + 1) - 2) := by
  -- A sibling hashes each leaf below it and each node above those leaves, once.
  have hpath := Merkle.isQueryBoundP_siblings (hash := nodeWith H) (leaves := leafWith H secrets)
    (fun _ => hleaf _) (fun _ _ _ => hnode _ _) ⟨0, i.toNat⟩ VRF_TREE_HEIGHT
  unfold openingWith Merkle.path
  exact (isQueryBoundP_bind hpath fun _ _ => isQueryBoundP_pure _ _ 0).mono
    (by simp [VRF_TREE_HEIGHT])

/-- With at most one counted call per hash, the extraction makes at most `2^(h + 1) + 2 h` calls.

Here `h` is the height of the tree. -/
theorem isQueryBoundP_extractCollision (hleaf : ∀ s, IsQueryBoundP (H (leafInput s)) p 1)
    (hnode : ∀ l r, IsQueryBoundP (H (nodeInput l r)) p 1) (claim : SelectionClaim) :
    IsQueryBoundP (extractCollision H claim) p
      (2 ^ (VRF_TREE_HEIGHT + 1) + 2 * VRF_TREE_HEIGHT) := by
  -- The search makes at most two calls per level, and each path has one sibling per level.
  have hsearch : ∀ (honest : Opening) (leaf leaf' : Digest),
      IsQueryBoundP (Merkle.findCollision (nodeWith H) ⟨0, claim.index.toNat⟩ leaf leaf'
        claim.revealed.path.toList honest.path.toList) p (2 * VRF_TREE_HEIGHT) :=
    fun honest leaf leaf' => (Merkle.isQueryBoundP_findCollision (hash := nodeWith H)
      (fun _ _ _ => hnode _ _) claim.revealed.path.toList honest.path.toList
      ⟨0, claim.index.toNat⟩ leaf leaf').mono (by simp)
  unfold extractCollision searchHashCollisionWith
  refine (isQueryBoundP_bind (isQueryBoundP_openingWith hleaf hnode _ _) fun honest _ =>
    isQueryBoundP_bind (hleaf _) fun leaf _ =>
      isQueryBoundP_bind (hleaf _) fun leaf' _ =>
        isQueryBoundP_bind (hsearch honest leaf leaf') fun _ _ =>
          isQueryBoundP_pure _ _ 0).mono ?_
  simp only [VRF_TREE_HEIGHT]
  omega

end Count

/-- The honest opening makes at most `2^(h + 1) - 2` oracle calls, for a tree of height `h`.

Its path has one sibling per level. -/
theorem openingWith_queryBound (secrets : UInt32 → Digest) (i : UInt32) :
    IsQueryBoundP (openingWith oracleHash secrets i) (fun _ => True)
      (2 ^ (VRF_TREE_HEIGHT + 1) - 2) :=
  isQueryBoundP_openingWith (fun _ => oracleHash_queryBound _)
    (fun _ _ => oracleHash_queryBound _) secrets i

/-- The extraction makes at most `2^(h + 1) + 2 h` oracle calls, for a tree of height `h`.

It builds the honest opening, hashes the two leaves, then at most two nodes per level. -/
theorem extractCollision_queryBound (claim : SelectionClaim) :
    IsQueryBoundP (extractCollision oracleHash claim) (fun _ => True)
      (2 ^ (VRF_TREE_HEIGHT + 1) + 2 * VRF_TREE_HEIGHT) :=
  isQueryBoundP_extractCollision (fun _ => oracleHash_queryBound _)
    (fun _ _ => oracleHash_queryBound _) claim

/-- The experiment makes the adversary's calls and at most `2^(h + 1) + 2 h` more.

Here `h` is the height of the tree. -/
theorem experimentWith_extractCollision_queryBound
    {adversary : OracleComp (unifSpec + HashSpec) SelectionClaim} {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    IsQueryBoundP (experimentWith (extractCollision oracleHash) adversary)
      (fun t => t.isRight = true) (q + (2 ^ (VRF_TREE_HEIGHT + 1) + 2 * VRF_TREE_HEIGHT)) :=
  experimentWith_queryBound hq extractCollision_queryBound

/-- The search finds a pair against the honest opening with probability at most `Q^2 / N`.

`N` is the number of digests, and `Q` bounds the classical oracle calls of the whole experiment.

Those are the calls of the adversary, of the honest opening and of the search.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_extractCollision_isSome_le [SampleableType Digest]
    (adversary : OracleComp (unifSpec + HashSpec) SelectionClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractCollision oracleHash) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashSpec.romImpl
      (experimentWith (extractCollision oracleHash) adversary)).run ∅}[z.1.isSome] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card Digest) :=
  -- Each found pair is two different queried inputs with one answer, so the birthday bound applies.
  prEvent_experimentWith_le (extractCollision oracleHash) (fun found => found.isSome)
    collision_of_extractCollision adversary hQ

/-- The same bound for 32 uniform bytes per answer: probability at most `Q^2 / 2^256`. -/
theorem prEvent_extractCollision_isSome_le_two_pow
    (adversary : OracleComp (unifSpec + HashSpec) SelectionClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractCollision oracleHash) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashSpec.romImpl
      (experimentWith (extractCollision oracleHash) adversary)).run ∅}[z.1.isSome] ≤
      Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_extractCollision_isSome_le adversary hQ
  rw [natCard_digest, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- The same bound with the adversary's classical oracle calls `q` counted alone.

The search finds a pair with probability at most `(q + 2^(h + 1) + 2 h)^2 / 2^256`.

Here `h = 32` is the height of the tree, so the experiment adds at most `2^33 + 64` calls. -/
theorem prEvent_extractCollision_isSome_le_of_adversary
    (adversary : OracleComp (unifSpec + HashSpec) SelectionClaim) {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashSpec.romImpl
      (experimentWith (extractCollision oracleHash) adversary)).run ∅}[z.1.isSome] ≤
      (q + (2 ^ (VRF_TREE_HEIGHT + 1) + 2 * VRF_TREE_HEIGHT) : Nat) *
        (((q + (2 ^ (VRF_TREE_HEIGHT + 1) + 2 * VRF_TREE_HEIGHT) : Nat) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_extractCollision_isSome_le_two_pow adversary
    (experimentWith_extractCollision_queryBound hq)

end EthLib.Cryptography.Vrf

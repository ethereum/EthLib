module

public import EthLib.Cryptography.Proofs.Vrf.Unpredictability
public import EthLib.Cryptography.Proofs.Merkle.QueryBound
public import EthLib.Cryptography.Proofs.Merkle.RandomOracle.Collision

/-!
# Proofs: one output per index in the random oracle model

This module bounds the chance that an adversary opens one index of a root to two outputs.

The hash is one random oracle on byte strings, for the leaves, the nodes and the outputs.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants
open OracleSpec OracleComp ENNReal
open EthLib.Cryptography.Merkle.RandomOracle (Collision experimentWith experimentWith_queryBound
  prEvent_experimentWith_le)

/-! ## The check with the hash as an oracle -/

/-- One call to the hash oracle, the only oracle that the extraction calls. -/
def oracleHash (x : ByteArray) : OracleComp HashSpec Digest :=
  liftM (HashSpec.query x)

/-- The check of an opening at index `i` against a root, with `H` in place of Keccak-256.

It returns the output at `i`, or nothing if the opening is invalid. -/
def verifyWith {m : Type → Type} [Monad m] (H : ByteArray → m Digest) (root : Digest)
    (i : UInt32) (o : Opening) : m (Option Digest) := do
  -- The leaf commits to the secret.
  let leaf ← H (leafInput o.secret)
  -- The opening is valid when its path leads from that leaf to the root.
  let top ← Merkle.climb (nodeWith H) ⟨0, i.toNat⟩ leaf o.path.toList
  if top = root then
    let output ← H (outputInput i o.secret)
    return some output
  else
    return none

/-- With Keccak-256 as `H`, the check is the check of the specification. -/
theorem verifyWith_hash (root : Digest) (i : UInt32) (o : Opening) :
    (verifyWith (m := Id) (fun x => pure (hash x)) root i o).run = verify root i o :=
  rfl

/-! ## The experiment -/

/-- What the adversary outputs: a root, an index, and two openings at that index. -/
structure OpeningsClaim where
  /-- The root that both openings must verify against. -/
  root : Digest
  /-- The index of both openings. -/
  index : UInt32
  /-- The first opening. -/
  first : Opening
  /-- The second opening. -/
  second : Opening

/-- What the experiment reports: the claim and the outputs of its two openings. -/
structure OpeningsOutcome where
  /-- The root, the index and the openings of the adversary. -/
  claim : OpeningsClaim
  /-- The output of the first opening, or nothing if it is invalid. -/
  firstOutput : Option Digest
  /-- The output of the second opening, or nothing if it is invalid. -/
  secondOutput : Option Digest

/-- The extraction for two openings, with `H` in place of Keccak-256.

It checks both openings at the index against the root, as verification does. -/
def extractOutputs {m : Type → Type} [Monad m] (H : ByteArray → m Digest)
    (claim : OpeningsClaim) : m OpeningsOutcome := do
  let firstOutput ← verifyWith H claim.root claim.index claim.first
  let secondOutput ← verifyWith H claim.root claim.index claim.second
  return ⟨claim, firstOutput, secondOutput⟩

/-- The adversary wins: both openings verify, with two different outputs. -/
def OutputsWin (outcome : OpeningsOutcome) : Prop :=
  ∃ y y', outcome.firstOutput = some y ∧ outcome.secondOutput = some y' ∧ y ≠ y'

/-- With Keccak-256 as the hash, a win is two openings that verify with two different outputs.

Both openings verify at the claimed index under the claimed root.

The step from Keccak-256 to the oracle is the idealisation of the model, not a theorem. -/
theorem outputsWin_keccak256_iff {claim : OpeningsClaim} :
    OutputsWin (extractOutputs (m := Id) (fun x => pure (hash x)) claim).run ↔
      ∃ y y', verify claim.root claim.index claim.first = some y ∧
        verify claim.root claim.index claim.second = some y' ∧ y ≠ y' := by
  simp only [OutputsWin, extractOutputs, Id.run_bind, Id.run_pure, verifyWith_hash]

/-! ## The check replayed from a cache -/

/-- A check, run against a full answer table, is the check with that table as the hash. -/
theorem evalWithAnswerFn_verifyWith (f : QueryImpl HashSpec Id) (root : Digest) (i : UInt32)
    (o : Opening) :
    evalWithAnswerFn f (verifyWith oracleHash root i o) =
      (verifyWith (m := Id) (fun x => pure (f x)) root i o).run := by
  -- Answering each call from the table commutes with the climb.
  have hclimb : ∀ (t : List Digest) (p : Merkle.Position) (b : Digest),
      evalWithAnswerFn f (Merkle.climb (nodeWith oracleHash) p b t) =
        (Merkle.climb (nodeWith (m := Id) (fun x => pure (f x))) p b t).run :=
    Merkle.climb_map_monad (nodeWith oracleHash)
      (fun {β} (x : OracleComp HashSpec β) => (evalWithAnswerFn f x : Id β))
      (fun _ => rfl) (fun _ _ => evalWithAnswerFn_bind _ _ _)
  simp only [verifyWith, evalWithAnswerFn_bind, oracleHash, evalWithAnswerFn_liftM_query,
    hclimb, Id.run_bind, Id.run_pure]
  split <;> rfl

/-- A replayed climb caches the node input of each pair it hashes, with the table's answer.

It assumes that the table agrees with the cache. -/
theorem cached_of_climb {cache : HashSpec.QueryCache} {f : QueryImpl HashSpec Id}
    (hf : cache.AgreesWithFn f) (t : List Digest) :
    ∀ (p : Merkle.Position) (b : Digest) {top : Digest},
      simulateQ cache.toPartialImpl (Merkle.climb (nodeWith oracleHash) p b t) = some top →
      ∀ x ∈ Merkle.climbPairs (nodeWith (m := Id) (fun x => pure (f x))) p b t,
        cache (nodeInput x.1 x.2) = some (f (nodeInput x.1 x.2)) := by
  induction t with
  | nil =>
    intro _ _ _ _ x hx
    simp [Merkle.climbPairs] at hx
  | cons v t ih =>
    intro p b top hrun x hx
    simp only [Merkle.climb, simulateQ_bind] at hrun
    obtain ⟨parent, hparent, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    -- The replay read the parent from the cache, so the table gives the same parent.
    simp only [nodeWith, oracleHash, simulateQ_spec_query, QueryCache.toPartialImpl_apply]
      at hparent
    simp only [Merkle.climbPairs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [hparent, hf hparent]
    · rw [← hf hparent] at hrun
      exact ih p.parent _ hrun x hx

/-- A replayed check caches its leaf input and the node input of each pair its climb hashes.

The cached answers are those of the table, when the table agrees with the cache. -/
theorem cached_of_verifyWith {cache : HashSpec.QueryCache} {f : QueryImpl HashSpec Id}
    (hf : cache.AgreesWithFn f) {root : Digest} {i : UInt32} {o : Opening} {r : Option Digest}
    (hrun : simulateQ cache.toPartialImpl (verifyWith oracleHash root i o) = some r) :
    cache (leafInput o.secret) = some (f (leafInput o.secret)) ∧
      ∀ x ∈ Merkle.climbPairs (nodeWith (m := Id) (fun x => pure (f x))) ⟨0, i.toNat⟩
          (f (leafInput o.secret)) o.path.toList,
        cache (nodeInput x.1 x.2) = some (f (nodeInput x.1 x.2)) := by
  simp only [verifyWith, simulateQ_bind] at hrun
  obtain ⟨leaf, hleaf, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨top, htop, -⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [oracleHash, simulateQ_spec_query, QueryCache.toPartialImpl_apply] at hleaf
  -- The replayed leaf is the table's leaf, so the climb starts from it.
  rw [← hf hleaf] at htop
  exact ⟨by rw [hleaf, hf hleaf], cached_of_climb hf _ _ _ htop⟩

/-- With a table as the hash, an opening verifies only when its climb reaches the root.

Its output is then the table's answer at its output input. -/
private theorem verifyWith_eq_some {f : QueryImpl HashSpec Id} {root : Digest} {i : UInt32}
    {o : Opening} {y : Digest}
    (h : (verifyWith (m := Id) (fun x => pure (f x)) root i o).run = some y) :
    (Merkle.climb (nodeWith (m := Id) (fun x => pure (f x))) ⟨0, i.toNat⟩
        (f (leafInput o.secret)) o.path.toList).run = root ∧
      y = f (outputInput i o.secret) := by
  simp only [verifyWith, Id.run_bind, Id.run_pure] at h
  split at h
  · next hc =>
    exact ⟨hc, (Option.some.inj h).symm⟩
  · cases h

/-- A replayed winning extraction exposes a collision of the cache.

The collision search with a table that extends the cache finds it. -/
theorem collision_of_extractOutputs {cache : HashSpec.QueryCache} {claim : OpeningsClaim}
    {outcome : OpeningsOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractOutputs oracleHash claim) = some outcome)
    (hwins : OutputsWin outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed check.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  simp only [extractOutputs, evalWithAnswerFn_bind, evalWithAnswerFn_verifyWith,
    evalWithAnswerFn_pure] at hout
  subst hout
  obtain ⟨y, y', hy, hy', hne⟩ := hwins
  dsimp only at hy hy'
  obtain ⟨hroot, rfl⟩ := verifyWith_eq_some hy
  obtain ⟨hroot', rfl⟩ := verifyWith_eq_some hy'
  -- Both checks were replayed, so the cache holds their inputs with the table's answers.
  simp only [extractOutputs, simulateQ_bind] at hrun
  obtain ⟨_, hrun₁, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, hrun₂, -⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨hleaf₁, hnodes₁⟩ := cached_of_verifyWith hf hrun₁
  obtain ⟨hleaf₂, hnodes₂⟩ := cached_of_verifyWith hf hrun₂
  -- Two different cached inputs with one answer of the table are a collision of the cache.
  have hcollision : ∀ {a b : ByteArray}, cache a = some (f a) → cache b = some (f b) →
      a ≠ b → f a = f b → Collision cache := fun ha hb hab heq =>
    ⟨_, _, _, hab, ha, hb.trans (congrArg some heq.symm)⟩
  -- Two different outputs come from two different secrets, so the search finds a collision.
  rcases secret_unique_of_climb_eq (H := fun x => f x) (i := claim.index) (o := claim.first)
      (o' := claim.second) (hroot.trans hroot'.symm) with hs | ⟨pair, hpair, hdistinct, hequal⟩
  · exact absurd (congrArg (fun s => f (outputInput claim.index s)) hs) hne
  unfold findHashCollisionWith at hpair
  split at hpair
  · -- Two node inputs, each of a pair that its own climb hashes.
    next c hc =>
    cases hpair
    obtain ⟨hx, hy⟩ := Merkle.findCollision_mem_climbPairs _ hc
    exact hcollision (hnodes₁ _ hx) (hnodes₂ _ hy) hdistinct hequal
  · -- The two leaf inputs.
    split at hpair
    · cases hpair
      exact hcollision hleaf₁ hleaf₂ hdistinct hequal
    · cases hpair

/-! ## The bound -/

/-- A check makes at most `h + 2` oracle calls, for a tree of height `h`.

It hashes the leaf, one node per sibling, and the output. -/
theorem verifyWith_queryBound (root : Digest) (i : UInt32) (o : Opening) :
    IsQueryBoundP (verifyWith oracleHash root i o) (fun _ => True) (VRF_TREE_HEIGHT + 2) := by
  have hcall : ∀ x, IsQueryBoundP (oracleHash x) (fun _ => True) 1 := fun x => by
    simp [oracleHash]
  -- The climb makes one call per sibling, and the path has one sibling per level.
  have hclimb : ∀ leaf, IsQueryBoundP (Merkle.climb (nodeWith oracleHash) ⟨0, i.toNat⟩ leaf
      o.path.toList) (fun _ => True) VRF_TREE_HEIGHT := fun leaf =>
    (Merkle.isQueryBoundP_climb (hash := nodeWith oracleHash) (fun _ _ _ => hcall _)
      o.path.toList ⟨0, i.toNat⟩ leaf).mono (by simp)
  unfold verifyWith
  refine (isQueryBoundP_bind (hcall _) fun leaf _ =>
    isQueryBoundP_bind (m := 1) (hclimb leaf) fun top _ => ?_).mono (by omega)
  split
  · exact (isQueryBoundP_bind (hcall _) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)
  · exact isQueryBoundP_pure _ _ _

/-- The extraction makes at most `2 (h + 2)` oracle calls, for a tree of height `h`. -/
theorem extractOutputs_queryBound (claim : OpeningsClaim) :
    IsQueryBoundP (extractOutputs oracleHash claim) (fun _ => True)
      (2 * (VRF_TREE_HEIGHT + 2)) :=
  (isQueryBoundP_bind (verifyWith_queryBound _ _ _) fun _ _ =>
    isQueryBoundP_bind (verifyWith_queryBound _ _ _) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by omega)

/-- The experiment makes the adversary's oracle calls and at most `2 (h + 2)` more.

Here `h` is the height of the tree. -/
theorem experimentWith_extractOutputs_queryBound
    {adversary : OracleComp (unifSpec + HashSpec) OpeningsClaim} {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    IsQueryBoundP (experimentWith (extractOutputs oracleHash) adversary)
      (fun t => t.isRight = true) (q + 2 * (VRF_TREE_HEIGHT + 2)) :=
  experimentWith_queryBound hq extractOutputs_queryBound

/-- Two different outputs at one index under one root, with probability at most `Q^2 / N`.

`N` is the number of digests, and `Q` bounds the oracle calls of the whole experiment.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_outputsWin_le [SampleableType Digest]
    (adversary : OracleComp (unifSpec + HashSpec) OpeningsClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractOutputs oracleHash) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashSpec.romImpl
      (experimentWith (extractOutputs oracleHash) adversary)).run ∅}[OutputsWin z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card Digest) :=
  -- Each win exposes two different queried inputs with one answer, so the birthday bound applies.
  prEvent_experimentWith_le (extractOutputs oracleHash) OutputsWin collision_of_extractOutputs
    adversary hQ

/-- The same bound for 32 uniform bytes per answer: probability at most `Q^2 / 2^256`. -/
theorem prEvent_outputsWin_le_two_pow
    (adversary : OracleComp (unifSpec + HashSpec) OpeningsClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractOutputs oracleHash) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashSpec.romImpl
      (experimentWith (extractOutputs oracleHash) adversary)).run ∅}[OutputsWin z.1] ≤
      Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_outputsWin_le adversary hQ
  rw [natCard_digest, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- The same bound with the adversary's oracle calls `q` counted alone.

A win has probability at most `(q + 2 (h + 2))^2 / 2^256`, for a tree of height `h = 32`. -/
theorem prEvent_outputsWin_le_of_adversary
    (adversary : OracleComp (unifSpec + HashSpec) OpeningsClaim) {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashSpec.romImpl
      (experimentWith (extractOutputs oracleHash) adversary)).run ∅}[OutputsWin z.1] ≤
      (q + 2 * (VRF_TREE_HEIGHT + 2) : Nat) *
        (((q + 2 * (VRF_TREE_HEIGHT + 2) : Nat) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_outputsWin_le_two_pow adversary (experimentWith_extractOutputs_queryBound hq)

end EthLib.Cryptography.Vrf

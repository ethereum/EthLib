module

public import EthLib.Execution.Proofs.Blocks.Roots
public import EthLib.Execution.Proofs.Trie.RandomOracle

/-!
# Proofs: the root of a list in the random oracle model

The hash is modelled as one random oracle, as for the root of one trie.

An adversary wins when it outputs two different lists with one root.

The birthday bound of the oracle bounds the probability that it wins.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2.

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Execution.Blocks.RandomOracle

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Execution.Trie.RandomOracle
open EthLib.Serialization.Rlp
open OracleComp OracleSpec ENNReal
open EthLib.Cryptography (evalWithAnswerFn_exceptT_bind evalWithAnswerFn_exceptT_liftExcept)
open EthLib.Cryptography.Merkle.RandomOracle (Collision collision_of_cached experimentWith
  prEvent_experimentWith_le card_bytes32)

/-- The root of a list, run against a table, is its root with that table as the hash. -/
theorem evalWithAnswerFn_indexedRootM (f : QueryImpl HashOracle Id) (values : List ByteArray) :
    evalWithAnswerFn f (indexedRootM queryHash values).run =
      (indexedRootM (m := Id) (fun x => f x) values).run := by
  rw [indexedRootM_eq]
  simp only [indexedRootM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_liftExcept,
    evalWithAnswerFn_rootM]
  rfl

/-- Queries every input of the indexed search: the binding inputs at the key of each index.

Lists whose entries do not encode have no root, and need no query. -/
def queryIndexedWitnesses (first second : List ByteArray) : OracleComp HashOracle Unit :=
  match indexedEntries first, indexedEntries second with
  | .ok entries₁, .ok entries₂ =>
    (List.range (max first.length second.length)).forM fun i =>
      match Codec.encode i with
      | .ok key => queryWitnesses ⟨false, entries₁⟩ ⟨false, entries₂⟩ key
      | .error _ => pure ()
  | _, _ => pure ()

/-- What the experiment reports: the two lists and their roots under the oracle. -/
structure IndexedOutcome where
  /-- The first list of the adversary. -/
  first : List ByteArray
  /-- The second list of the adversary. -/
  second : List ByteArray
  /-- The root of the first list under the oracle. -/
  firstRoot : Except TrieError Hash32
  /-- The root of the second list under the oracle. -/
  secondRoot : Except TrieError Hash32

/-- The part of the experiment after the adversary, which only calls the hash oracle.

It computes both roots, then queries every input of the indexed search. -/
def extractIndexed (first second : List ByteArray) : OracleComp HashOracle IndexedOutcome := do
  let firstRoot ← (indexedRootM queryHash first).run
  let secondRoot ← (indexedRootM queryHash second).run
  queryIndexedWitnesses first second
  return ⟨first, second, firstRoot, secondRoot⟩

/-- The experiment: the adversary picks two lists, then the extraction runs. -/
def indexedExperiment
    (adversary : OracleComp (unifSpec + HashOracle) (List ByteArray × List ByteArray)) :
    OracleComp (unifSpec + HashOracle) IndexedOutcome :=
  experimentWith (fun claim => extractIndexed claim.1 claim.2) adversary

/-- The adversary wins: two different lists have one root. -/
def IndexedWins (outcome : IndexedOutcome) : Prop :=
  (∃ root, outcome.firstRoot = .ok root ∧ outcome.secondRoot = .ok root) ∧
    outcome.first ≠ outcome.second

/-- A replayed query of the indexed witnesses caches both inputs of each pair the search returns.

So each such pair, under a table that agrees with the cache, is a collision of the cache. -/
theorem collision_of_queryIndexedWitnesses {cache : HashOracle.QueryCache}
    {f : QueryImpl HashOracle Id} (hf : cache.AgreesWithFn f) {first second : List ByteArray}
    {u : Unit} (hrun : simulateQ cache.toPartialImpl (queryIndexedWitnesses first second) = some u)
    {pair : ByteArray × ByteArray}
    (hfind : findIndexedCollision (fun x => f x) first second = some pair) : Collision cache := by
  unfold findIndexedCollision at hfind
  unfold queryIndexedWitnesses at hrun
  split at hfind
  · rename_i entries₁ entries₂ h₁ h₂
    simp only [h₁, h₂] at hrun
    obtain ⟨i, hi, hfound⟩ := List.exists_of_findSome?_eq_some hfind
    obtain ⟨_, hstep⟩ := replay_forM _ _ hrun i hi
    split at hfound
    · -- The search returns two nodes of the proofs of the index's key, which the replay cached.
      rename_i key hkey
      simp only [hkey] at hstep
      have hcached := cached_of_queryWitnesses hf hstep
      obtain ⟨hmem₁, hmem₂⟩ := mem_witnesses_of_findCollision _ hfound
      obtain ⟨hne, heq⟩ := findCollision_valid _ hfound
      exact collision_of_cached hne heq (hcached _ hmem₁) (hcached _ hmem₂)
    · cases hfound
  · cases hfind

/-- A replayed winning extraction exposes a collision of the cache. -/
theorem collision_of_extractIndexed {cache : HashOracle.QueryCache} {first second : List ByteArray}
    {outcome : IndexedOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractIndexed first second) = some outcome)
    (hwins : IndexedWins outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  simp only [extractIndexed, simulateQ_bind] at hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, hwitnesses, -⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [extractIndexed, evalWithAnswerFn_bind, evalWithAnswerFn_indexedRootM,
    evalWithAnswerFn_pure] at hout
  subst hout
  obtain ⟨⟨root', hroot₁, hroot₂⟩, hne⟩ := hwins
  -- Two different lists with one root leave the search a collision.
  rcases indexedRootM_binding (fun x => f x) hroot₁ hroot₂ with heq | ⟨_, hfind, -⟩
  · exact absurd heq hne
  · exact collision_of_queryIndexedWitnesses hf hwitnesses hfind

/-- Two different lists with one root: probability at most `Q^2 / 2^256`.

Each answer of the oracle is 32 uniform bytes. -/
theorem prEvent_indexedWins_le
    (adversary : OracleComp (unifSpec + HashOracle) (List ByteArray × List ByteArray)) {Q : Nat}
    -- `Q` bounds the oracle calls of the whole experiment, repeats included.
    --
    -- It counts the adversary's calls, the two roots, and the queries at each index.
    --
    -- Each index rebuilds both proofs, so the calls grow as the square of the longer length.
    (hQ : IsQueryBoundP (indexedExperiment adversary) (fun t => t.isRight = true) Q) :
    -- The oracle cache starts empty, and the adversary's private sampling is not counted.
    Pr{let z ← (simulateQ HashOracle.romImpl (indexedExperiment adversary)).run ∅}[
      IndexedWins z.1] ≤ Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_experimentWith_le (fun claim : List ByteArray × List ByteArray =>
    extractIndexed claim.1 claim.2) IndexedWins
    (fun hrun hwins => collision_of_extractIndexed hrun hwins) adversary hQ
  rwa [card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound

end EthLib.Execution.Blocks.RandomOracle

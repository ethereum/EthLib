module

public import EthLib.Execution.Proofs.Trie.RandomOracle
public import EthLib.Execution.Proofs.Trie.RangeComplete

/-!
# Proofs: the node search of the range check in the random oracle model

The range check finds a node of a sent proof by its hash.

An honest answer fails it only when a sent node shares its hash with a different honest node.

With the hash a random oracle, the birthday bound bounds the probability of such a pair.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2.

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Execution.Trie.RandomOracle

open EthLib.Base
open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Merkle.RandomOracle (Collision collision_of_cached experimentWith
  prEvent_experimentWith_le card_bytes32)

/-- The answer recorded for an input, from the list of queried inputs and their answers.

An input that was never queried reads as the zero digest. -/
def answerOf (inputs : List ByteArray) (answers : List Hash32) (x : ByteArray) : Hash32 :=
  (((inputs.zip answers).find? fun entry => entry.1 = x).map Prod.snd).getD default

/-- The answers of a table, recorded for a list of inputs, are the table on each of them. -/
theorem answerOf_map (f : ByteArray → Hash32) {x : ByteArray} :
    (inputs : List ByteArray) → x ∈ inputs → answerOf inputs (inputs.map f) x = f x
  | [], hx => by cases hx
  | y :: rest, hx => by
    by_cases hxy : y = x
    · subst hxy
      simp [answerOf]
    · have hrest : x ∈ rest := (List.mem_cons.mp hx).resolve_left (Ne.symm hxy)
      have ih := answerOf_map f rest hrest
      simpa [answerOf, hxy] using ih

/-- A run of queries on a list, against a table, answers each input with the table. -/
theorem evalWithAnswerFn_mapM_queryHash (f : QueryImpl HashOracle Id) :
    (inputs : List ByteArray) →
      evalWithAnswerFn f (inputs.mapM queryHash) = inputs.map fun x => f x
  | [] => rfl
  | x :: rest => by
    simp only [List.mapM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      evalWithAnswerFn_mapM_queryHash f rest, List.map_cons]
    rfl

/-- What the range experiment reports: the honest nodes, the sent nodes and their answers. -/
structure RangeOutcome where
  /-- The nodes of the honest proofs of the ends of the range. -/
  honest : List ByteArray
  /-- The nodes that the adversary sends as the proof. -/
  proof : List ByteArray
  /-- The answers of the oracle to the honest nodes, then to the sent nodes. -/
  answers : List Hash32

/-- The answer of the oracle to a node of the outcome, as the experiment recorded it. -/
def RangeOutcome.answer (outcome : RangeOutcome) : ByteArray → Hash32 :=
  answerOf (outcome.honest ++ outcome.proof) outcome.answers

/-- The part of the range experiment after the adversary, which only calls the hash oracle.

It builds the proof of each end in the trie, then queries every honest and every sent node. -/
def extractRange (data : List (Hash32 × ByteArray)) (ends : List Hash32)
    (proof : List ByteArray) : OracleComp HashOracle RangeOutcome := do
  -- The range check reads the plain trie of the 32-byte keys.
  let proofs ← ends.mapM fun key =>
    (getProofM queryHash ⟨false, data.map fun entry => (⟨entry.1.toArray⟩, entry.2)⟩
      ⟨key.toArray⟩).run
  -- A proof that fails to build has no node.
  let honest := proofs.flatMap fun nodes => nodes.toOption.getD []
  let answers ← (honest ++ proof).mapM queryHash
  return ⟨honest, proof, answers⟩

/-- The range experiment: the adversary picks the trie, the ends and the sent proof.

Then the extraction runs. -/
def rangeExperiment (adversary :
    OracleComp (unifSpec + HashOracle) (List (Hash32 × ByteArray) × List Hash32 × List ByteArray)) :
    OracleComp (unifSpec + HashOracle) RangeOutcome :=
  experimentWith (fun claim => extractRange claim.1 claim.2.1 claim.2.2) adversary

/-- The adversary wins when the node search, with the answers of the oracle, finds a pair. -/
def RangeWins (outcome : RangeOutcome) : Prop :=
  (findCrossCollision outcome.answer outcome.honest outcome.proof).isSome

/-- A replayed winning range extraction exposes a collision of the cache. -/
theorem collision_of_extractRange {cache : HashOracle.QueryCache}
    {data : List (Hash32 × ByteArray)} {ends : List Hash32} {proof : List ByteArray}
    {outcome : RangeOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractRange data ends proof) = some outcome)
    (hwins : RangeWins outcome) : Collision cache := by
  -- A table that extends the cache gives the replayed answers.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  simp only [extractRange, simulateQ_bind] at hrun
  obtain ⟨proofs, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨answers, hanswers, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [simulateQ_pure] at hrun
  obtain rfl := Option.some.inj hrun
  have hmap := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hanswers
  rw [evalWithAnswerFn_mapM_queryHash] at hmap
  subst hmap
  -- The search returns a sent node and an honest node, both queried, with one answer.
  obtain ⟨pair, hpair⟩ := Option.isSome_iff_exists.mp hwins
  obtain ⟨hsent, hhonest⟩ := mem_of_findCrossCollision _ hpair
  obtain ⟨hne, heq⟩ := findCrossCollision_valid _ hpair
  have hmem₁ := List.mem_append_right (List.flatMap (fun nodes => nodes.toOption.getD []) proofs)
    hsent
  have hmem₂ := List.mem_append_left proof hhonest
  simp only [RangeOutcome.answer, answerOf_map _ _ hmem₁, answerOf_map _ _ hmem₂] at heq
  -- Each queried node is in the cache with the answer of the table.
  have hcached : ∀ x ∈ List.flatMap (fun nodes => nodes.toOption.getD []) proofs ++ proof,
      cache x = some (f x) := fun x hx => by
    obtain ⟨answer, hanswer⟩ := cached_of_mapM_queryHash _ hanswers x hx
    rw [hanswer, hf hanswer]
  exact collision_of_cached hne heq (hcached _ hmem₁) (hcached _ hmem₂)

/-- The node search of the range check finds a pair: probability at most `Q^2 / 2^256`.

Each answer of the oracle is 32 uniform bytes. -/
theorem prEvent_rangeWins_le (adversary :
    OracleComp (unifSpec + HashOracle) (List (Hash32 × ByteArray) × List Hash32 × List ByteArray))
    {Q : Nat}
    -- `Q` bounds the oracle calls of the whole experiment, repeats included.
    --
    -- It counts the adversary's calls, the proofs of the ends, and one call per node.
    --
    -- Building a proof hashes the subtrees on its path, so the calls grow with the trie size.
    (hQ : IsQueryBoundP (rangeExperiment adversary) (fun t => t.isRight = true) Q) :
    -- The oracle cache starts empty, and the adversary's private sampling is not counted.
    Pr{let z ← (simulateQ HashOracle.romImpl (rangeExperiment adversary)).run ∅}[
      RangeWins z.1] ≤ Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_experimentWith_le (fun claim :
      List (Hash32 × ByteArray) × List Hash32 × List ByteArray =>
    extractRange claim.1 claim.2.1 claim.2.2) RangeWins
    (fun hrun hwins => collision_of_extractRange hrun hwins) adversary hQ
  rwa [card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound

end EthLib.Execution.Trie.RandomOracle

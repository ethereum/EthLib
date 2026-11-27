module

public import EthLib.Serialization.Proofs.Ssz.RandomOracle
public import EthLib.Serialization.Proofs.Ssz.Merkle.MultiproofBinding
public import EthLib.Cryptography.Proofs.Merkle.RandomOracle.Multiproof

/-!
# Proofs: two multiproofs of one root in the random oracle model

This module bounds the probability that an adversary opens one request to two lists of leaves.

The adversary picks the request, a list of generalized indices.

A bound on the number of indices and helper indices of the request is fixed before the run.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Serialization.Ssz.RandomOracle

open EthLib.Base
open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Merkle.RandomOracle (Collision experimentWith experimentWith_queryBound
  prEvent_experimentWith_le)

/-- What the adversary outputs: a request, and two multiproofs of it with leaves and helpers. -/
structure MultiproofClaim where
  /-- The generalized indices of the request. -/
  indices : List Nat
  /-- The leaves of the first multiproof, one per index of the request. -/
  firstLeaves : List (Vector UInt8 32)
  /-- The helper nodes of the first multiproof. -/
  firstProof : List (Vector UInt8 32)
  /-- The leaves of the second multiproof, one per index of the request. -/
  secondLeaves : List (Vector UInt8 32)
  /-- The helper nodes of the second multiproof. -/
  secondProof : List (Vector UInt8 32)

/-- What the multiproof experiment reports: the claim and the roots of its two multiproofs. -/
structure MultiproofOutcome where
  /-- The two multiproofs of the adversary. -/
  claim : MultiproofClaim
  /-- The root that the first multiproof rebuilds, if its request is rebuilt and gives one. -/
  firstRoot : Option Bytes
  /-- The root that the second multiproof rebuilds, if its request is rebuilt and gives one. -/
  secondRoot : Option Bytes

/-- The extraction for multiproofs: the roots that both rebuild, with a node hash in any monad.

It rebuilds them as the multiproof check does, from the positions of the request. -/
def extractMultiproofs {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray)
    (size : Nat) (claim : MultiproofClaim) : m MultiproofOutcome :=
  -- A request that the check refuses gives no root.
  match claimPositions claim.indices with
  | .ok (height, opened) =>
    -- So does a request of more than `size` indices and helper indices.
    --
    -- Unlike the check, the rebuild does not count the helper nodes.
    --
    -- Extra ones are dropped, and missing ones give no root.
    if opened.length + (Cryptography.Merkle.helpers height opened).length ≤ size then do
      let firstRoot ← Cryptography.Merkle.verify (fun _ => combineM hash) height opened
        (claim.firstLeaves.map fun node => ⟨node.toArray⟩)
        (claim.firstProof.map fun node => ⟨node.toArray⟩)
      let secondRoot ← Cryptography.Merkle.verify (fun _ => combineM hash) height opened
        (claim.secondLeaves.map fun node => ⟨node.toArray⟩)
        (claim.secondProof.map fun node => ⟨node.toArray⟩)
      return ⟨claim, firstRoot, secondRoot⟩
    else return ⟨claim, none, none⟩
  | .error _ => return ⟨claim, none, none⟩

/-- The adversary wins: two different lists of leaves of its request rebuild one root.

Each list holds one leaf per index of the request. -/
def MultiproofWins (outcome : MultiproofOutcome) : Prop :=
  outcome.claim.firstLeaves ≠ outcome.claim.secondLeaves ∧
    outcome.claim.firstLeaves.length = outcome.claim.indices.length ∧
    outcome.claim.secondLeaves.length = outcome.claim.indices.length ∧
    ∃ root, outcome.firstRoot = some root ∧ outcome.secondRoot = some root

/-- A replayed rebuild is the rebuild with the table, and caches every message it hashes.

It needs the table to agree with the cache. -/
theorem rebuild_go_of_replay_queryHash {cache : HashOracle.QueryCache}
    {f : QueryImpl HashOracle Id} (hf : cache.AgreesWithFn f) {l j : Nat}
    {nodes : List (Cryptography.Merkle.Position × Bytes)} {result : Option Bytes}
    (hrun : simulateQ cache.toPartialImpl
      (Cryptography.Merkle.rebuild.go (fun _ => combineM queryHash) nodes l j) = some result) :
    result = (Cryptography.Merkle.rebuild.go (fun _ => combineM (m := Id) (tableHash f))
        nodes l j).run ∧
      ∀ x ∈ (((Cryptography.Merkle.rebuild.go (Cryptography.Merkle.recordingHash
        (fun _ => combineM (m := Id) (tableHash f)) fun _ a b => a ++ b) nodes l j).run
          []).run).2, cache x = some (f x) := by
  obtain ⟨equal, recorded⟩ := Cryptography.Merkle.RandomOracle.rebuild_go_of_replay
    (Q := fun x => cache x = some (f x)) (fun _ a b parent hparent => by
      -- The replayed parent is the parent with the table, which agrees with the cache.
      have heval := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hparent
      rw [evalWithAnswerFn_combineM] at heval
      -- The node hash queried its message, so the cache holds the answer of the table.
      simp only [combineM] at hparent
      obtain ⟨digest, hdigest⟩ := cached_of_queryHash hparent
      exact ⟨by rw [hdigest, hf hdigest], heval.symm⟩) l j nodes [] hrun
  exact ⟨equal, fun x hx => (recorded x hx).resolve_left (List.not_mem_nil)⟩

/-- A request that passes the checks opens distinct positions that form an antichain in its tree.

These are the conditions of the binding of the Merkle multiproof. -/
private theorem claimPositions_valid {indices : List Nat} {height : Nat}
    {opened : List Cryptography.Merkle.Position}
    (claimed : claimPositions indices = .ok (height, opened)) :
    opened.Nodup ∧
      (∀ a ∈ opened, ∀ b ∈ opened, a.IsAncestor b → a = b) ∧
      (∀ p ∈ opened, (⟨height, 0⟩ : Cryptography.Merkle.Position).IsAncestor p) ∧
      opened.length = indices.length := by
  have accepted : rejectRelated indices = .ok () := by
    cases checked : rejectRelated indices with
    | error fault => simp [claimPositions, checked, Bind.bind, Except.bind] at claimed
    | ok checked => rfl
  rw [claimPositions_ok accepted, Except.ok.injEq, Prod.mk.injEq] at claimed
  obtain ⟨rfl, rfl⟩ := claimed
  refine ⟨?_, rejectRelated_antichain accepted, rejectRelated_inTree accepted, List.length_map _⟩
  -- Two valid indices with one position are one index.
  refine (rejectRelated_nodup accepted).map_on fun a ha b hb same => ?_
  have deepA := log2_le_gindexHeight ha
  have deepB := log2_le_gindexHeight hb
  have := congrArg (positionGindex (gindexHeight indices)) same
  rwa [positionGindex_gindexPosition (by have := rejectRelated_valid accepted a ha; omega) deepA,
    positionGindex_gindexPosition (by have := rejectRelated_valid accepted b hb; omega) deepB]
    at this

/-- A replayed winning multiproof extraction exposes a collision of the cache.

The multiproof search over the two rebuilds finds it, run with a table that extends the cache. -/
theorem collision_of_extractMultiproofs {size : Nat} {cache : HashOracle.QueryCache}
    {claim : MultiproofClaim} {outcome : MultiproofOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractMultiproofs queryHash size claim) =
      some outcome)
    (hwins : MultiproofWins outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed rebuild.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  obtain ⟨hleaves, hfirst, hsecond, root, hroot₁, hroot₂⟩ := hwins
  unfold extractMultiproofs at hrun
  split at hrun
  · rename_i height opened claimed
    obtain ⟨unique, antichain, inside, count⟩ := claimPositions_valid claimed
    -- A request beyond the size gives no root, so only a rebuilt request can win.
    split at hrun
    swap
    · simp only [simulateQ_pure] at hrun
      cases hrun
      simp at hroot₁
    simp only [simulateQ_bind, simulateQ_pure] at hrun
    obtain ⟨firstRoot, hrun₁, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨secondRoot, hrun₂, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    cases hrun
    dsimp only at hleaves hfirst hsecond hroot₁ hroot₂
    subst hroot₁ hroot₂
    -- Each replayed rebuild is the rebuild with the table, and caches what it hashes.
    obtain ⟨rebuilt₁, cached₁⟩ := rebuild_go_of_replay_queryHash hf hrun₁
    obtain ⟨rebuilt₂, cached₂⟩ := rebuild_go_of_replay_queryHash hf hrun₂
    -- Under the table, the leaves are equal, or the search over the two rebuilds succeeds.
    rcases Cryptography.Merkle.verify_binding (fun _ => combineM (m := Id) (tableHash f)) unique
        antichain inside (by simp [hfirst, count]) (by simp [hsecond, count]) rebuilt₁.symm
        rebuilt₂.symm with same | found
    · refine absurd (List.map_injective_iff.mpr (fun a b equal => ?_) same) hleaves
      exact Vector.toArray_inj.mp (ByteArray.mk.inj equal)
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp found
      -- Every node given is 32 bytes, and so is every digest of the table.
      have widths : ∀ (leaves proof : List (Vector UInt8 32)),
          ∀ e ∈ opened.zip (leaves.map fun node => (⟨node.toArray⟩ : Bytes)) ++
            (Cryptography.Merkle.helpers height opened).zip
              (proof.map fun node => (⟨node.toArray⟩ : Bytes)), e.2.size = 32 := by
        intro leaves proof e member
        rcases List.mem_append.mp member with given | given <;>
          obtain ⟨vector, -, equal⟩ := List.mem_map.mp (List.of_mem_zip given).2 <;>
          · rw [← equal]
            exact vector.size_toArray
      obtain ⟨⟨different, joined⟩, -⟩ := Cryptography.Merkle.findMultiproofCollision_valid _ hc
      obtain ⟨x1, x2, y1, y2⟩ := Cryptography.Merkle.findMultiproofCollision_children _
        (fun node => node.size = 32) (fun _ x y => tableHash_size f (x ++ y)) (widths _ _)
        (widths _ _) hc
      -- Fixed child widths keep the boundary between the two children in place.
      have distinct : c.x.1 ++ c.x.2 ≠ c.y.1 ++ c.y.2 := fun equal => different (by
        have joinedData := congrArg ByteArray.data equal
        rw [ByteArray.data_append, ByteArray.data_append] at joinedData
        obtain ⟨h1, h2⟩ := Array.append_inj joinedData (by simp_all)
        exact Prod.ext (ByteArray.ext h1) (ByteArray.ext h2))
      -- Each pair is one that its own rebuild hashed, so the cache holds both messages.
      have recorded₁ := Cryptography.Merkle.findMultiproofCollision_recorded _
        (fun _ a b => a ++ b) height 0 _ [] hc
      have recorded₂ := Cryptography.Merkle.findMultiproofCollision_recorded _
        (fun _ a b => a ++ b) height 0 _ [] (c := ⟨c.position, c.y, c.x⟩)
        (by rw [Cryptography.Merkle.findMultiproofCollision_swap, hc]; rfl)
      exact collision_of_cached distinct joined (cached₁ _ recorded₁) (cached₂ _ recorded₂)
  · simp only [simulateQ_pure] at hrun
    cases hrun
    simp at hroot₁

/-- The extraction makes at most `2 * (size - 1)` oracle calls.

A request of more than `size` indices and helper indices is not rebuilt.

A rebuild from at most `size` given nodes hashes at most `size - 1` times. -/
theorem extractMultiproofs_queryBound (size : Nat) (claim : MultiproofClaim) :
    IsQueryBoundP (extractMultiproofs queryHash size claim) (fun _ => True)
      (2 * (size - 1)) := by
  unfold extractMultiproofs
  split
  · rename_i height opened _
    split
    · rename_i small
      -- Each rebuild has at most one node given per index and one per helper index.
      have rebuilds : ∀ (leaves proof : List (Vector UInt8 32)),
          IsQueryBoundP (Cryptography.Merkle.verify (fun _ => combineM queryHash) height opened
            (leaves.map fun node => ⟨node.toArray⟩) (proof.map fun node => ⟨node.toArray⟩))
            (fun _ => True) (size - 1) := by
        intro leaves proof
        refine (Cryptography.Merkle.RandomOracle.isQueryBoundP_rebuild_go
          (fun _ left right => combineM_queryBound left right) _ _ _).mono ?_
        simp only [List.length_append, List.length_zip, List.length_map]
        omega
      exact (isQueryBoundP_bind (rebuilds _ _) fun _ _ =>
        isQueryBoundP_bind (rebuilds _ _) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)
    · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _

/-- The experiment makes the adversary's oracle calls and at most `2 * (size - 1)` more. -/
theorem experimentWith_extractMultiproofs_queryBound (size : Nat)
    {adversary : OracleComp (unifSpec + HashOracle) MultiproofClaim} {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    IsQueryBoundP (experimentWith (extractMultiproofs queryHash size) adversary)
      (fun t => t.isRight = true) (q + 2 * (size - 1)) :=
  experimentWith_queryBound hq (extractMultiproofs_queryBound size)

/-- Two different lists of leaves of one request with one root, at probability at most `Q^2 / N`.

`Q` bounds the oracle calls of the whole experiment, repeats included, and `N` counts the digests.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_multiproofWins_le [SampleableType Hash32] (size : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) MultiproofClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractMultiproofs queryHash size) adversary)
      (fun t => t.isRight = true) Q) :
    -- The roots are rebuilt with the oracle as the node hash.
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractMultiproofs queryHash size) adversary)).run ∅}[
        MultiproofWins z.1] ≤ Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  -- Each win exposes two different queried inputs with one answer, so the birthday bound applies.
  prEvent_experimentWith_le (extractMultiproofs queryHash size) MultiproofWins
    collision_of_extractMultiproofs adversary hQ

/-- The same bound with the adversary's oracle calls `q` counted alone, and 32 bytes per answer.

A win has probability at most `(q + 2 * (size - 1))^2 / 2^256`.

The size bounds the indices and helper indices of a request that the extraction rebuilds. -/
theorem prEvent_multiproofWins_le_of_adversary (size : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) MultiproofClaim) {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractMultiproofs queryHash size) adversary)).run ∅}[
        MultiproofWins z.1] ≤
      (q + 2 * (size - 1) : Nat) * (((q + 2 * (size - 1) : Nat) : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_multiproofWins_le size adversary
    (experimentWith_extractMultiproofs_queryBound size hq)
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- With SHA-256 as the node hash, two accepted multiproofs of different leaves win.

A win need not be accepted, since the extraction ignores helper nodes beyond their count.

The step from SHA-256 to the oracle is the idealisation of the model, not a theorem. -/
theorem multiproofWins_sha256_of_verify {size : Nat} {claim : MultiproofClaim}
    {helpers : List Nat} {root : Bytes} (built : getHelperIndices claim.indices = .ok helpers)
    -- The request has at most `size` indices and helper indices.
    (small : claim.indices.length + helpers.length ≤ size)
    -- Both multiproofs answer the request with the same root, and their leaves differ.
    (differ : claim.firstLeaves ≠ claim.secondLeaves)
    (first : verifyMerkleMultiproof (claim.firstLeaves.map fun node => ⟨node.toArray⟩)
      (claim.firstProof.map fun node => ⟨node.toArray⟩) claim.indices root = .ok true)
    (second : verifyMerkleMultiproof (claim.secondLeaves.map fun node => ⟨node.toArray⟩)
      (claim.secondProof.map fun node => ⟨node.toArray⟩) claim.indices root = .ok true) :
    -- The roots of the outcome are rebuilt with SHA-256, not with the oracle.
    MultiproofWins (extractMultiproofs (m := Id) Cryptography.Hash.Sha256.hash size claim).run := by
  obtain ⟨-, -, built₁⟩ := (verifyMerkleMultiproof_eq_true_iff ..).mp first
  obtain ⟨-, -, built₂⟩ := (verifyMerkleMultiproof_eq_true_iff ..).mp second
  obtain ⟨other, otherIndices, leafCount₁, -, rebuilt₁⟩ :=
    calculateMultiMerkleRootUnchecked_shape built₁
  obtain rfl : helpers = other := Except.ok.inj (built.symm.trans otherIndices)
  obtain ⟨other, otherIndices, leafCount₂, -, rebuilt₂⟩ :=
    calculateMultiMerkleRootUnchecked_shape built₂
  obtain rfl : helpers = other := Except.ok.inj (built.symm.trans otherIndices)
  rw [List.length_map] at leafCount₁ leafCount₂
  -- The extraction with SHA-256 rebuilds the nodes of each multiproof, as the check does.
  rw [multiproofNodes_eq built (by simpa using leafCount₁)] at rebuilt₁
  rw [multiproofNodes_eq built (by simpa using leafCount₂)] at rebuilt₂
  obtain ⟨accepted, shape⟩ := getHelperIndices_ok built
  -- The request fits the size, since the helper indices are the helpers of the Merkle tree.
  have fits : (claim.indices.map (gindexPosition (gindexHeight claim.indices))).length +
      (Cryptography.Merkle.helpers (gindexHeight claim.indices)
        (claim.indices.map (gindexPosition (gindexHeight claim.indices)))).length ≤ size := by
    rw [shape, List.length_map] at small
    rwa [List.length_map]
  simp only [MultiproofWins, extractMultiproofs, claimPositions_ok accepted, ite_eq_left fits]
  exact ⟨differ, leafCount₁, leafCount₂, root, rebuilt₁, rebuilt₂⟩

end EthLib.Serialization.Ssz.RandomOracle

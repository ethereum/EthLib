module

public import EthLib.Cryptography.Proofs.Vrf.Hash
public import EthLib.Cryptography.Proofs.Vrf.Oracle
public import EthLib.Cryptography.Proofs.RandomOracleTable

/-!
# Proofs: the outputs of one secret with a cached random oracle

The oracle answers in place of the Keccak-256 call that gives each output.

The secret and the indices are fixed, and the cache holds no answer for their output inputs.

Then the outputs at distinct indices are independent uniform values.

No theorem here covers a secret chosen after the oracle answered one of those inputs.

The independence holds for the oracle, and no theorem carries it over to Keccak-f[1600] itself.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open OracleSpec OracleComp ENNReal

/-- Answering the hash call of each output with Keccak-256 gives the specified outputs. -/
theorem evalWithAnswerFn_outputs (secret : Digest) (indices : List UInt32) :
    evalWithAnswerFn (QueryImpl.ofFn hash)
      (indices.mapM fun i => oracleHash (outputInput i secret)) =
      indices.map fun i => outputHash i secret := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    rw [List.mapM_cons, List.map_cons, ← ih]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, oracleHash,
      evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, outputHash]

/-- The outputs of one secret at distinct indices are independent uniform values.

A random oracle answers their hash calls, from a cache with no answer for any of their inputs.

The secret and the indices are fixed before the oracle answers any of their output inputs. -/
theorem run_outputs_evalDistEq (secret : Digest) (indices : List UInt32)
    (cache : HashSpec.QueryCache) (distinct : indices.Nodup)
    -- The cache may hold other answers, such as those of leaf and node inputs.
    (fresh : ∀ i ∈ indices, cache (outputInput i secret) = none) :
    ((simulateQ HashSpec.randomOracle
      (indices.mapM fun i => oracleHash (outputInput i secret))).run' cache) =ᵈ
      indices.mapM fun _ => ($ᵗ Digest) := by
  -- Each index reads its own cell of a uniform table with `2^32` cells.
  let cell (i : UInt32) : Fin (2 ^ 32) := ⟨i.toNat, i.toNat_lt⟩
  have apart : Function.Injective cell := fun _ _ equal =>
    UInt32.toNat_inj.mp (congrArg Fin.val equal)
  -- Two output inputs of one secret are equal exactly when their indices are.
  have same : ∀ i ∈ indices, ∀ j ∈ indices,
      outputInput i secret = outputInput j secret ↔ cell i = cell j := fun i _ j _ =>
    ⟨fun equal => congrArg cell (outputInput_inj.mp equal).1,
      fun equal => congrArg (outputInput · secret) (apart equal)⟩
  have reads := run_mapM_query_evalDistEq (fun i => outputInput i secret) cell
    (fun _ (y : Digest) => y) indices same cache
  have draws := mapM_uniformSample_evalDistEq cell (fun _ (y : Digest) => y) indices
    (distinct.map apart)
  simp only [id_map'] at reads draws
  refine reads.trans ((EvalDistEq.of_eq ?_).trans draws.symm)
  congr 1
  funext T
  refine List.map_congr_left fun i hi => ?_
  simp only [fresh i hi, Option.getD_none]

/-- Two events, one on each output of one secret at distinct indices, hold with the product chance.

A random oracle answers their hash calls, from a cache with no answer for either input.

The factors are the chances of the two events for two uniform values. -/
theorem prEvent_outputs_pair_of_fresh (secret : Digest) (i j : UInt32) (different : i ≠ j)
    (cache : HashSpec.QueryCache) (leftFresh : cache (outputInput i secret) = none)
    (rightFresh : cache (outputInput j secret) = none) (P Q : Digest → Prop) :
    Pr{let z ← (simulateQ HashSpec.randomOracle (do
      let left ← oracleHash (outputInput i secret)
      let right ← oracleHash (outputInput j secret)
      pure (left, right))).run' cache}[P z.1 ∧ Q z.2] =
      Pr{let y ← $ᵗ Digest}[P y] * Pr{let y ← $ᵗ Digest}[Q y] := by
  -- Different indices give different output inputs.
  exact prEvent_run'_query_pair_of_fresh _ _
    (fun equal => different (outputInput_inj.mp equal).1) cache leftFresh rightFresh P Q

end EthLib.Cryptography.Vrf

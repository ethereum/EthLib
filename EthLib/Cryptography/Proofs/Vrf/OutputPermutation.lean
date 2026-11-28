module

public import EthLib.Cryptography.Proofs.Vrf.OutputRandomOracle
public import EthLib.Cryptography.Proofs.Hash.Keccak.Sponge

/-!
# Proofs: the outputs of one secret over a uniform permutation

Each hash is Keccak-256 with a uniform permutation in place of Keccak-f[1600].

With Keccak-f[1600] itself, each hash is the output of the specification.

An event on the outputs at distinct indices has nearly its chance for independent uniform values.

The secret, the indices and the events are fixed before the permutation is drawn.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open OracleSpec OracleComp ENNReal
open EthLib.Cryptography.Indifferentiability (Indifferentiable)
open EthLib.Cryptography.Sponge (spongeIndiffBound)
open EthLib.Cryptography.Hash.Keccak (State RATE_256 blockCount keccak256With keccak256Cost
  keccak256_indifferentiable)

/-- **The outputs of one secret at distinct indices, over a uniform permutation.**

An event on the `n` outputs holds with its chance for independent uniform values, up to `ε`.

Here `ε = n (n - 1) / 2^1601 + (n^2 + n) / 2^512`, the bound for a cost of one block per index.

With at most `2^32` distinct indices, `ε` is below `2^-447`. -/
theorem prEvent_outputs_keccak256With_le_add (secret : Digest) (indices : List UInt32)
    (distinct : indices.Nodup) (P : List Digest → Prop) :
    Pr{let π ← $ᵗ (Equiv.Perm State)}[P (indices.map fun i =>
        Id.run (keccak256With (fun S => pure (π S)) (outputInput i secret)))] ≤
        Pr{let ys ← indices.mapM fun _ => ($ᵗ Digest)}[P ys] +
          spongeIndiffBound (2 ^ 1600) (2 ^ 512) indices.length ∧
      Pr{let ys ← indices.mapM fun _ => ($ᵗ Digest)}[P ys] ≤
        Pr{let π ← $ᵗ (Equiv.Perm State)}[P (indices.map fun i =>
          Id.run (keccak256With (fun S => pure (π S)) (outputInput i secret)))] +
          spongeIndiffBound (2 ^ 1600) (2 ^ 512) indices.length := by
  -- The digests of Keccak-256 are those of the VRF.
  have hind : Indifferentiable (Dg := Digest)
      (fun π msg => Id.run (keccak256With (fun S => pure (π S)) msg)) keccak256Cost
      (spongeIndiffBound (2 ^ 1600) (2 ^ 512)) :=
    keccak256_indifferentiable
  have hcost := isQueryBound_mapM_oracleHash keccak256Cost indices fun i => outputInput i secret
  -- An output input has 49 bytes, so each hash call costs one block.
  rw [show (indices.map fun i => keccak256Cost (outputInput i secret)).sum = indices.length by
    simp [keccak256Cost, blockCount, RATE_256]] at hcost
  obtain ⟨hle, hge⟩ := hind.prEvent_le_add hcost P
  -- With a random oracle from an empty cache, the outputs are independent uniform values.
  rw [(run_outputs_evalDistEq secret indices ∅ distinct fun _ _ => rfl).prEvent_eq] at hle hge
  -- Over a fixed permutation, each hash call returns Keccak-256 over that permutation.
  simp only [simulateQ_list_mapM, oracleHash, simulateQ_spec_query, List.mapM_pure, map_pure,
    bind_pure_comp] at hle hge
  exact ⟨hle, hge⟩

/-- **Two outputs of one secret at distinct indices, over a uniform permutation.**

Two events, one on each output, both hold with the product chance, up to `2^-1600 + 6 / 2^512`.

The factors are the chances of the two events for two uniform values.

The bound is for a cost of 2, since each output input fits in one block. -/
theorem prEvent_outputs_pair_keccak256With_le_add (secret : Digest) (i j : UInt32)
    (different : i ≠ j) (P Q : Digest → Prop) :
    Pr{let π ← $ᵗ (Equiv.Perm State)}[
        P (Id.run (keccak256With (fun S => pure (π S)) (outputInput i secret))) ∧
          Q (Id.run (keccak256With (fun S => pure (π S)) (outputInput j secret)))] ≤
        Pr{let y ← $ᵗ Digest}[P y] * Pr{let y ← $ᵗ Digest}[Q y] +
          spongeIndiffBound (2 ^ 1600) (2 ^ 512) 2 ∧
      Pr{let y ← $ᵗ Digest}[P y] * Pr{let y ← $ᵗ Digest}[Q y] ≤
        Pr{let π ← $ᵗ (Equiv.Perm State)}[
          P (Id.run (keccak256With (fun S => pure (π S)) (outputInput i secret))) ∧
            Q (Id.run (keccak256With (fun S => pure (π S)) (outputInput j secret)))] +
          spongeIndiffBound (2 ^ 1600) (2 ^ 512) 2 := by
  -- The pair is the list of the two indices, with both events as one event on its outputs.
  have h := prEvent_outputs_keccak256With_le_add secret [i, j] (by simpa using different)
    fun ys => P (ys.getD 0 default) ∧ Q (ys.getD 1 default)
  -- Two independent uniform values give the product of the two chances.
  simp only [List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, List.length_cons,
    List.length_nil, List.getD_cons_zero, List.getD_cons_succ, bind_pure_comp, map_bind,
    Functor.map_map, map_pure, prEvent_bind_bind_and, zero_add, Nat.reduceAdd] at h
  exact h

end EthLib.Cryptography.Vrf

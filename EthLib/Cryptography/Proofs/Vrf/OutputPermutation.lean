module

public import EthLib.Cryptography.Proofs.Vrf.OutputRandomOracle
public import EthLib.Cryptography.Proofs.Hash.Keccak.Sponge

/-!
# Proofs: two outputs of one secret over a uniform permutation

Each hash is Keccak-256 with a uniform permutation in place of Keccak-f[1600].

With Keccak-f[1600] itself, each hash is the output of the specification.

Two events, one on each output at distinct indices, hold with nearly the product chance.

The secret, the indices and the events are fixed before the permutation is drawn.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open OracleSpec OracleComp ENNReal
open EthLib.Cryptography.Indifferentiability (Indifferentiable)
open EthLib.Cryptography.Sponge (spongeIndiffBound)
open EthLib.Cryptography.Hash.Keccak (State RATE_256 blockCount keccak256With keccak256Cost
  keccak256_indifferentiable)

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
  -- The digests of Keccak-256 are those of the VRF.
  have hind : Indifferentiable (Dg := Digest)
      (fun π msg => Id.run (keccak256With (fun S => pure (π S)) msg)) keccak256Cost
      (spongeIndiffBound (2 ^ 1600) (2 ^ 512)) :=
    keccak256_indifferentiable
  -- An output input has 49 bytes, so each of the two hash calls costs one block.
  have hcost : IsQueryBound (do
      let left ← oracleHash (outputInput i secret)
      let right ← oracleHash (outputInput j secret)
      pure (left, right)) 2 (fun x n => keccak256Cost x ≤ n) fun x n => n - keccak256Cost x := by
    simp [oracleHash, keccak256Cost, blockCount, RATE_256]
  obtain ⟨hle, hge⟩ := hind.prEvent_le_add hcost fun z => P z.1 ∧ Q z.2
  -- With a random oracle from an empty cache, the two events hold with the product chance.
  rw [prEvent_outputs_pair_of_fresh secret i j different ∅ rfl rfl P Q] at hle hge
  simp only [oracleHash, simulateQ_bind, simulateQ_map, simulateQ_spec_query, map_pure,
    bind_pure_comp] at hle hge
  exact ⟨hle, hge⟩

end EthLib.Cryptography.Vrf

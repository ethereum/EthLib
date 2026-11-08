module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Uniform

/-!
# Landing in the kept subtree

The kept subtree of a key holds `2^b` of the `2^h` indices.

This file numbers the indices that land in it by their local leaf numbers, `0` to `2^b - 1`.

It also shows that the index read from a uniform first digest call is uniform.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

variable [Params]

theorem subtreePosition_lt (parameter : PublicParameter) :
    subtreePosition parameter < 2 ^ (totalHeight - subtreeHeight) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem subtree_size_mul : 2 ^ (totalHeight - subtreeHeight) * 2 ^ subtreeHeight =
    (2 : Nat) ^ totalHeight := by
  rw [← pow_add, Nat.sub_add_cancel Params.subtreeHeight_le]

/-- The local leaf numbers below `2^b` enumerate the indices that land in the kept subtree. -/
def keptLeafEquiv (parameter : PublicParameter) :
    Fin (2 ^ subtreeHeight) ≃ {i : Index // Landed parameter i} where
  toFun j := ⟨⟨subtreePosition parameter * 2 ^ subtreeHeight + j.val, by
    have hj := j.isLt
    have hs := subtreePosition_lt parameter
    have hmul := Nat.mul_le_mul_right (2 ^ subtreeHeight) (Nat.succ_le_of_lt hs)
    rw [subtree_size_mul] at hmul
    rw [Nat.succ_mul] at hmul
    omega⟩, by
      change (subtreePosition parameter * 2 ^ subtreeHeight + j.val) / 2 ^ subtreeHeight = _
      rw [Nat.mul_comm (subtreePosition parameter), Nat.mul_add_div (Nat.two_pow_pos _),
        Nat.div_eq_of_lt j.isLt, Nat.add_zero]⟩
  invFun i := ⟨i.val.val % 2 ^ subtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  left_inv j := by
    apply Fin.ext
    change (subtreePosition parameter * 2 ^ subtreeHeight + j.val) % 2 ^ subtreeHeight = j.val
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change subtreePosition parameter * 2 ^ subtreeHeight + i.val.val % 2 ^ subtreeHeight = _
    rw [← i.property, Nat.mul_comm, Nat.div_add_mod]

/-- A full key keeps the whole top layer: its subtree is the first and only one. -/
theorem subtreePosition_eq_zero (parameter : PublicParameter) : subtreePosition parameter = 0 := by
  unfold subtreePosition
  rw [Params.full, Nat.sub_self, pow_zero, Nat.mod_one]

/-- With a full key, every index lands in the kept subtree. -/
theorem landed_full (parameter : PublicParameter) (index : Index) : Landed parameter index := by
  unfold Landed
  rw [subtreePosition_eq_zero, Params.full, Nat.div_eq_of_lt index.isLt]

theorem evalDist_blockIndex_uniform :
    (Concrete.blockIndex <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ
      ($ᵗ Index : ProbComp Index) := by
  have heq : Concrete.blockIndex <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      BitVec.toFin <$> ((fun u : HashOutput => u.extractLsb' 0 totalHeight) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)) := by rw [Functor.map_map]; rfl
  rw [heq]
  exact ((evalDist_hashOutput_extract_uniform totalHeight_le_hashOutput).map _).trans
    (SampleableType.map_uniformSample_evalDistEq_of_bijective (f := BitVec.toFin)
      ⟨fun _ _ h => congrArg BitVec.ofFin h, fun i => ⟨BitVec.ofFin i, rfl⟩⟩)

end SphincsSecurity

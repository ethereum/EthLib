module

public import EthLib.Cryptography.Proofs.Kzg.RecoveryMasked

/-!
# Proofs: at most half the cells are missing

Recovery needs at least 64 of the 128 cells.

Given distinct, in-range indices, the known and the missing cells partition the 128 cells.

So 64 known cells leave at most 64 missing ones.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Kzg.Constants

/-- For distinct in-range cell indices, known and missing cells partition the 128-cell domain. -/
theorem recoveryMissing_size_add_size
    (indices : Array CellIndex) (hnd : indices.toList.Nodup)
    (hbound : ∀ ci ∈ indices.toList, ci < CELLS_PER_EXT_BLOB) :
    (recoveryMissing indices).size + indices.size = CELLS_PER_EXT_BLOB := by
  have hperm : ((List.range CELLS_PER_EXT_BLOB).filter indices.contains).Perm indices.toList := by
    apply (List.perm_ext_iff_of_nodup
      (List.nodup_range.filter _) hnd).mpr
    intro ci
    simp only [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨_, h⟩
      simpa using h
    · intro h
      exact ⟨hbound ci h, by simpa using h⟩
  have hlen := (List.filter_append_perm indices.contains (List.range CELLS_PER_EXT_BLOB)).length_eq
  rw [List.length_append, hperm.length_eq, List.length_range] at hlen
  have hm : (recoveryMissing indices).size =
      ((List.range CELLS_PER_EXT_BLOB).filter (fun ci => !indices.contains ci)).length := by
    simp [recoveryMissing, ← Array.length_toList]
  rw [hm]
  simpa only [Array.length_toList, Nat.add_comm] using hlen

/-- At least half the distinct valid cells means at most half are erased. -/
theorem recoveryMissing_size_le_half
    (indices : Array CellIndex) (hnd : indices.toList.Nodup)
    (hbound : ∀ ci ∈ indices.toList, ci < CELLS_PER_EXT_BLOB)
    (hhalf : CELLS_PER_EXT_BLOB / 2 ≤ indices.size) :
    (recoveryMissing indices).size ≤ CELLS_PER_EXT_BLOB / 2 := by
  have hsum := recoveryMissing_size_add_size indices hnd hbound
  change (recoveryMissing indices).size + indices.size = 128 at hsum
  change 64 ≤ indices.size at hhalf
  change (recoveryMissing indices).size ≤ 64
  omega

end EthLib.Cryptography.Kzg

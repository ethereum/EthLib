module

public import EthLib.Base.Uint64

/-!
# Proofs: `Uint64`

A checked operation succeeds exactly when the exact result fits in 64 bits.

It then returns that result.

The integer square root is the floor of the square root, the largest `x` with `x^2 ≤ n`.
-/

@[expose] public section

namespace EthLib.Base.Uint64

/-- The sum succeeds exactly when it is below `2^64`, and then it is the sum on `Nat`. -/
theorem addChecked_ok_iff {a b c : UInt64} :
    addChecked a b = .ok c ↔ a.toNat + b.toNat < 2 ^ 64 ∧ c.toNat = a.toNat + b.toNat := by
  unfold addChecked
  split
  · -- Without overflow, the sum modulo `2^64` is the sum itself.
    rename_i h
    simp only [Except.ok.injEq, h, true_and]
    rw [← UInt64.toNat_inj, UInt64.toNat_add, Nat.mod_eq_of_lt h, eq_comm]
  · rename_i h
    simp only [reduceCtorEq, false_iff, not_and]
    omega

/-- A wrapping sum below `2^64` is the sum on `Nat`. -/
theorem toNat_add_of_lt {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

/-- A sum below `2^64` succeeds, and it returns the wrapping sum. -/
theorem addChecked_of_lt {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    addChecked a b = .ok (a + b) :=
  addChecked_ok_iff.mpr ⟨h, toNat_add_of_lt h⟩

/-- The difference succeeds exactly when `b ≤ a`, and then it is the difference on `Nat`. -/
theorem subChecked_ok_iff {a b c : UInt64} :
    subChecked a b = .ok c ↔ b.toNat ≤ a.toNat ∧ c.toNat = a.toNat - b.toNat := by
  unfold subChecked
  split
  · rename_i h
    simp only [Except.ok.injEq, UInt64.le_iff_toNat_le.mp h, true_and]
    rw [← UInt64.toNat_inj, UInt64.toNat_sub_of_le _ _ h, eq_comm]
  · rename_i h
    simp only [reduceCtorEq, false_iff, not_and]
    intro h'
    exact absurd (UInt64.le_iff_toNat_le.mpr h') h

/-- The product succeeds exactly when it is below `2^64`, and then it is the product on `Nat`. -/
theorem mulChecked_ok_iff {a b c : UInt64} :
    mulChecked a b = .ok c ↔ a.toNat * b.toNat < 2 ^ 64 ∧ c.toNat = a.toNat * b.toNat := by
  unfold mulChecked
  split
  · -- Without overflow, the product modulo `2^64` is the product itself.
    rename_i h
    simp only [Except.ok.injEq, h, true_and]
    rw [← UInt64.toNat_inj, UInt64.toNat_mul, Nat.mod_eq_of_lt h, eq_comm]
  · rename_i h
    simp only [reduceCtorEq, false_iff, not_and]
    omega

/-- A product below `2^64` succeeds, and it returns the wrapping product. -/
theorem mulChecked_of_lt {a b : UInt64} (h : a.toNat * b.toNat < 2 ^ 64) :
    mulChecked a b = .ok (a * b) :=
  mulChecked_ok_iff.mpr ⟨h, by rw [UInt64.toNat_mul, Nat.mod_eq_of_lt h]⟩

/-- The quotient succeeds exactly when `b ≠ 0`, and then it is the quotient on `Nat`. -/
theorem divChecked_ok_iff {a b c : UInt64} :
    divChecked a b = .ok c ↔ b ≠ 0 ∧ c.toNat = a.toNat / b.toNat := by
  unfold divChecked
  split
  · simp_all
  · rename_i h
    simp only [Except.ok.injEq, ne_eq, h, not_false_eq_true, true_and]
    rw [← UInt64.toNat_inj, UInt64.toNat_div, eq_comm]

/-- The saturating difference is the difference on `Nat`, which stops at 0. -/
theorem toNat_saturatingSub (a b : UInt64) :
    (saturatingSub a b).toNat = a.toNat - b.toNat := by
  unfold saturatingSub
  split
  · rename_i h
    exact UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)
  · rename_i h
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h)
    simp only [UInt64.toNat_zero]
    omega

/-- The integer square root is the floor square root on `Nat`. -/
theorem toNat_integerSquareroot (n : UInt64) :
    (integerSquareroot n).toNat = n.toNat.sqrt := by
  -- The root is at most `n`, so it is below `2^64` and the conversion keeps it.
  have hle : n.toNat.sqrt ≤ n.toNat := by
    have := Nat.sqrt_le n.toNat
    rcases Nat.eq_zero_or_pos n.toNat.sqrt with h | h
    · omega
    · exact Nat.le_trans (Nat.le_mul_of_pos_right _ h) this
  have hlt := Nat.lt_of_le_of_lt hle n.toNat_lt
  simp [integerSquareroot, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]

/-- The integer square root `r` of `n` has `r^2 ≤ n < (r + 1)^2`. -/
theorem integerSquareroot_spec (n : UInt64) :
    (integerSquareroot n).toNat ^ 2 ≤ n.toNat
      ∧ n.toNat < ((integerSquareroot n).toNat + 1) ^ 2 := by
  rw [toNat_integerSquareroot, Nat.pow_two, Nat.pow_two]
  exact ⟨Nat.sqrt_le _, Nat.lt_succ_sqrt _⟩

/-- A number has its square at most `n` exactly when it is at most the integer square root. -/
theorem le_integerSquareroot_iff (n : UInt64) (x : Nat) :
    x ^ 2 ≤ n.toNat ↔ x ≤ (integerSquareroot n).toNat := by
  obtain ⟨hlo, hhi⟩ := integerSquareroot_spec n
  generalize (integerSquareroot n).toNat = r at hlo hhi
  rw [Nat.pow_two] at *
  constructor
  · -- A number above the root has its square above `n`.
    intro hx
    exact Nat.le_of_lt_succ (Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_of_le_of_lt hx hhi))
  · intro hx
    exact Nat.le_trans (Nat.mul_self_le_mul_self hx) hlo

/-- At `n = 2^64 - 1` the root is `2^32 - 1 = 4294967295`. -/
theorem integerSquareroot_max : integerSquareroot 18446744073709551615 = 4294967295 := by
  apply UInt64.toNat.inj
  -- The bounds `r^2 ≤ n < (r + 1)^2` hold for exactly one `r`.
  have h := le_integerSquareroot_iff 18446744073709551615
  have hle := (h 4294967295).mp (by decide)
  have hlt : ¬ 4294967296 ≤ (integerSquareroot 18446744073709551615).toNat :=
    fun hx => absurd ((h 4294967296).mpr hx) (by decide)
  simp only [UInt64.reduceToNat]
  omega

end EthLib.Base.Uint64

module

public import EthLib.Cryptography.Hash.Blake2b
public import Mathlib.Logic.Function.Defs

/-!
# Proofs: `Hash.Blake2b`

The constants and the rounds of F, against [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693).

- The IV is what §2.6 derives from the square roots of the first eight primes.
- Each row of the message schedule is a permutation of the 16 word indices.
- Round `i` uses row `i mod 10`, and a run of rounds splits into two runs.
- Rotating a word by `n` bits with `0 < n < 64` has rotation by `64 - n` as its inverse.
- G on a four-word cycle, one round, and every run of rounds permute the work vector.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Blake2b

/-! ## The constants -/

/-- Word `i` of the IV is `floor(2^64 * frac(sqrt(p)))`, for `p` the `(i + 1)`-th prime, RFC 7693 §2.6.

- The primes are 2, 3, 5, 7, 11, 13, 17 and 19.
- Let `n = floor(sqrt(p))` and `s = 2^64 * n + IV[i]`.
- The word is right exactly when `s = floor(2^64 * sqrt(p))`.
- That is `s^2 <= 2^128 * p < (s + 1)^2`. -/
theorem IV_sqrt (i : Fin 8) :
    let p := #v[2, 3, 5, 7, 11, 13, 17, 19][i]
    let s := 2 ^ 64 * #v[1, 1, 2, 2, 3, 3, 4, 4][i] + IV[i].toNat
    s ^ 2 ≤ 2 ^ 128 * p ∧ 2 ^ 128 * p < (s + 1) ^ 2 := by
  revert i
  decide +kernel

/-- Each row of the message schedule is a permutation of the indices 0 to 15, RFC 7693 §2.7.

So each round reads every message word exactly once. -/
theorem SIGMA_perm (i : Fin 10) : SIGMA[i].toList.Perm (List.finRange 16) := by
  revert i
  decide +kernel

/-! ## The rounds -/

/-- Round `i + 10` is round `i`, RFC 7693 §2.7.

The schedule has 10 rows, so rounds 10 and 11 of BLAKE2b reuse rows 0 and 1. -/
theorem round_add_ten (m v : Vector UInt64 16) (i : Nat) : round m (i + 10) v = round m i v := by
  simp only [round, Nat.add_mod_right]

/-- Running `a + b` rounds is running `a` rounds, then the `b` rounds after them. -/
theorem roundsFrom_add (m v : Vector UInt64 16) (start a b : Nat) :
    roundsFrom m start (a + b) v = roundsFrom m (start + a) b (roundsFrom m start a v) := by
  induction a generalizing start v with
  | zero => simp [roundsFrom]
  | succ a ih =>
    -- Peel the first round off both sides, then apply the induction hypothesis.
    rw [Nat.add_right_comm, roundsFrom, ih, roundsFrom]
    congr 1
    omega

/-! ## The rotation -/

/-- `rotr x n` is the right rotation of the 64-bit word by `n` bits, for `0 < n < 64`.

The RFC writes the rotation as a shift right by `n` and a shift left by `64 - n`. -/
theorem rotr_toBitVec (x n : UInt64) (h0 : 0 < n.toNat) (h64 : n.toNat < 64) :
    (rotr x n).toBitVec = x.toBitVec.rotateRight n.toNat := by
  refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
  unfold rotr
  -- The left shift wraps modulo `2^64`, so its distance is `64 - n` bits.
  simp [hi, Nat.mod_eq_of_lt h64,
    show (18446744073709551616 - n.toNat) % 64 = 64 - n.toNat by omega]
  by_cases hlt : i < 64 - n.toNat
  · simp [hlt, BitVec.getLsbD_eq_getElem, (by omega : n.toNat + i < 64)]
  · simp [hlt, BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ n.toNat + i)]

/-- Rotating right by `n` and then by `64 - n` returns the word, for `0 < n < 64`. -/
theorem rotr_rotr (x n : UInt64) (h0 : 0 < n.toNat) (h64 : n.toNat < 64) :
    rotr (rotr x n) (64 - n) = x := by
  have hsub : (64 - n).toNat = 64 - n.toNat := by
    rw [UInt64.toNat_sub_of_le]
    · simp
    · rw [UInt64.le_iff_toNat_le]
      exact Nat.le_of_lt h64
  apply UInt64.toBitVec_inj.mp
  rw [rotr_toBitVec _ _ (by omega) (by omega), rotr_toBitVec _ _ h0 h64, hsub]
  refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
  simp only [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt (by omega : 64 - n.toNat < 64),
    Nat.mod_eq_of_lt h64, hi, decide_true, Bool.true_and]
  rw [show 64 - (64 - n.toNat) = n.toNat by omega]
  by_cases hlt : i < n.toNat
  · have hlt2 : 64 - n.toNat + i < 64 := by omega
    have hge2 : ¬ (64 - n.toNat + i < 64 - n.toNat) := by omega
    simp [hlt, hlt2, hge2, show 64 - n.toNat + i - (64 - n.toNat) = i by omega]
  · have hlt3 : i - n.toNat < 64 - n.toNat := by omega
    simp [hlt, hlt3, show n.toNat + (i - n.toNat) = i by omega]

/-- Subtracting a positive distance below 64 from 64 twice returns that distance. -/
private theorem sixtyFour_sub_cancel {n : UInt64} (h0 : 0 < n.toNat) (h64 : n.toNat < 64) :
    (64 - n).toNat = 64 - n.toNat ∧ 64 - (64 - n) = n := by
  have hsub : (64 - n).toNat = 64 - n.toNat := by
    rw [UInt64.toNat_sub_of_le]
    · simp
    · exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt h64)
  refine ⟨hsub, UInt64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq ?_)⟩
  simp
  omega

/-- Right rotation by a fixed `n` with `0 < n < 64` permutes the 64-bit words. -/
theorem rotr_left_bijective {n : UInt64} (h0 : 0 < n.toNat) (h64 : n.toNat < 64) :
    Function.Bijective (rotr · n) := by
  obtain ⟨hsub, hcancel⟩ := sixtyFour_sub_cancel h0 h64
  refine ⟨Function.LeftInverse.injective (g := (rotr · (64 - n))) fun x => rotr_rotr x n h0 h64,
    Function.RightInverse.surjective (g := (rotr · (64 - n))) fun x => ?_⟩
  simpa only [hcancel] using rotr_rotr x (64 - n) (by omega) (by omega)

/-- Right rotation by a fixed `n` with `0 < n < 64` loses no bit of the word. -/
theorem rotr_left_injective {n : UInt64} (h0 : 0 < n.toNat) (h64 : n.toNat < 64) :
    Function.Injective (rotr · n) :=
  (rotr_left_bijective h0 h64).1

/-! ## One update of a work-vector word -/

/-- Replacing word `i` by `f` of words `i` and `j` is bijective when `g` undoes `f`.

The other words stay fixed, so the inverse replaces word `i` by `g` of the same pair. -/
private theorem set_bijective (i j : Fin 16) (f g : UInt64 → UInt64 → UInt64) (hij : i ≠ j)
    (hl : ∀ u w, g (f u w) w = u) (hr : ∀ u w, f (g u w) w = u) :
    Function.Bijective (fun v : Vector UInt64 16 => v.set i (f v[i] v[j])) := by
  have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
  refine ⟨Function.LeftInverse.injective
      (g := fun v : Vector UInt64 16 => v.set i (g v[i] v[j])) fun v => ?_,
    Function.RightInverse.surjective
      (g := fun v : Vector UInt64 16 => v.set i (g v[i] v[j])) fun v => ?_⟩
  · ext k hk
    by_cases hik : i.val = k
    · subst hik
      simp [hne, hl]
    · simp [hik]
  · ext k hk
    by_cases hik : i.val = k
    · subst hik
      simp [hne, hr]
    · simp [hik]

/-- Adding a word and a message word into another word is bijective on the work vector. -/
private theorem set_add3_bijective {i j : Fin 16} (hij : i ≠ j) (x : UInt64) :
    Function.Bijective (fun v : Vector UInt64 16 => v.set i (v[i] + v[j] + x)) :=
  set_bijective i j (fun u w => u + w + x) (fun u w => u - x - w) hij
    (fun u w => by rw [UInt64.add_sub_cancel, UInt64.add_sub_cancel])
    (fun u w => by rw [UInt64.sub_add_cancel, UInt64.sub_add_cancel])

/-- Adding one word into another word is bijective on the work vector. -/
private theorem set_add2_bijective {i j : Fin 16} (hij : i ≠ j) :
    Function.Bijective (fun v : Vector UInt64 16 => v.set i (v[i] + v[j])) :=
  set_bijective i j (fun u w => u + w) (fun u w => u - w) hij
    UInt64.add_sub_cancel UInt64.sub_add_cancel

/-- XOR of two words, then rotation right by `n`, is bijective for `0 < n < 64`.

The inverse rotates right by `64 - n` and XORs the unchanged word again. -/
private theorem set_xor_rotr_bijective {i j : Fin 16} (hij : i ≠ j) {n : UInt64}
    (h0 : 0 < n.toNat) (h64 : n.toNat < 64) :
    Function.Bijective (fun v : Vector UInt64 16 => v.set i (rotr (v[i] ^^^ v[j]) n)) := by
  obtain ⟨hsub, hcancel⟩ := sixtyFour_sub_cancel h0 h64
  exact set_bijective i j (fun u w => rotr (u ^^^ w) n) (fun u w => rotr u (64 - n) ^^^ w) hij
    (fun u w => by rw [rotr_rotr _ _ h0 h64, UInt64.xor_assoc, UInt64.xor_self, UInt64.xor_zero])
    (fun u w => by
      have hrot := rotr_rotr u (64 - n) (by omega) (by omega)
      rw [hcancel] at hrot
      rw [UInt64.xor_assoc, UInt64.xor_self, UInt64.xor_zero, hrot])

/-! ## G, one round and a run of rounds -/

/-- G of RFC 7693 §3.1 permutes the work vector when adjacent indices in `(a, b, c, d)` differ.

Each of its eight updates changes one word from an adjacent word around that four-word cycle.

Subtraction undoes addition, and the complementary rotation undoes each rotation. -/
theorem mix_bijective {a b c d : Fin 16} (x y : UInt64)
    (hab : a ≠ b) (had : a ≠ d) (hbc : b ≠ c) (hcd : c ≠ d) :
    Function.Bijective (mix · a b c d x y) := by
  have h1 := set_add3_bijective hab x
  have h2 := set_xor_rotr_bijective had.symm (n := 32) (by decide) (by decide)
  have h3 := set_add2_bijective hcd
  have h4 := set_xor_rotr_bijective hbc (n := 24) (by decide) (by decide)
  have h5 := set_add3_bijective hab y
  have h6 := set_xor_rotr_bijective had.symm (n := 16) (by decide) (by decide)
  have h7 := set_add2_bijective hcd
  have h8 := set_xor_rotr_bijective hbc (n := 63) (by decide) (by decide)
  -- G is the composition of those eight updates, in the order of the RFC.
  exact h8.comp (h7.comp (h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))))

/-- G is injective on the work vector when adjacent indices in `(a, b, c, d)` differ. -/
theorem mix_injective {a b c d : Fin 16} (x y : UInt64)
    (hab : a ≠ b) (had : a ≠ d) (hbc : b ≠ c) (hcd : c ≠ d) :
    Function.Injective (mix · a b c d x y) :=
  (mix_bijective x y hab had hbc hcd).1

/-- Round `i` of F permutes the work vector, for every message block.

Each column and each diagonal of the 4 x 4 matrix has four distinct indices. -/
theorem round_bijective (m : Vector UInt64 16) (i : Nat) :
    Function.Bijective (round m i) := by
  let s := SIGMA[i % 10]
  have c0 := mix_bijective (a := 0) (b := 4) (c := 8) (d := 12) m[s[0]] m[s[1]]
    (by decide) (by decide) (by decide) (by decide)
  have c1 := mix_bijective (a := 1) (b := 5) (c := 9) (d := 13) m[s[2]] m[s[3]]
    (by decide) (by decide) (by decide) (by decide)
  have c2 := mix_bijective (a := 2) (b := 6) (c := 10) (d := 14) m[s[4]] m[s[5]]
    (by decide) (by decide) (by decide) (by decide)
  have c3 := mix_bijective (a := 3) (b := 7) (c := 11) (d := 15) m[s[6]] m[s[7]]
    (by decide) (by decide) (by decide) (by decide)
  have d0 := mix_bijective (a := 0) (b := 5) (c := 10) (d := 15) m[s[8]] m[s[9]]
    (by decide) (by decide) (by decide) (by decide)
  have d1 := mix_bijective (a := 1) (b := 6) (c := 11) (d := 12) m[s[10]] m[s[11]]
    (by decide) (by decide) (by decide) (by decide)
  have d2 := mix_bijective (a := 2) (b := 7) (c := 8) (d := 13) m[s[12]] m[s[13]]
    (by decide) (by decide) (by decide) (by decide)
  have d3 := mix_bijective (a := 3) (b := 4) (c := 9) (d := 14) m[s[14]] m[s[15]]
    (by decide) (by decide) (by decide) (by decide)
  exact d3.comp (d2.comp (d1.comp (d0.comp (c3.comp (c2.comp (c1.comp c0))))))

/-- The rounds from `start` through `start + count - 1` permute the work vector.

The statement holds for every message block, starting round and round count. -/
theorem roundsFrom_bijective (m : Vector UInt64 16) (start count : Nat) :
    Function.Bijective (roundsFrom m start count) := by
  induction count generalizing start with
  | zero => exact Function.bijective_id
  | succ count ih =>
    -- One more round is one bijective round followed by a bijective run.
    simpa [roundsFrom, Function.comp_def] using (ih (start + 1)).comp (round_bijective m start)

/-- Column `0, 4, 8, 12` of RFC 7693 §3.2 satisfies the cycle inequalities, and one round permutes.

The four indices are the first column of the work matrix. -/
theorem exists_mix_indices_and_round_bijective :
    ∃ a b c d : Fin 16, a ≠ b ∧ a ≠ d ∧ b ≠ c ∧ c ≠ d ∧
      (∀ x y : UInt64, Function.Bijective (mix · a b c d x y)) ∧
      (∀ m : Vector UInt64 16, ∀ i : Nat, Function.Bijective (round m i)) :=
  ⟨0, 4, 8, 12, by decide, by decide, by decide, by decide,
    fun x y => mix_bijective x y (by decide) (by decide) (by decide) (by decide),
    round_bijective⟩

end EthLib.Cryptography.Hash.Blake2b

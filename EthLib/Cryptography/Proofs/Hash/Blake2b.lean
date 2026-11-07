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
- F, read as 64-bit vectors, is the F of a model of §3.1 and §3.2, for every round count.

The model works on 64-bit vectors and rotates with the rotation of bit vectors.

It takes the offset counter as one 128-bit vector, as §3.2 does.

It shares only the IV and the message schedule with the executable code.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Blake2b

/-! ## The model -/

namespace Spec

/-- A word of BLAKE2b, `w = 64` bits, RFC 7693 §2.1.

Its addition is modulo `2^64`, as in §3.1. -/
abbrev Word := BitVec 64

/-- The mixing function G, RFC 7693 §3.1.

It rotates by the constants 32, 24, 16 and 63 of §2.1. -/
def mix (v : Vector Word 16) (a b c d : Fin 16) (x y : Word) : Vector Word 16 :=
  let v := v.set a (v[a] + v[b] + x)
  let v := v.set d ((v[d] ^^^ v[a]).rotateRight 32)
  let v := v.set c (v[c] + v[d])
  let v := v.set b ((v[b] ^^^ v[c]).rotateRight 24)
  let v := v.set a (v[a] + v[b] + y)
  let v := v.set d ((v[d] ^^^ v[a]).rotateRight 16)
  let v := v.set c (v[c] + v[d])
  v.set b ((v[b] ^^^ v[c]).rotateRight 63)

/-- Round `i` of the loop of RFC 7693 §3.2.

It applies G to the four columns and then to the four diagonals of the work vector.

It reads the message words in the order of row `i mod 10` of the message schedule. -/
def round (m : Vector Word 16) (i : Nat) (v : Vector Word 16) : Vector Word 16 :=
  let s := SIGMA[i % 10]
  let v := mix v 0 4  8 12 m[s[0]]  m[s[1]]
  let v := mix v 1 5  9 13 m[s[2]]  m[s[3]]
  let v := mix v 2 6 10 14 m[s[4]]  m[s[5]]
  let v := mix v 3 7 11 15 m[s[6]]  m[s[7]]
  let v := mix v 0 5 10 15 m[s[8]]  m[s[9]]
  let v := mix v 1 6 11 12 m[s[10]] m[s[11]]
  let v := mix v 2 7  8 13 m[s[12]] m[s[13]]
  mix v 3 4  9 14 m[s[14]] m[s[15]]

/-- The work vector after rounds `0` to `n - 1` of the loop of RFC 7693 §3.2. -/
def rounds (m : Vector Word 16) (v : Vector Word 16) : Nat → Vector Word 16
  | 0 => v
  | n + 1 => round m n (rounds m v n)

/-- The compression function F of RFC 7693 §3.2, with `r` rounds.

- `h` is the state and `m` is the message block.
- `t` is the 128-bit offset counter and `f` is the final block flag.

The work vector starts as the state followed by the IV.

Word 12 takes `t mod 2^64` and word 13 takes `t >> 64`, both by exclusive-or.

The final block inverts all bits of word 14.

After the rounds, word `i` of the result is `h[i] ^ v[i] ^ v[i + 8]`.

The RFC fixes `r = 12`, and EIP-152 lets the caller choose `r`. -/
def compress (r : Nat) (h : Vector Word 8) (m : Vector Word 16) (t : BitVec 128) (f : Bool) :
    Vector Word 8 :=
  let v : Vector Word 16 := h ++ IV.map UInt64.toBitVec
  let v := v.set 12 (v[12] ^^^ t.setWidth 64)
  let v := v.set 13 (v[13] ^^^ (t >>> 64).setWidth 64)
  let v := if f then v.set 14 (~~~v[14]) else v
  let v := rounds m v r
  Vector.ofFn fun i => h[i] ^^^ v[i] ^^^ v[i.val + 8]

end Spec

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

/-- The rotation is the right rotation of the 64-bit word by `n` bits, for `0 < n < 64`.

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

/-- Rotating right by `n` and then by `64 - n` returns the word, for `0 < n < 64`. -/
theorem rotr_rotr (x n : UInt64) (h0 : 0 < n.toNat) (h64 : n.toNat < 64) :
    rotr (rotr x n) (64 - n) = x := by
  have hsub := (sixtyFour_sub_cancel h0 h64).1
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

/-- Right rotation by a fixed `n` with `0 < n < 64` permutes the 64-bit words. -/
theorem rotr_left_bijective {n : UInt64} (h0 : 0 < n.toNat) (h64 : n.toNat < 64) :
    Function.Bijective (rotr · n) := by
  obtain ⟨hsub, hcancel⟩ := sixtyFour_sub_cancel h0 h64
  refine ⟨Function.LeftInverse.injective (g := (rotr · (64 - n))) fun x => rotr_rotr x n h0 h64,
    Function.RightInverse.surjective (g := (rotr · (64 - n))) fun x => ?_⟩
  simpa only [hcancel] using rotr_rotr x (64 - n) (by omega) (by omega)

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

/-! ## Agreement with the model -/

/-- An entry of a work vector, as a bit vector, is that entry of the vector read as bit vectors. -/
private theorem toBitVec_getElem (v : Vector UInt64 16) (i : Nat) (hi : i < 16) :
    v[i].toBitVec = (v.map UInt64.toBitVec)[i] :=
  (Vector.getElem_map _ _).symm

/-- G, read word by word as 64-bit vectors, is the G of the model. -/
theorem mix_toBitVec (v : Vector UInt64 16) (a b c d : Fin 16) (x y : UInt64) :
    (mix v a b c d x y).map UInt64.toBitVec =
      Spec.mix (v.map UInt64.toBitVec) a b c d x.toBitVec y.toBitVec := by
  have r32 (z : UInt64) : (rotr z 32).toBitVec = z.toBitVec.rotateRight 32 :=
    rotr_toBitVec z 32 (by decide) (by decide)
  have r24 (z : UInt64) : (rotr z 24).toBitVec = z.toBitVec.rotateRight 24 :=
    rotr_toBitVec z 24 (by decide) (by decide)
  have r16 (z : UInt64) : (rotr z 16).toBitVec = z.toBitVec.rotateRight 16 :=
    rotr_toBitVec z 16 (by decide) (by decide)
  have r63 (z : UInt64) : (rotr z 63).toBitVec = z.toBitVec.rotateRight 63 :=
    rotr_toBitVec z 63 (by decide) (by decide)
  simp only [mix, Spec.mix, Fin.getElem_fin, UInt64.toBitVec_add, UInt64.toBitVec_xor,
    r32, r24, r16, r63, toBitVec_getElem, Vector.map_set]

/-- Round `i`, read word by word as 64-bit vectors, is round `i` of the model. -/
theorem round_toBitVec (m v : Vector UInt64 16) (i : Nat) :
    (round m i v).map UInt64.toBitVec =
      Spec.round (m.map UInt64.toBitVec) i (v.map UInt64.toBitVec) := by
  simp only [round, Spec.round, mix_toBitVec, Fin.getElem_fin, Vector.getElem_map]

/-- The first `n` rounds, read as 64-bit vectors, are the first `n` rounds of the model. -/
theorem roundsFrom_zero_toBitVec (m v : Vector UInt64 16) (n : Nat) :
    (roundsFrom m 0 n v).map UInt64.toBitVec =
      Spec.rounds (m.map UInt64.toBitVec) (v.map UInt64.toBitVec) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- Round `n` comes after the first `n` rounds.
    rw [roundsFrom_add, Nat.zero_add, roundsFrom, roundsFrom, round_toBitVec, ih, Spec.rounds]

/-- The low and high halves of a 128-bit vector made of two 64-bit vectors. -/
private theorem append_halves (hi lo : BitVec 64) :
    (hi ++ lo).setWidth 64 = lo ∧ ((hi ++ lo) >>> 64).setWidth 64 = hi := by
  refine ⟨BitVec.setWidth_append_eq_right, BitVec.eq_of_getLsbD_eq fun i hi64 => ?_⟩
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hi64]
  simp

/-- F, read word by word as 64-bit vectors, is the F of the model.

The counter of the model is the 128-bit vector whose high word is `t1` and whose low word is `t0`.

This holds for every round count, state, message block, counter and flag. -/
theorem compress_toBitVec (r : Nat) (h : Vector UInt64 8) (m : Vector UInt64 16) (t0 t1 : UInt64)
    (f : Bool) :
    (compress r h m t0 t1 f).map UInt64.toBitVec =
      Spec.compress r (h.map UInt64.toBitVec) (m.map UInt64.toBitVec)
        (t1.toBitVec ++ t0.toBitVec) f := by
  obtain ⟨hlo, hhi⟩ := append_halves t1.toBitVec t0.toBitVec
  have hinv (z : UInt64) : (z ^^^ 0xFFFFFFFFFFFFFFFF).toBitVec = ~~~z.toBitVec := by
    rw [UInt64.toBitVec_xor, show (0xFFFFFFFFFFFFFFFF : UInt64).toBitVec = BitVec.allOnes 64 by
      decide, BitVec.xor_allOnes]
  cases f <;>
  · refine Vector.ext fun i hi => ?_
    simp only [compress, Spec.compress, Vector.getElem_map, Vector.getElem_ofFn, ↓reduceIte,
      Bool.false_eq_true]
    simp only [Fin.getElem_fin, UInt64.toBitVec_xor, toBitVec_getElem, roundsFrom_zero_toBitVec,
      Vector.map_set, Vector.map_append, Vector.getElem_map, hinv, hlo, hhi]

end EthLib.Cryptography.Hash.Blake2b

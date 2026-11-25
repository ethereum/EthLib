module

public import EthLib.Cryptography.Montgomery.Limbs

/-!
# Montgomery arithmetic: the CIOS product

The Montgomery product `a b R⁻¹ mod p` of numbers written in words, below `p`.

The product is the Coarsely Integrated Operand Scanning (CIOS) method of Koç, Acar and Kaliski.

It is "Analyzing and comparing Montgomery multiplication algorithms", [IEEE Micro 16(3)][cios].

[cios]: https://doi.org/10.1109/40.502403
-/

@[expose] public section

namespace EthLib.Cryptography.Montgomery

open Internal

section Generic

variable {n : Nat} [Words n]

private theorem low_zero {m x y z : Nat} (hm : m = x * y % 2 ^ 32)
    (h : (z * y + 1) % 2 ^ 32 = 0) : (x + m * z) % 2 ^ 32 = 0 := by
  subst hm
  rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod, Nat.mul_assoc, Nat.mul_comm y z]
  have : x + x * (z * y) = x * (z * y + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
  rw [this, Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-! ## The product -/

/-- One CIOS step: `(t + a b_i + m p) / 2 ^ 32`, as the low words and the word above them.

`m` is the multiple of `p` that makes the low word of the sum zero. -/
@[inline] def step (p : Nat → UInt64) (pinv : UInt64) (a b : Nat → UInt64) (i : Nat)
    (st : Words.W n × UInt64) : Words.W n × UInt64 :=
  -- The product of two forms is `a b R ^ 2`, and one Montgomery reduction divides it by `R`.
  --
  -- The reduction adds the multiple of `p` that clears the low limb, then drops that limb.
  --
  -- So it needs no division by `p`.
  --
  -- CIOS interleaves the product and the reduction, one limb of `b` at a time.
  --
  -- CIOS, the multiplication loop over `j` from `0` to `s - 1`, with `C := 0` first.
  --
  -- The paper's modulus `n` is `p` here.
  let r := Words.mac st.1 a (b i) 0 0
  -- `m := t[0]*n'[0] mod W`, with `W = 2^32` and `n'[0] = -p^(-1) mod W`.
  let m := (Words.word r.1 0 * pinv) &&& 0xFFFFFFFF
  -- `(C,S) := t[s] + C`, `t[s] := S`, `t[s+1] := C` is one 64-bit sum: the top word plus the carry.
  --
  -- The reduction loop follows, with the shift by one word integrated, as the paper improves it.
  Words.red r.1 p m (st.2 + r.2)

/-- The integer of words and the word above them. -/
def value (st : Words.W n × UInt64) : Nat :=
  num n (Words.word st.1) 0 + 2 ^ (32 * n) * st.2.toNat

/-- A modulus with an inverse mod `2 ^ 32` is positive. -/
theorem Internal.pos_of_pinv {P : Nat} {pinv : UInt64} (hpinv : (P * pinv.toNat + 1) % 2 ^ 32 = 0) :
    0 < P := by
  rcases Nat.eq_zero_or_pos P with h | h
  · rw [h, Nat.zero_mul] at hpinv
    exact absurd hpinv (by decide)
  · exact h

/-- One CIOS step adds `a b_i` and a multiple of `p`, divides by `2 ^ 32`, and stays below `2 p`. -/
theorem Internal.step_spec {p : Nat → UInt64} {pinv : UInt64} (hp : Fits n p 0)
    (hpinv : (num n p 0 * pinv.toNat + 1) % 2 ^ 32 = 0) {a : Nat → UInt64} (ha : Fits n a 0)
    (hA : num n a 0 < num n p 0) (b : Nat → UInt64) {i : Nat} (hb : (b i).toNat < 2 ^ 32)
    {st : Words.W n × UInt64} (ht : Fits n (Words.word st.1) 0)
    (hv : value st < 2 * num n p 0) :
    Fits n (Words.word (step p pinv a b i st).1) 0 ∧ value (step p pinv a b i st) < 2 * num n p 0 ∧
      ∃ m, 2 ^ 32 * value (step p pinv a b i st) = value st + num n a 0 * (b i).toNat +
        m * num n p 0 := by
  have hP := pos_of_pinv hpinv
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd hP (by simp [num])
    · exact h
  have hR := num_lt hp
  have z : (0 : UInt64).toNat < 2 ^ 32 := by decide
  obtain ⟨fr, cr, er⟩ := Words.mac_spec st.1 a (b i) 0 0 ht ha hb z
  have hst : st.2.toNat < 2 := by
    simp only [value] at hv
    have : 2 ^ (32 * n) * st.2.toNat < 2 ^ (32 * n) * 2 := by
      rw [Nat.mul_comm _ 2]
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  have htop : (st.2 + (Words.mac st.1 a (b i) 0 0).2).toNat =
      st.2.toNat + (Words.mac st.1 a (b i) 0 0).2.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hm : ((Words.word (Words.mac st.1 a (b i) 0 0).1 0 * pinv) &&& 0xFFFFFFFF).toNat =
      (Words.word (Words.mac st.1 a (b i) 0 0).1 0).toNat * pinv.toNat % 2 ^ 32 := by
    have hk : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl
    rw [UInt64.toNat_and, hk, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_mul,
      Nat.mod_mod_of_dvd _ (by decide)]
  generalize hmd : (Words.word (Words.mac st.1 a (b i) 0 0).1 0 * pinv) &&& 0xFFFFFFFF = m at hm
  have hml : m.toNat < 2 ^ 32 := hm ▸ Nat.mod_lt _ (by decide)
  have hlow := low_zero hm hpinv
  have h0 := num_mod hn fr
  obtain ⟨q, hq⟩ := radix_mod (n := n) hn
  have hsum : (num n (Words.word (Words.mac st.1 a (b i) 0 0).1) 0 + m.toNat * num n p 0 +
      2 ^ (32 * n) * (st.2 + (Words.mac st.1 a (b i) 0 0).2).toNat) % 2 ^ 32 = 0 := by
    rw [hq, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    omega
  obtain ⟨fs, cs, es⟩ := Words.red_spec _ p m _ fr hp hml (by omega) hsum
  simp only [step]
  rw [hmd]
  refine ⟨fs, ?_, ⟨m.toNat, ?_⟩⟩
  · have hb1 : num n a 0 * (b i).toNat ≤ num n p 0 * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (Nat.le_of_lt hA) (by omega)
    have hb2 : m.toNat * num n p 0 ≤ (2 ^ 32 - 1) * num n p 0 := Nat.mul_le_mul_right _ (by omega)
    simp only [value, UInt64.toNat_zero, Nat.add_zero] at *
    rw [htop, Nat.mul_add (2 ^ (32 * n))] at es
    omega
  · simp only [value, UInt64.toNat_zero, Nat.add_zero] at *
    rw [htop, Nat.mul_add (2 ^ (32 * n))] at es
    omega

/-- `x - p` when `x ≥ p`, else `x`, for `x < 2 p` given as words and the word above them. -/
@[inline] def reduce (p : Nat → UInt64) (t : Words.W n) (top : UInt64) {β : Type}
    (out : Words.W n → β) : β :=
  -- Step 3 of the paper: the result is `u - n` when `u >= n`, and `u` otherwise.
  let d := Words.subb t p 0 0
  -- The borrow exceeds the top word exactly when `x < p`.
  if top < d.2 then out t else out d.1

/-- The final reduction hands its result to its continuation. -/
theorem Internal.reduce_out (p : Nat → UInt64) (t : Words.W n) (top : UInt64) {β : Type}
    (out : Words.W n → β) : reduce p t top out = out (reduce p t top id) := by
  unfold reduce
  dsimp only
  split <;> rfl

/-- The final reduction gives the integer mod `p`. -/
theorem Internal.reduce_spec {p : Nat → UInt64} (hp : Fits n p 0) {t : Words.W n} {top : UInt64}
    (ht : Fits n (Words.word t) 0) (hv : value (t, top) < 2 * num n p 0) :
    Fits n (Words.word (reduce p t top id)) 0 ∧
      num n (Words.word (reduce p t top id)) 0 = value (t, top) % num n p 0 := by
  have z : (0 : UInt64).toNat ≤ 1 := by decide
  obtain ⟨fd, bd, ed⟩ := Words.subb_spec t p 0 0 ht hp z
  have hR := num_lt hp
  have hRt := num_lt ht
  have hRd := num_lt fd
  simp only [value, UInt64.toNat_zero, Nat.add_zero] at hv ed
  have htop : top.toNat < 2 := by
    have : 2 ^ (32 * n) * top.toNat < 2 ^ (32 * n) * 2 := by
      rw [Nat.mul_comm _ 2]
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  unfold reduce
  simp only [value, id]
  generalize Words.subb t p 0 0 = d at *
  generalize 2 ^ (32 * n) = R at *
  have hb : d.2.toNat = 0 ∨ d.2.toNat = 1 := by omega
  have ht' : top.toNat = 0 ∨ top.toNat = 1 := by omega
  split
  · rename_i h
    have h' : top.toNat < d.2.toNat := h
    refine ⟨ht, ?_⟩
    rcases hb with hb | hb <;> rcases ht' with ht' | ht' <;> simp only [hb, ht'] at * <;>
      first | omega | (rw [Nat.mod_eq_of_lt (by omega)]; omega)
  · rename_i h
    have h' : ¬ top.toNat < d.2.toNat := h
    refine ⟨fd, ?_⟩
    rcases hb with hb | hb <;> rcases ht' with ht' | ht' <;> simp only [hb, ht'] at * <;>
      first | omega | (rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega)

/-- The CIOS product `a b 2 ^ (-32 n)` mod `p`, reduced, given to `out`. -/
@[inline] def mulWords (p : Nat → UInt64) (pinv : UInt64) (a b : Nat → UInt64) {β : Type}
    (out : Words.W n → β) : β :=
  -- CIOS: one step for each `i` from `0` to `s - 1`, with the array `t` set to `0` first.
  let st := Words.fold (n := n) (step p pinv a b) 0 (Words.zero, 0)
  -- The result is the first `s + 1` words of `t`, below `2 p`, then one subtraction.
  reduce p st.1 st.2 out

/-- The product hands its result to its continuation. -/
theorem Internal.mulWords_out (p : Nat → UInt64) (pinv : UInt64) (a b : Nat → UInt64) {β : Type}
    (out : Words.W n → β) : mulWords p pinv a b out = out (mulWords p pinv a b id) :=
  reduce_out _ _ _ _

/-- The CIOS product is `a b R⁻¹` mod `p`, below `p`, with `R = 2 ^ (32 n)`. -/
theorem Internal.mulWords_spec {p : Nat → UInt64} {pinv : UInt64} (hp : Fits n p 0)
    (hpinv : (num n p 0 * pinv.toNat + 1) % 2 ^ 32 = 0) {a : Nat → UInt64} (ha : Fits n a 0)
    (hA : num n a 0 < num n p 0) {b : Nat → UInt64} (hb : Fits n b 0) :
    Fits n (Words.word (mulWords (n := n) p pinv a b id)) 0 ∧
      num n (Words.word (mulWords (n := n) p pinv a b id)) 0 < num n p 0 ∧
      2 ^ (32 * n) * num n (Words.word (mulWords (n := n) p pinv a b id)) 0 % num n p 0 =
        num n a 0 * num n b 0 % num n p 0 := by
  have hP := pos_of_pinv hpinv
  have hbi := lt_of_fits hb
  let Inv (i : Nat) (st : Words.W n × UInt64) : Prop :=
    Fits n (Words.word st.1) 0 ∧ value st < 2 * num n p 0 ∧
      ∃ K, 2 ^ (32 * i) * value st = num n a 0 * num i b 0 + K * num n p 0
  have hinv : Inv (0 + n) (loop n (step p pinv a b) 0 (Words.zero, 0)) := by
    apply loop_induct
    · refine ⟨zero_spec.1, ?_, 0, ?_⟩
      · simp only [value, zero_spec.2, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
        omega
      · simp [value, zero_spec.2, num]
    · intro i st _ hi ⟨hf, hv, K, hK⟩
      obtain ⟨fs, vs, m, es⟩ := step_spec hp hpinv ha hA b (i := i)
        (by have := hbi i (by omega); rwa [Nat.zero_add] at this) hf hv
      refine ⟨fs, vs, K + 2 ^ (32 * i) * m, ?_⟩
      rw [radix_succ, num_snoc, Nat.zero_add, Nat.mul_assoc, Nat.mul_left_comm, es]
      generalize value (step p pinv a b i st) = V' at *
      generalize 2 ^ (32 * i) = X at *
      grind
  rw [Nat.zero_add] at hinv
  obtain ⟨hf, hv, K, hK⟩ := hinv
  unfold mulWords
  rw [Words.fold_eq]
  generalize loop n (step p pinv a b) 0 ((Words.zero : Words.W n), 0) = st at *
  obtain ⟨fr, er⟩ := reduce_spec hp hf hv
  refine ⟨fr, ?_, ?_⟩
  · rw [er]
    exact Nat.mod_lt _ hP
  · rw [er, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, hK, Nat.add_mul_mod_self_right]

/-- Whether the integer of the words `t` is below that of the words `p`: `t - p` borrows. -/
@[inline] def ltWords (t : Words.W n) (p : Nat → UInt64) : Bool :=
  (Words.subb t p 0 0).2 != 0

/-! ## The product in two parts -/

section Parts

/-- Zeros load as the words of zero. -/
theorem Internal.load_zero : Words.load (n := n) (fun _ => 0) 0 = Words.zero :=
  Words.ext _ _ fun i hi => by rw [Words.word_load _ _ _ hi, Words.word_zero]

variable [Limbs n]

/-- `m` rows of the CIOS product from row `k`, from the words `acc` with `0` above them. -/
@[inline] def mulRows (m : Nat) [Words m] (p : Nat → UInt64) (pinv : UInt64) (a b : Nat → UInt64)
    (k : Nat) (acc : Nat → UInt64) : Words.W n × UInt64 :=
  Words.fold (n := m) (step p pinv a b) k (Words.load (n := n) acc 0, 0)

/-- The first `k` rows of the CIOS product, as stored limbs.

The word above them is `0` when `2 p ≤ R`, so the limbs hold the whole state. -/
@[inline] def mulLow (k : Nat) [Words k] (p : Nat → UInt64) (pinv : UInt64)
    (a b : Nat → UInt64) : Limbs.T n :=
  Limbs.pack (mulRows (n := n) k p pinv a b 0 fun _ => 0).1

/-- The rows of the CIOS product from row `k`, from the limbs `lo` of the rows before them.

The final reduction follows, and its result goes to `out`. -/
@[inline] def mulHigh (m : Nat) [Words m] (p : Nat → UInt64) (pinv : UInt64) (a b : Nat → UInt64)
    (k : Nat) (lo : Limbs.T n) {β : Type} (out : Words.W n → β) : β :=
  let st := mulRows (n := n) m p pinv a b k (Limbs.get lo)
  reduce p st.1 st.2 out

/-- Fitting words, stored as limbs and loaded back, are the same words. -/
theorem Internal.load_pack {t : Words.W n} (h : Fits n (Words.word t) 0) :
    Words.load (n := n) (Limbs.get (Limbs.pack (n := n) t)) 0 = t := by
  have hl := lt_of_fits h
  refine Words.ext _ _ fun i hi => UInt64.toNat_inj.mp ?_
  rw [Words.word_load _ _ _ hi, Nat.zero_add, Limbs.get_pack _ _ hi,
    Nat.mod_eq_of_lt (by simpa using hl i hi)]

/-- The product in two parts is the CIOS product, when `2 p ≤ R`.

The rows keep the state below `2 p`, so the word above the limbs of the first part is `0`. -/
theorem mulHigh_mulLow {k m : Nat} [Words k] [Words m] (hkm : k + m = n) {p : Nat → UInt64}
    {pinv : UInt64} (hp : Fits n p 0) (hpinv : (num n p 0 * pinv.toNat + 1) % 2 ^ 32 = 0)
    (hR : 2 * num n p 0 ≤ 2 ^ (32 * n)) {a : Nat → UInt64} (ha : Fits n a 0)
    (hA : num n a 0 < num n p 0) {b : Nat → UInt64} (hb : Fits n b 0) {β : Type}
    (out : Words.W n → β) :
    mulHigh m p pinv a b k (mulLow (n := n) k p pinv a b) out = mulWords p pinv a b out := by
  have hbi := lt_of_fits hb
  have hlow := loop_induct (fun _ st => Fits n (Words.word st.1) 0 ∧ value st < 2 * num n p 0)
    (step p pinv a b) k 0 ((Words.zero : Words.W n), 0) ⟨zero_spec.1, by
      simp only [value, zero_spec.2, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
      have := pos_of_pinv hpinv
      omega⟩ fun i st _ hi ⟨hf, hv⟩ => by
      obtain ⟨fs, vs, _⟩ := step_spec hp hpinv ha hA b (i := i)
        (by have := hbi i (by omega); rwa [Nat.zero_add] at this) hf hv
      exact ⟨fs, vs⟩
  have e := loop_add (step p pinv a b) k m 0 ((Words.zero : Words.W n), 0)
  rw [hkm, Nat.zero_add] at e
  unfold mulHigh mulLow mulRows mulWords
  rw [load_zero, Words.fold_eq, Words.fold_eq, Words.fold_eq, e]
  generalize loop k (step p pinv a b) 0 ((Words.zero : Words.W n), 0) = st at hlow ⊢
  obtain ⟨hf, hv⟩ := hlow
  have htop : st.2 = 0 := by
    simp only [value] at hv
    have : 2 ^ (32 * n) * st.2.toNat < 2 ^ (32 * n) * 1 := by omega
    exact UInt64.toNat_inj.mp (Nat.lt_one_iff.mp (Nat.lt_of_mul_lt_mul_left this))
  rw [load_pack hf, show ((st.1, 0) : Words.W n × UInt64) = st from Prod.ext rfl htop.symm]

end Parts

end Generic

end EthLib.Cryptography.Montgomery

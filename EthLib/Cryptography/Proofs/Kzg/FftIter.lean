module

public import EthLib.Cryptography.Proofs.Kzg.Fft
public import EthLib.Cryptography.Proofs.Kzg.BitReversal
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Proofs: the iterative FFT computes the recursive one

Take `n = 2^k` values in bit-reversed order, and run the stages.

After `s` stages, block `b` of `2^s` values holds the recursive FFT of `2^s` input values.

They are `2^(k - s)` apart, from the bit reversal of `b` over `k - s` bits.

A stage joins two blocks by the butterflies of one step of the recursion.

After the last stage, the one block holds the recursive FFT of all the values.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.BitReversal

/-! ## Selections of values -/

/-- `len` values of `v`, `d` apart, from index `c`. -/
def sel (v : Array Fr) (c d len : Nat) : Array Fr :=
  Array.ofFn (n := len) fun i => v[c + d * i.val]!

@[simp] theorem size_sel (v : Array Fr) (c d len : Nat) : (sel v c d len).size = len := by
  simp [sel]

theorem getElem!_sel (v : Array Fr) (c d len i : Nat) (h : i < len) :
    (sel v c d len)[i]! = v[c + d * i]! := by
  rw [getElem!_pos (sel v c d len) i (by simpa using h)]
  simp [sel]

/-- The even values of a selection are a selection, twice as far apart. -/
theorem fftHalve_sel_zero (v : Array Fr) (c d len : Nat) :
    fftHalve (sel v c d (2 * len)) 0 = sel v c (2 * d) len := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [size_sel] at h2
    rw [getElem_fftHalve, ← getElem!_pos (sel v c (2 * d) len) i (by simpa using h2),
      getElem!_sel _ _ _ _ _ (by omega), getElem!_sel _ _ _ _ _ h2]
    congr 1
    ring

/-- The odd values of a selection are a selection, twice as far apart, one step further. -/
theorem fftHalve_sel_one (v : Array Fr) (c d len : Nat) :
    fftHalve (sel v c d (2 * len)) 1 = sel v (c + d) (2 * d) len := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [size_sel] at h2
    rw [getElem_fftHalve, ← getElem!_pos (sel v (c + d) (2 * d) len) i (by simpa using h2),
      getElem!_sel _ _ _ _ _ (by omega), getElem!_sel _ _ _ _ _ h2]
    congr 1
    ring

/-- All the values, one apart, from index `0`. -/
theorem sel_self (v : Array Fr) : sel v 0 1 v.size = v := by
  apply Array.ext
  · simp
  · intro i h1 h2
    rw [← getElem!_pos (sel v 0 1 v.size) i h1, getElem!_sel _ _ _ _ _ h2,
      getElem!_pos v _ (by simpa using h2)]
    simp

/-! ## Bit reversal of `2 b` and `2 b + 1` -/

/-- Reversing the bits of `2 b` over `j + 1` bits reverses those of `b` over `j` bits. -/
theorem reverseBitsAux_two_mul (b j : Nat) :
    reverseBitsAux (2 * b) 0 (j + 1) = reverseBitsAux b 0 j := by
  rw [reverseBitsAux, Nat.and_one_is_mod, Nat.shiftRight_one]
  congr 1
  · omega
  · simp

/-- The accumulator of the bit reversal lands above the reversed bits. -/
theorem reverseBitsAux_acc (x r j : Nat) :
    reverseBitsAux x r j = r * 2 ^ j + reverseBitsAux x 0 j := by
  induction j generalizing x r with
  | zero => simp [reverseBitsAux]
  | succ j ih =>
    rw [reverseBitsAux, reverseBitsAux, ih, ih (x >>> 1) (0 <<< 1 ||| _),
      Nat.and_one_is_mod, Nat.zero_shiftLeft, Nat.zero_or,
      ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.shiftLeft_eq]
    ring

/-- Reversing the bits of `2 b + 1` over `j + 1` bits gives `2^j` plus those of `b` over `j`. -/
theorem reverseBitsAux_two_mul_add_one (b j : Nat) :
    reverseBitsAux (2 * b + 1) 0 (j + 1) = 2 ^ j + reverseBitsAux b 0 j := by
  rw [reverseBitsAux, Nat.and_one_is_mod, Nat.shiftRight_one,
    show (2 * b + 1) / 2 = b by omega, show (2 * b + 1) % 2 = 1 by omega, reverseBitsAux_acc]
  simp

/-! ## The stages -/

/-- Running `s + 1` stages is running `s` stages, then one on blocks `2^s` times larger. -/
theorem fftStages_succ (roots : Array Fr) (s : Nat) (x : Array Fr) (h : Nat) :
    fftStages roots (s + 1) x h = fftStage roots (fftStages roots s x h) (2 ^ s * h) := by
  induction s generalizing x h with
  | zero => simp [fftStages]
  | succ s ih =>
    show fftStages roots (s + 1) (fftStage roots x h) (2 * h) =
      fftStage roots (fftStages roots s (fftStage roots x h) (2 * h)) (2 ^ (s + 1) * h)
    rw [ih, pow_succ, Nat.mul_assoc]

/-- Entry `j` of block `b` after a stage on blocks of `2 h`, from the entries before it. -/
theorem getElem!_fftStage (roots x : Array Fr) {h b j : Nat} (hh : 0 < h)
    (hx : 2 * h * (b + 1) ≤ x.size) (hj : j < 2 * h) :
    (fftStage roots x h)[2 * h * b + j]! =
      if j < h then x[2 * h * b + j]! + x[2 * h * b + h + j]! * roots[x.size / (2 * h) * j]!
      else x[2 * h * b + (j - h)]! - x[2 * h * b + h + (j - h)]!
        * roots[x.size / (2 * h) * (j - h)]! := by
  have hi : 2 * h * b + j < x.size := by nlinarith
  have hdiv : (2 * h * b + j) / (2 * h) = b := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (2 * h * b + j) % (2 * h) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have ht : ∀ r, r < h → h * b + r < x.size / 2 := fun r hr => by
    have : 2 * (h * b + r) + 2 ≤ x.size := by nlinarith
    omega
  have htdiv : ∀ r, r < h → (h * b + r) / h = b := fun r hr => by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hr, Nat.zero_add]
  have htmod : ∀ r, r < h → (h * b + r) % h = r := fun r hr => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  rw [getElem!_pos (fftStage roots x h) _ (by simpa using hi)]
  simp only [fftStage, Array.getElem_ofFn, hdiv, hmod]
  split
  · rename_i hjh
    rw [getElem!_pos _ (h * b + j) (by simpa using ht j hjh)]
    simp only [Array.getElem_ofFn, htdiv j hjh, htmod j hjh]
  · rename_i hjh
    rw [show 2 * h * b + j - h = 2 * h * b + (j - h) by omega,
      show h * b + j - h = h * b + (j - h) by omega,
      getElem!_pos _ (h * b + (j - h)) (by simpa using ht (j - h) (by omega))]
    simp only [Array.getElem_ofFn, htdiv (j - h) (by omega), htmod (j - h) (by omega)]

/-! ## The invariant of the stages -/

/-- After `s` stages, each block holds the recursive FFT of its selection. -/
theorem getElem!_fftStages {k : Nat} (vals roots : Array Fr) (hn : vals.size = 2 ^ k)
    (s : Nat) (hs : s ≤ k) (b j : Nat) (hb : b < 2 ^ (k - s)) (hj : j < 2 ^ s) :
    (fftStages roots s (bitReversalPermutation vals) 1)[2 ^ s * b + j]! =
      (fftFieldAux (sel vals (reverseBitsAux b 0 (k - s)) (2 ^ (k - s)) (2 ^ s))
        (sel roots 0 (2 ^ (k - s)) (2 ^ s)))[j]! := by
  induction s generalizing b j with
  | zero =>
    obtain rfl : j = 0 := by simpa using hj
    simp only [pow_zero, Nat.sub_zero] at hb ⊢
    have hb' : b < (bitReversalPermutation vals).size := by
      rw [size_bitReversalPermutation, hn]; exact hb
    rw [fftStages, one_mul, Nat.add_zero, getElem!_pos _ b hb',
      getElem_bitReversalPermutation, fftFieldAux, ite_eq_left (by simp),
      getElem!_sel _ _ _ _ _ (by decide), hn, reverseBits, Nat.log2_two_pow]
    simp
  | succ s ih =>
    obtain ⟨e, rfl⟩ : ∃ e, k = s + 1 + e := ⟨k - (s + 1), by omega⟩
    have he1 : s + 1 + e - (s + 1) = e := by omega
    have he0 : s + 1 + e - s = e + 1 := by omega
    rw [he1] at hb ⊢
    have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
    have h2s : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
    have hsize : (fftStages roots s (bitReversalPermutation vals) 1).size
        = 2 * 2 ^ s * 2 ^ e := by
      rw [size_fftStages, size_bitReversalPermutation, hn, pow_add, h2s]
    have hstride : 2 * 2 ^ s * 2 ^ e / (2 * 2 ^ s) = 2 ^ e :=
      Nat.mul_div_cancel_left _ (by omega)
    have hb2 : b + 1 ≤ 2 ^ e := hb
    rw [fftStages_succ, mul_one, h2s, getElem!_fftStage _ _ hpos
        (by rw [hsize]; exact Nat.mul_le_mul_left _ hb2) (by omega),
      hsize, hstride]
    -- The model takes one step on the selection of `2^(s + 1)` values.
    rw [getElem_fftFieldAux_step _ _ (by simp; omega) j (by rw [h2s] at hj; simpa using hj)]
    simp only [size_sel, show 2 * 2 ^ s / 2 = 2 ^ s by omega]
    rw [fftHalve_sel_zero, fftHalve_sel_one, show (2 * 2 ^ s : Nat) = 2 * (2 ^ s) from rfl,
      fftHalve_sel_zero, show 2 * 2 ^ e = 2 ^ (e + 1) by rw [pow_succ]; ring]
    -- The two halves are the blocks `2 b` and `2 b + 1` of the stage before.
    have hl : ∀ r, r < 2 ^ s →
        (fftStages roots s (bitReversalPermutation vals) 1)[2 * 2 ^ s * b + r]! =
          (fftFieldAux (sel vals (reverseBitsAux b 0 e) (2 ^ (e + 1)) (2 ^ s))
            (sel roots 0 (2 ^ (e + 1)) (2 ^ s)))[r]! := by
      intro r hr
      have := ih (by omega) (2 * b) r (by rw [he0, pow_succ]; omega) hr
      rw [he0, reverseBitsAux_two_mul] at this
      rw [← this]
      congr 2
      ring
    have hr : ∀ r, r < 2 ^ s →
        (fftStages roots s (bitReversalPermutation vals) 1)[2 * 2 ^ s * b + 2 ^ s + r]! =
          (fftFieldAux (sel vals (reverseBitsAux b 0 e + 2 ^ e) (2 ^ (e + 1)) (2 ^ s))
            (sel roots 0 (2 ^ (e + 1)) (2 ^ s)))[r]! := by
      intro r hr
      have := ih (by omega) (2 * b + 1) r (by rw [he0, pow_succ]; omega) hr
      rw [he0, reverseBitsAux_two_mul_add_one, Nat.add_comm (2 ^ e)] at this
      rw [← this]
      congr 2
      ring
    have hroot : ∀ r, r < 2 ^ s → roots[2 ^ e * r]! = (sel roots 0 (2 ^ e) (2 * 2 ^ s))[r]! := by
      intro r hr
      rw [getElem!_sel _ _ _ _ _ (by omega), Nat.zero_add]
    split
    · rename_i hjs
      rw [hl j hjs, hr j hjs, hroot j hjs]
    · rename_i hjs
      rw [hl (j - 2 ^ s) (by omega), hr (j - 2 ^ s) (by omega), hroot (j - 2 ^ s) (by omega)]

/-! ## The transform -/

/-- The iterative FFT computes the recursive one, for a power-of-two length. -/
theorem fftFieldIter_eq {k : Nat} (vals roots : Array Fr) (hn : vals.size = 2 ^ k)
    (hr : roots.size = 2 ^ k) :
    fftFieldIter vals roots = fftFieldAux vals roots := by
  apply Array.ext
  · simp [fftFieldIter, size_bitReversalPermutation]
  · intro j h1 h2
    rw [← getElem!_pos _ j h1, ← getElem!_pos _ j h2]
    have h := getElem!_fftStages vals roots hn k le_rfl 0 j (by simp)
      (by simpa [hn] using h2)
    simp only [Nat.sub_self, pow_zero, mul_zero, Nat.zero_add] at h
    rw [fftFieldIter, hn, Nat.log2_two_pow, h, show reverseBitsAux 0 0 0 = 0 from rfl,
      ← hn, sel_self, hn, ← hr, sel_self]

/-- For a power-of-two length, the FFT is the recursive model, on the roots or reversed roots. -/
theorem fftField_def {k : Nat} (vals rootsOfUnity : Array Fr) (inv : Bool)
    (hn : vals.size = 2 ^ k) (hr : rootsOfUnity.size = 2 ^ k) :
    fftField vals rootsOfUnity inv =
      if inv then
        (fftFieldAux vals (Array.ofFn (n := rootsOfUnity.size) fun i =>
          if i.val = 0 then rootsOfUnity[0]!
          else rootsOfUnity[rootsOfUnity.size - i.val]!)).map
            (· * (Fr.ofNat vals.size).inverse)
      else fftFieldAux vals rootsOfUnity := by
  cases inv with
  | false => exact fftFieldIter_eq vals rootsOfUnity hn hr
  | true =>
    simp only [fftField, ↓reduceIte]
    rw [fftFieldIter_eq vals _ hn (by simpa using hr)]

end EthLib.Cryptography.Kzg

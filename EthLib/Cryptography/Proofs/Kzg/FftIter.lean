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

/-- An entry of a vector, read with a proof, is the entry of its array read with a default. -/
theorem Vector.getElem_eq_getElem!_toArray {α : Type _} [Inhabited α] {n : Nat} (x : Vector α n)
    {i : Nat} (h : i < n) :
    x[i] = x.toArray[i]! := by
  rw [getElem!_pos x.toArray i (by simpa using h), Vector.getElem_toArray]

/-- Entry `j` of block `b` after a stage on `m` blocks of `2 h`, from the entries before it. -/
theorem getElem!_fftStage {n : Nat} (roots x : Vector Fr n) {m h b j : Nat}
    (hn : n = m * (2 * h)) (hb : b < m) (hj : j < 2 * h) :
    (fftStage roots x m h hn).toArray[2 * h * b + j]! =
      if j < h then
        x.toArray[2 * h * b + j]! + x.toArray[2 * h * b + h + j]! * roots.toArray[m * j]!
      else x.toArray[2 * h * b + (j - h)]! - x.toArray[2 * h * b + h + (j - h)]!
        * roots.toArray[m * (j - h)]! := by
  have hh : 0 < h := by omega
  have hi : 2 * h * b + j < n := by rw [hn]; nlinarith
  have hdiv : (2 * h * b + j) / (2 * h) = b := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (2 * h * b + j) % (2 * h) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have htdiv : ∀ r, r < h → (h * b + r) / h = b := fun r hr => by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hr, Nat.zero_add]
  have htmod : ∀ r, r < h → (h * b + r) % h = r := fun r hr => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  rw [getElem!_pos _ _ (by simpa using hi), Vector.getElem_toArray]
  simp only [fftStage, Vector.getElem_ofFn, hdiv, hmod]
  split
  · rename_i hjh
    simp only [Fin.getElem_fin, htdiv j hjh, htmod j hjh, Vector.getElem_eq_getElem!_toArray]
  · rename_i hjh
    simp only [htdiv (j - h) (by omega), htmod (j - h) (by omega),
      Vector.getElem_eq_getElem!_toArray]
    rw [show 2 * h * b + j - h = 2 * h * b + (j - h) by omega]

/-- The selections that block `b` of `2^s` values holds after `s` stages, transformed. -/
def stageModel (vals roots : Array Fr) (k s b : Nat) : Array Fr :=
  fftFieldAux (sel vals (reverseBitsAux b 0 (k - s)) (2 ^ (k - s)) (2 ^ s))
    (sel roots 0 (2 ^ (k - s)) (2 ^ s))

/-- The invariant of the stages: after `s` stages, each block holds the model of its selection. -/
def StagesDone {n : Nat} (vals roots : Array Fr) (k s : Nat) (x : Vector Fr n) : Prop :=
  ∀ b j, b < 2 ^ (k - s) → j < 2 ^ s → x.toArray[2 ^ s * b + j]! = (stageModel vals roots k s b)[j]!

/-- One stage takes the invariant from `s` stages to `s + 1`. -/
theorem stagesDone_fftStage {n k s : Nat} (vals : Array Fr) (roots : Vector Fr n)
    (hs : s < k) (x : Vector Fr n) (hx : StagesDone vals roots.toArray k s x)
    (hn : n = 2 ^ (k - (s + 1)) * (2 * 2 ^ s)) :
    StagesDone vals roots.toArray k (s + 1) (fftStage roots x (2 ^ (k - (s + 1))) (2 ^ s) hn) := by
  intro b j hb hj
  obtain ⟨e, rfl⟩ : ∃ e, k = s + 1 + e := ⟨k - (s + 1), by omega⟩
  have he1 : s + 1 + e - (s + 1) = e := by omega
  have he0 : s + 1 + e - s = e + 1 := by omega
  rw [he1] at hb
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  have h2s : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  rw [h2s] at hj ⊢
  rw [getElem!_fftStage _ _ hn (by rw [he1]; exact hb) hj, he1]
  unfold stageModel
  rw [he1, h2s]
  -- The model takes one step on the selection of `2^(s + 1)` values.
  rw [getElem_fftFieldAux_step _ _ (by rw [size_sel]; omega) j (by rw [size_sel]; exact hj)]
  simp only [size_sel, show 2 * 2 ^ s / 2 = 2 ^ s by omega]
  rw [fftHalve_sel_zero, fftHalve_sel_one, show (2 * 2 ^ s : Nat) = 2 * (2 ^ s) from rfl,
    fftHalve_sel_zero, show 2 * 2 ^ e = 2 ^ (e + 1) by rw [pow_succ]; ring]
  -- The two halves are the blocks `2 b` and `2 b + 1` of the stage before.
  have hl : ∀ r, r < 2 ^ s → x.toArray[2 * 2 ^ s * b + r]! =
      (fftFieldAux (sel vals (reverseBitsAux b 0 e) (2 ^ (e + 1)) (2 ^ s))
        (sel roots.toArray 0 (2 ^ (e + 1)) (2 ^ s)))[r]! := by
    intro r hr
    have := hx (2 * b) r (by rw [he0, pow_succ]; omega) hr
    unfold stageModel at this
    rw [he0, reverseBitsAux_two_mul] at this
    rw [← this]
    congr 2
    ring
  have hr : ∀ r, r < 2 ^ s → x.toArray[2 * 2 ^ s * b + 2 ^ s + r]! =
      (fftFieldAux (sel vals (reverseBitsAux b 0 e + 2 ^ e) (2 ^ (e + 1)) (2 ^ s))
        (sel roots.toArray 0 (2 ^ (e + 1)) (2 ^ s)))[r]! := by
    intro r hr
    have := hx (2 * b + 1) r (by rw [he0, pow_succ]; omega) hr
    unfold stageModel at this
    rw [he0, reverseBitsAux_two_mul_add_one, Nat.add_comm (2 ^ e)] at this
    rw [← this]
    congr 2
    ring
  have hroot : ∀ r, r < 2 ^ s →
      roots.toArray[2 ^ e * r]! = (sel roots.toArray 0 (2 ^ e) (2 * 2 ^ s))[r]! := by
    intro r hr
    rw [getElem!_sel _ _ _ _ _ (by omega), Nat.zero_add]
  split
  · rename_i hjs
    rw [hl j hjs, hr j hjs, hroot j hjs]
  · rename_i hjs
    rw [hl (j - 2 ^ s) (by omega), hr (j - 2 ^ s) (by omega), hroot (j - 2 ^ s) (by omega)]

/-- The remaining `c` stages take the invariant from `s` stages to all `k`. -/
theorem stagesDone_fftStages {n k : Nat} (vals : Array Fr) (roots : Vector Fr n) :
    ∀ (c s : Nat) (x : Vector Fr n) (h : Nat) (hn : n = 2 ^ c * h),
      s + c = k → h = 2 ^ s → StagesDone vals roots.toArray k s x →
      StagesDone vals roots.toArray k k (fftStages roots c x h hn)
  | 0, s, x, h, hn, hsc, _, hx => by
    rw [Nat.add_zero] at hsc
    subst hsc
    exact hx
  | c + 1, s, x, h, hn, hsc, hh, hx => by
    subst hh
    rw [fftStages]
    refine stagesDone_fftStages vals roots c (s + 1) _ _ _ (by omega)
      (by rw [pow_succ]; ring) ?_
    have hc : c = k - (s + 1) := by omega
    subst hc
    exact stagesDone_fftStage vals roots (by omega) x hx _

/-- Before any stage, the values in bit-reversed order hold the invariant. -/
theorem stagesDone_zero {n k : Nat} (vals roots : Array Fr) (hn : vals.size = 2 ^ k)
    (x : Vector Fr n) (hx : x.toArray = bitReversalPermutation vals) :
    StagesDone vals roots k 0 x := by
  intro b j hb hj
  obtain rfl : j = 0 := by simpa using hj
  simp only [pow_zero, Nat.sub_zero] at hb ⊢
  have hb' : b < (bitReversalPermutation vals).size := by
    rw [size_bitReversalPermutation, hn]; exact hb
  rw [one_mul, Nat.add_zero, hx, getElem!_pos _ b hb', getElem_bitReversalPermutation,
    stageModel, fftFieldAux, ite_eq_left (by simp), getElem!_sel _ _ _ _ _ (by decide), hn,
    reverseBits, Nat.log2_two_pow]
  simp

/-! ## The transform -/

/-- The iterative FFT computes the recursive one, for a power-of-two length. -/
theorem fftFieldIter_eq {k : Nat} (vals roots : Array Fr) (hn : vals.size = 2 ^ k)
    (hr : roots.size = 2 ^ k) :
    fftFieldIter vals roots = fftFieldAux vals roots := by
  have hshape : vals.size = 2 ^ vals.size.log2 ∧ roots.size = vals.size := by
    rw [hn, Nat.log2_two_pow]; exact ⟨rfl, hr⟩
  rw [fftFieldIter, dite_eq_left hshape]
  apply Array.ext
  · simp
  · intro j h1 h2
    rw [← getElem!_pos _ j h1, ← getElem!_pos _ j h2]
    -- Run every stage from the values in bit-reversed order.
    have hlog : vals.size.log2 = k := by rw [hn, Nat.log2_two_pow]
    have h := stagesDone_fftStages vals ⟨roots, hshape.2⟩ vals.size.log2 0
      ⟨bitReversalPermutation vals, by simp [size_bitReversalPermutation]⟩ 1
      (by rw [Nat.mul_one]; exact hshape.1) (by omega) (by simp)
      (stagesDone_zero vals roots hn _ rfl) 0 j (by simp) (by simpa [hn] using h2)
    simp only [mul_zero, Nat.zero_add] at h
    rw [h, stageModel, Nat.sub_self, pow_zero, show reverseBitsAux 0 0 0 = 0 from rfl,
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
    congr 2
    apply Array.ext (by simp)
    intro i h1 h2
    simp only [Array.getElem_ofFn]
    split
    · rename_i hi0
      rw [getElem!_pos _ 0 (by simp at h1; omega)]
      simp [hi0]
    · rename_i hi0
      simp only [Array.size_ofFn] at h1
      rw [getElem!_pos _ _ (by omega)]
      simp [Nat.mod_eq_of_lt (show rootsOfUnity.size - i < rootsOfUnity.size by omega)]

end EthLib.Cryptography.Kzg

module

public import EthLib.Cryptography.Bls
public import EthLib.Cryptography.Kzg.Constants
public import EthLib.Cryptography.Kzg.BitReversal

/-!
# `Fft`

Number-theoretic transforms over `Fr`, including a coset variant.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)

open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal

/-- Entries `start`, `start + 2`, `start + 4` and so on of `xs`: the even or the odd entries. -/
def everyOther {α : Type _} {k : Nat} (xs : Vector α (2 ^ (k + 1))) (start : Fin 2) :
    Vector α (2 ^ k) :=
  Vector.ofFn fun i => xs[start.val + 2 * i.val]'(by
    have hi := i.isLt
    have hs := start.isLt
    have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
    omega)

/-! ## Index bounds of the stages -/

/-- The second value of pair `j`, in `m` blocks of `2 h` values, lies inside the blocks. -/
theorem stage_pair_lt {j m h : Nat} (hj : j < m * h) :
    2 * h * (j / h) + h + j % h < m * (2 * h) := by
  have hh : 0 < h := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hj
  have hq : j / h < m := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have hle := Nat.mul_le_mul_left (2 * h) hq
  have hr := Nat.mod_lt j hh
  rw [Nat.mul_succ] at hle
  rw [Nat.mul_comm m]
  omega

/-- The root of pair `j`, at stride `m`, lies inside `m` blocks of `2 h` roots. -/
theorem stage_root_lt {j m h : Nat} (hj : j < m * h) : m * (j % h) < m * (2 * h) := by
  have hh : 0 < h := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hj
  have hm : 0 < m := Nat.pos_of_ne_zero fun m0 => by simp [m0] at hj
  exact Nat.mul_lt_mul_of_pos_left (Nat.lt_of_lt_of_le (Nat.mod_lt j hh) (by omega)) hm

/-- Value `i` of `m` blocks of `2 h` values belongs to pair `h * b + r'`.

Here `b` is its block and `r'` its offset, less `h` in the second half of the block. -/
theorem stage_product_lt {i m h r' : Nat} (hi : i < m * (2 * h)) (hr : r' < h) :
    h * (i / (2 * h)) + r' < m * h := by
  have hb : i / (2 * h) < m := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have := Nat.mul_le_mul_left h hb
  rw [Nat.mul_succ] at this
  rw [Nat.mul_comm m]
  omega

/-- One stage of the iterative FFT, on `m` blocks of `2 h` values.

In each block, value `r < h` pairs with value `r + h`.

The second value is multiplied by a root of unity, once.

The pair becomes the sum and the difference of the first value and that product.

The root is entry `r * m` of the roots. -/
def fftStage {n : Nat} (roots x : Vector Fr n) (m h : Nat) (hn : n = m * (2 * h)) :
    Vector Fr n :=
  let t := Vector.ofFn (n := m * h) fun j =>
    x[2 * h * (j.val / h) + h + j.val % h]'(hn ▸ stage_pair_lt j.isLt) *
      roots[m * (j.val % h)]'(hn ▸ stage_root_lt j.isLt)
  Vector.ofFn fun i =>
    let b := i.val / (2 * h)
    let r := i.val % (2 * h)
    if hr : r < h then
      x[i] + t[h * b + r]'(stage_product_lt (hn ▸ i.isLt) hr)
    else
      have hi : i.val < m * (2 * h) := hn ▸ i.isLt
      have hh : 0 < h := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
      have hr2 : r < 2 * h := Nat.mod_lt _ (by omega)
      x[i.val - h]'(by have := i.isLt; omega) -
        t[h * b + (r - h)]'(stage_product_lt (hn ▸ i.isLt) (by omega))

/-- The stages of the iterative FFT, for blocks of `2 h`, `4 h`, and so on.

There are `2^s` blocks of `2 h` values for the first stage, so `n = 2^s * h`. -/
def fftStages {n : Nat} (roots : Vector Fr n) :
    (s : Nat) → Vector Fr n → (h : Nat) → n = 2 ^ s * h → Vector Fr n
  | 0, x, _, _ => x
  | s + 1, x, h, hn =>
    have hn' : n = 2 ^ s * (2 * h) := by rw [hn, Nat.pow_succ, Nat.mul_assoc]
    fftStages roots s (fftStage roots x (2 ^ s) h hn') (2 * h) hn'

/-- The radix-2 Cooley-Tukey FFT, iterative.

The values are put in bit-reversed order, then each of the `log2 n` stages doubles the block size.

After stage `s`, each block of `2^s` values is the FFT of the values its indices select.

The values and the roots of unity must have the same length, a power of two.

Values of any other shape have no transform, and they come back unchanged. -/
def fftFieldIter (vals roots : Array Fr) : Array Fr :=
  if h : vals.size = 2 ^ vals.size.log2 ∧ roots.size = vals.size then
    (fftStages ⟨roots, h.2⟩ vals.size.log2
      ⟨bitReversalPermutation vals, by simp [bitReversalPermutation]⟩ 1
      (by rw [Nat.mul_one]; exact h.1)).toArray
  else vals

/-- The forward FFT, or the inverse FFT when `inv` is true.

The inverse reverses the roots of unity and divides each output by the length.

The length must be a power of two, and every caller passes one. -/
def fftField
    (vals : Array Fr) (rootsOfUnity : Array Fr)
    (inv : Bool := false) : Array Fr :=
  if inv then
    let invlen := (Fr.ofNat vals.size).inverse
    -- Root `i` of the inverse is root `n - i` of the forward transform, and root `0` stays.
    let n := rootsOfUnity.size
    let reversed := Array.ofFn (n := n) fun i =>
      rootsOfUnity[(n - i.val) % n]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt))
    (fftFieldIter vals reversed).map (· * invlen)
  else
    fftFieldIter vals rootsOfUnity

/-- The FFT in `G1` of `2^k` points, by the Cooley-Tukey recursion.

```text
    out[i] = sum_j [rootsOfUnity[i]^j] vals[j]
```

The butterflies are those of the FFT over `Fr`.

Each product by a root is a scalar multiplication. -/
def fftG1Vector : (k : Nat) → Vector Bls.G1 (2 ^ k) → Vector Fr (2 ^ k) → Vector Bls.G1 (2 ^ k)
  | 0, vals, _ => vals
  | k + 1, vals, rootsOfUnity =>
    let halfRoots := everyOther rootsOfUnity 0
    let l := fftG1Vector k (everyOther vals 0) halfRoots
    let r := fftG1Vector k (everyOther vals 1) halfRoots
    -- Each product [root_i] r_i serves two outputs, so it is computed once.
    -- The products are independent, so each runs as its own task.
    let tasks := Vector.ofFn (n := 2 ^ k) fun i => Task.spawn fun _ =>
      Bls.G1.mul r[i] (rootsOfUnity[i.val]'(by
        have hlt := i.isLt
        have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
        omega))
    let t := tasks.map Task.get
    Vector.ofFn fun i =>
      if h : i.val < 2 ^ k then Bls.G1.add l[i.val] t[i.val]
      else
        have hi : i.val - 2 ^ k < 2 ^ k := by
          have hlt := i.isLt
          have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
          omega
        Bls.G1.add l[i.val - 2 ^ k] (Bls.G1.neg t[i.val - 2 ^ k])

/-- The FFT in `G1` of the points `vals`.

The roots of unity have the length of the values, a power of two.

Points of any other shape have no transform, and they come back unchanged. -/
def fftG1 (vals : Array Bls.G1) (rootsOfUnity : Array Fr) : Array Bls.G1 :=
  if h : vals.size = 2 ^ vals.size.log2 ∧ rootsOfUnity.size = vals.size then
    (fftG1Vector vals.size.log2 ⟨vals, h.1⟩ ⟨rootsOfUnity, h.2.trans h.1⟩).toArray
  else vals

/-- Multiply successive values by successive powers of `factor`, starting at `shift`. -/
def shiftValsAux (factor : Fr) : Fr → List Fr → List Fr
  | _, [] => []
  | shift, v :: rest => (v * shift) :: shiftValsAux factor (shift * factor) rest

/-- Multiply `vals[i]` by `factor ^ i`, shifting the values onto a coset. -/
def shiftVals
    (vals : Array Fr) (factor : Fr)
    : Array Fr :=
  (shiftValsAux factor Fr.one vals.toList).toArray

/-- The FFT or the inverse FFT over a coset of the roots of unity.

It serves to divide by a polynomial that vanishes on the unshifted domain. -/
def cosetFftField
    (vals : Array Fr) (rootsOfUnity : Array Fr)
    (inv : Bool := false) : Array Fr :=
  let shiftFactor : Fr := Fr.ofNat PRIMITIVE_ROOT_OF_UNITY
  if inv then
    let post := fftField vals rootsOfUnity inv
    shiftVals post shiftFactor.inverse
  else
    let pre := shiftVals vals shiftFactor
    fftField pre rootsOfUnity inv

end EthLib.Cryptography.Kzg

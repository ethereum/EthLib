module

public import EthLib.Cryptography.Kzg.Fft
public import EthLib.Cryptography.Proofs.Bls.Fr
public import EthLib.Cryptography.Proofs.Kzg.BitReversal
public import Mathlib.Tactic.Set

/-!
# Proofs: the shape of the FFT helpers

Every transform keeps the size of its input.

The halving step picks out every other element.

The shift multiplies element `i` by `factor^i`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)

/-- Every other element of `xs`, starting at index `start`.

The recursive model below halves its arrays with it. -/
def fftHalve (xs : Array Fr) (start : Nat) : Array Fr :=
  Array.ofFn (n := xs.size / 2) fun i => xs[start + 2 * i.val]!

@[simp] theorem size_fftHalve (xs : Array Fr) (start : Nat) :
    (fftHalve xs start).size = xs.size / 2 := by
  simp [fftHalve]

/-- `fftHalve` picks out every other element, starting at `start`. -/
theorem getElem_fftHalve (xs : Array Fr) (start i : Nat)
    (h : i < (fftHalve xs start).size) :
    (fftHalve xs start)[i] = xs[start + 2 * i]! := by
  simp [fftHalve]

/-- The recursive radix-2 Cooley-Tukey FFT, the model that the proofs compare against.

It transforms the even and the odd values, then combines the two halves by butterflies.

The roots of unity must have the length of the values. -/
def fftFieldAux
    (vals : Array Fr) (rootsOfUnity : Array Fr)
    : Array Fr :=
  if vals.size ≤ 1 then
    vals
  else
    let halfRoots := fftHalve rootsOfUnity 0
    let l := fftFieldAux (fftHalve vals 0) halfRoots
    let r := fftFieldAux (fftHalve vals 1) halfRoots
    let n := vals.size
    let halfL := l.size  -- = n / 2
    -- Butterfly: for `i < n / 2`, with `t = r[i] * root[i]`, output `i` is `l[i] + t`.

    -- Output `i + n / 2` is `l[i] - t`, with the same root index `i`.
    Array.ofFn (n := n) fun i =>
      let baseIdx     := if i.val < halfL then i.val else i.val - halfL
      let lAt         := l[baseIdx]!
      let rAt         := r[baseIdx]!
      let yTimesRoot  := rAt * rootsOfUnity[baseIdx]!
      if i.val < halfL then lAt + yTimesRoot
      else                  lAt - yTimesRoot
termination_by vals.size
decreasing_by all_goals (simp [fftHalve]; omega)

@[simp] theorem size_fftFieldAux (vals rootsOfUnity : Array Fr) :
    (fftFieldAux vals rootsOfUnity).size = vals.size := by
  rw [fftFieldAux]
  split
  · rfl
  · simp

@[simp] theorem size_fftField (vals rootsOfUnity : Array Fr) (inv : Bool) :
    (fftField vals rootsOfUnity inv).size = vals.size := by
  have hiter : ∀ roots, (fftFieldIter vals roots).size = vals.size := by
    intro roots
    unfold fftFieldIter
    split
    · exact Vector.size_toArray _
    · rfl
  cases inv <;> simp [fftField, hiter]

/-! ## One step of the Cooley–Tukey recursion

One output of the model, for more than one value, is a butterfly of the two half transforms.

Proofs by induction on the size then need no more unfolding of arrays. -/

theorem getElem_fftFieldAux_step (vals roots : Array Fr)
    (hsz : 1 < vals.size) (p : Nat) (hp : p < vals.size) :
    (fftFieldAux vals roots)[p]! =
      (if p < vals.size / 2
        then (fftFieldAux (fftHalve vals 0) (fftHalve roots 0))[p]!
              + (fftFieldAux (fftHalve vals 1) (fftHalve roots 0))[p]!
                * roots[p]!
        else (fftFieldAux (fftHalve vals 0) (fftHalve roots 0))[p - vals.size / 2]!
              - (fftFieldAux (fftHalve vals 1) (fftHalve roots 0))[p - vals.size / 2]!
                * roots[p - vals.size / 2]!) := by
  -- Name the two half transforms, so that the unfolding below touches only the left side.
  set l := fftFieldAux (fftHalve vals 0) (fftHalve roots 0) with hl
  set r := fftFieldAux (fftHalve vals 1) (fftHalve roots 0) with hr
  rw [fftFieldAux, ite_eq_right (by omega : ¬ vals.size ≤ 1)]
  rw [getElem!_pos _ p (by simpa using hp)]
  -- Read the entry of the array, and fold the half transforms back.
  simp only [Array.getElem_ofFn, ← hl, ← hr]
  -- The first half has `n / 2` values, so the two conditions agree.
  have hlsize : l.size = vals.size / 2 := by
    rw [hl, size_fftFieldAux, size_fftHalve]
  rw [hlsize]
  split <;> rfl

@[simp] theorem length_shiftValsAux (factor shift : Fr) (l : List Fr) :
    (shiftValsAux factor shift l).length = l.length := by
  induction l generalizing shift with
  | nil => rfl
  | cons v rest ih => simp [shiftValsAux, ih]

@[simp] theorem size_shiftVals (vals : Array Fr) (factor : Fr) :
    (shiftVals vals factor).size = vals.size := by
  simp [shiftVals]

/-- Element `i` of `shiftValsAux factor shift l` is
`l[i] * (shift * factor ^ i)`. -/
theorem getElem_shiftValsAux (factor shift : Fr) (l : List Fr) (i : Nat)
    (h : i < (shiftValsAux factor shift l).length) :
    (shiftValsAux factor shift l)[i] =
      l[i]'(by rwa [length_shiftValsAux] at h) *
        (shift * Fr.powNat factor i) := by
  induction l generalizing shift i with
  | nil => exact absurd h (by simp)
  | cons v rest ih =>
    cases i with
    | zero =>
      simp only [shiftValsAux, List.getElem_cons_zero, Fr.powNat_zero,
        Fr.mul_mul_one]
    | succ i =>
      simp only [shiftValsAux, List.getElem_cons_succ]
      rw [ih, Fr.powNat_succ, ← Fr.mul_assoc shift factor]

/-- Element `i` of `shiftVals vals factor` is `vals[i] * factor ^ i`. -/
theorem getElem_shiftVals (vals : Array Fr) (factor : Fr) (i : Nat)
    (h : i < (shiftVals vals factor).size) :
    (shiftVals vals factor)[i] =
      vals[i]'(by rwa [size_shiftVals] at h) * Fr.powNat factor i := by
  have hl : i < (shiftValsAux factor Fr.one vals.toList).length := by
    simpa [shiftVals] using h
  show (shiftValsAux factor Fr.one vals.toList).toArray[i] = _
  rw [List.getElem_toArray, getElem_shiftValsAux factor Fr.one vals.toList i hl,
    Fr.mul_one_mul, Array.getElem_toList]

@[simp] theorem size_cosetFftField (vals rootsOfUnity : Array Fr)
    (inv : Bool) :
    (cosetFftField vals rootsOfUnity inv).size = vals.size := by
  cases inv <;> simp [cosetFftField]

end EthLib.Cryptography.Kzg

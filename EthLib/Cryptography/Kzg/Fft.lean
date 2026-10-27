import EthLib.Cryptography.Bls
import EthLib.Cryptography.Kzg.Constants

/-!
# `Fft`

Number-theoretic transforms over `Fr`, including a coset variant.
-/

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)

open EthLib.Cryptography.Kzg.Constants

/-- Every other element of `xs`, starting at index `start`. -/
def fftHalve (xs : Array Fr) (start : Nat) : Array Fr :=
  Array.ofFn (n := xs.size / 2) fun i => xs[start + 2 * i.val]!

/-- Cooley-Tukey radix-2 forward FFT. `rootsOfUnity` must have the same
length as `vals`. -/
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
    -- Butterfly: for each `i ∈ [0, n/2)` let `t = r[i] * rootsOfUnity[i]`,
    -- then write `l[i] + t` to `o[i]` and `l[i] - t` to `o[i + n/2]`.
    -- The same root index `i` (not `i + n/2`) is used for both halves.
    Array.ofFn (n := n) fun i =>
      let baseIdx     := if i.val < halfL then i.val else i.val - halfL
      let lAt         := l[baseIdx]!
      let rAt         := r[baseIdx]!
      let yTimesRoot  := rAt * rootsOfUnity[baseIdx]!
      if i.val < halfL then lAt + yTimesRoot
      else                  lAt - yTimesRoot
termination_by vals.size
decreasing_by all_goals (simp [fftHalve]; omega)

/-- Forward (`inv = false`) or inverse FFT (`inv = true`) over `vals`.
The inverse reverses the roots of unity and divides each output by
`len(vals)`. -/
def fftField
    (vals : Array Fr) (rootsOfUnity : Array Fr)
    (inv : Bool := false) : Array Fr :=
  let out :=
    if inv then
      let invlen := (Fr.ofNat vals.size).inverse
      -- Reverse: keep roots[0] then reverse roots[1..]
      let reversed := Array.ofFn (n := rootsOfUnity.size) fun i =>
        if i.val = 0 then rootsOfUnity[0]!
        else rootsOfUnity[rootsOfUnity.size - i.val]!
      (fftFieldAux vals reversed).map (· * invlen)
    else
      fftFieldAux vals rootsOfUnity
  -- Only (non-empty) power-of-two input lengths are legal: `fftHalve`
  -- silently truncates an odd length reached during recursion instead of
  -- failing, and the empty input has no well-defined transform.
  if vals.size.isPowerOfTwo then out
  else panicWith out s!"fftField: input length {vals.size} is not a power of two"

/-- Every other point of `xs`, starting at index `start`. -/
def fftHalveG1 (xs : Array Bls.G1) (start : Nat) : Array Bls.G1 :=
  Array.ofFn (n := xs.size / 2) fun i => xs[start + 2 * i.val]!

/-- Cooley-Tukey radix-2 FFT whose coefficients are points of G1.

```text
    out[i] = sum_j [rootsOfUnity[i]^j] vals[j]
```

The butterflies are those of `fftFieldAux`.

Each product by a root is a scalar multiplication.

`rootsOfUnity` has the length of `vals`, a power of two. -/
def fftG1 (vals : Array Bls.G1) (rootsOfUnity : Array Fr) : Array Bls.G1 :=
  if vals.size ≤ 1 then
    vals
  else
    let halfRoots := fftHalve rootsOfUnity 0
    let l := fftG1 (fftHalveG1 vals 0) halfRoots
    let r := fftG1 (fftHalveG1 vals 1) halfRoots
    let half := l.size
    -- Each product [root_i] r_i serves two outputs, so it is computed once.
    -- The products are independent, so each runs as its own task.
    let tasks := Array.ofFn (n := half) fun i => Task.spawn fun _ => Bls.G1.mul r[i.val]! rootsOfUnity[i.val]!
    let t := tasks.map Task.get
    Array.ofFn (n := vals.size) fun i =>
      if i.val < half then Bls.G1.add l[i.val]! t[i.val]!
      else Bls.G1.add l[i.val - half]! (Bls.G1.neg t[i.val - half]!)
termination_by vals.size
decreasing_by all_goals (simp [fftHalveG1]; omega)

/-- Multiply successive elements of `vals` by successive powers of
`factor`, starting at `shift`. -/
def shiftValsAux (factor : Fr) : Fr → List Fr → List Fr
  | _, [] => []
  | shift, v :: rest => (v * shift) :: shiftValsAux factor (shift * factor) rest

/-- Multiply `vals[i]` by `factor ^ i`, shifting the values onto a coset. -/
def shiftVals
    (vals : Array Fr) (factor : Fr)
    : Array Fr :=
  (shiftValsAux factor Fr.one vals.toList).toArray

/-- FFT/IFFT over a coset of the roots of unity. Useful for dividing by
a polynomial that vanishes on the unshifted domain. -/
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

import EthLib.Cryptography.Proofs.Kzg.CosetInverse

/-!
# Proofs: FFT outputs are polynomial evaluations

Entry `i` of the forward FFT is the polynomial evaluated at `w^i`.

```text
    fft(c)[i] = sum_j c_j * (w^i)^j = p(w^i)
```

The coset FFT first scales coefficient `j` by `k^j`.

That is the same as evaluating at `k * w^i`.
-/

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

private theorem fr_mul_pow (a b : Fr) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n := mul_pow a b n
private theorem fr_pow_mul (a : Fr) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := pow_mul a m n

/-- Coefficient evaluation is the finite sum defining the discrete Fourier transform. -/
theorem evalCoeffPolyAux_eq_sum (p : PolynomialCoeff) (x : Fr) (n : Nat) :
    evalCoeffPolyAux p x n = ∑ i ∈ Finset.range n, p[i]! * x ^ i := by
  induction n with
  | zero => simp [evalCoeffPolyAux]
  | succ n ih =>
    rw [evalCoeffPolyAux, ih, Finset.sum_range_succ, Bls.Fr.powNat_eq_pow]

/-- Forward FFT entries are evaluations of the actual coefficient array. -/
theorem getElem!_fftField_eval {k : Nat} {ω : Fr}
    (hω : IsPrimitiveRoot ω (2 ^ k))
    (vals roots : Array Fr) (hn : vals.size = 2 ^ k) (hrs : roots.size = 2 ^ k)
    (hroots : ∀ i, i < 2 ^ k → roots[i]! = ω ^ i)
    (j : Nat) (hj : j < 2 ^ k) :
    (fftField vals roots false)[j]! = evalPolyAt vals (ω ^ j) := by
  rw [show fftField vals roots false = fftFieldAux vals roots by exact fftField_def vals roots false]
  rw [getElem!_fftFieldAux_dft hω vals roots hn hrs hroots j hj]
  rw [evalPolyAt, evalCoeffPoly, evalCoeffPolyAux_eq_sum, hn]
  apply Finset.sum_congr rfl
  intro i _
  rw [← fr_pow_mul, Nat.mul_comm j i]

/-- Coefficient shifting corresponds to scaling the evaluation point. -/
theorem evalPolyAt_shiftVals (vals : Array Fr) (factor x : Fr) :
    evalPolyAt (shiftVals vals factor) x = evalPolyAt vals (factor * x) := by
  rw [evalPolyAt, evalPolyAt, evalCoeffPoly, evalCoeffPoly,
    evalCoeffPolyAux_eq_sum, evalCoeffPolyAux_eq_sum, size_shiftVals]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < vals.size := Finset.mem_range.mp hi
  rw [getElem!_pos (shiftVals vals factor) i (by simpa using hi'), getElem_shiftVals,
    ← getElem!_pos vals i hi', Bls.Fr.powNat_eq_pow, fr_mul_pow, Bls.Fr.mul_assoc]

/-- Forward coset FFT entries evaluate the polynomial at the shifted roots. -/
theorem getElem!_cosetFftField_eval {k : Nat} {ω : Fr}
    (hω : IsPrimitiveRoot ω (2 ^ k))
    (vals roots : Array Fr) (hn : vals.size = 2 ^ k) (hrs : roots.size = 2 ^ k)
    (hroots : ∀ i, i < 2 ^ k → roots[i]! = ω ^ i)
    (j : Nat) (hj : j < 2 ^ k) :
    (cosetFftField vals roots false)[j]! =
      evalPolyAt vals (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY * ω ^ j) := by
  simp only [cosetFftField, Bool.false_eq_true, ↓reduceIte]
  rw [getElem!_fftField_eval hω _ roots (by simpa using hn) hrs hroots j hj,
    evalPolyAt_shiftVals]

end EthLib.Cryptography.Kzg

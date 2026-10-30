module

public import EthLib.Cryptography.Proofs.Kzg.FftInverse
public import EthLib.Cryptography.Proofs.Bls.G1Order

/-!
# Proofs: the radix-2 FFT over `G1`

`fftG1` applies the Cooley-Tukey butterfly directly to `G1` points.

Field products become scalar multiplications in the prime-order subgroup, where `Fr.modulus * P = 0`.

```text
    even[q] + [roots[q]] odd[q]       (top half:    j = q)
    even[q] - [roots[q]] odd[q]       (bottom half: j = q + 2^k)
```

Each butterfly product runs in a `Task.spawn`.

Reading `.get` gives its value by definition.

This file proves:

- `fftG1` preserves input array length.
- `fftG1` preserves `Bls.G1.Valid` and prime-order torsion (`Fr.modulus * toPoint P = 0`).
- Entry `j` maps under `Bls.G1.toPoint` to `sum_{i < 2^k} (omega^(i * j)).val * toPoint vals[i]`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr G1)
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

private theorem fr_pow_zero (a : Fr) : a ^ 0 = 1 := pow_zero a
private theorem fr_pow_add (a : Fr) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := pow_add a m n
private theorem fr_pow_mul (a : Fr) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := pow_mul a m n
private theorem fr_one_pow (n : Nat) : (1 : Fr) ^ n = 1 := one_pow n
private theorem fr_mul_one (a : Fr) : a * 1 = a := mul_one a
private theorem fr_mul_neg (a b : Fr) : a * -b = -(a * b) := mul_neg a b
private theorem fr_neg_add_cancel (a : Fr) : -a + a = 0 := neg_add_cancel a

/-! ## `Fr` scalar action on `r`-torsion points of `G1` -/

/-- Multiplying an `r`-torsion curve point by `(a + b).val` splits into the sum of scalar multiples. -/
theorem nsmul_val_add_of_torsion {P : G1.curve.toAffine.Point}
    (htor : Fr.modulus • P = 0) (a b : Fr) :
    (a + b).val • P = a.val • P + b.val • P := by
  have hmod (m : Nat) : (m % Fr.modulus) • P = m • P := by
    conv_rhs => rw [← Nat.div_add_mod m Fr.modulus]
    rw [add_nsmul, Nat.mul_comm Fr.modulus (m / Fr.modulus), mul_nsmul',
      htor, nsmul_zero, zero_add]
  change ((a.val + b.val) % Fr.modulus) • P = a.val • P + b.val • P
  rw [hmod, add_nsmul]

/-- Multiplying an `r`-torsion curve point by `(a * b).val` composes the two scalar multiplications. -/
theorem nsmul_val_mul_of_torsion {P : G1.curve.toAffine.Point}
    (htor : Fr.modulus • P = 0) (a b : Fr) :
    (a * b).val • P = a.val • (b.val • P) := by
  have hmod (m : Nat) : (m % Fr.modulus) • P = m • P := by
    conv_rhs => rw [← Nat.div_add_mod m Fr.modulus]
    rw [add_nsmul, Nat.mul_comm Fr.modulus (m / Fr.modulus), mul_nsmul',
      htor, nsmul_zero, zero_add]
  change ((a.val * b.val) % Fr.modulus) • P = a.val • (b.val • P)
  rw [hmod, mul_nsmul']

/-- Multiplying an `r`-torsion curve point by `(-a).val` negates `a.val * P`. -/
theorem nsmul_val_neg_of_torsion {P : G1.curve.toAffine.Point}
    (htor : Fr.modulus • P = 0) (a : Fr) :
    (-a).val • P = -(a.val • P) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← nsmul_val_add_of_torsion htor (-a) a, fr_neg_add_cancel]
  exact zero_nsmul P

/-! ## Shape and butterfly step of `fftHalveG1` and `fftG1` -/

@[simp] theorem size_fftHalveG1 (xs : Array G1) (start : Nat) :
    (fftHalveG1 xs start).size = xs.size / 2 := by
  simp [fftHalveG1]

theorem getElem!_fftHalveG1 (xs : Array G1) (start i : Nat)
    (h : i < xs.size / 2) :
    (fftHalveG1 xs start)[i]! = xs[start + 2 * i]! := by
  rw [getElem!_pos (fftHalveG1 xs start) i (by rw [size_fftHalveG1]; exact h)]
  simp [fftHalveG1]

/-- `fftG1` preserves input array length. -/
@[simp] theorem size_fftG1 (vals : Array G1) (rootsOfUnity : Array Fr) :
    (fftG1 vals rootsOfUnity).size = vals.size := by
  rw [fftG1]
  split
  · rfl
  · simp

/-- Single-element unfolding of `fftG1` in the recursive case (`vals.size = 2 * m`). -/
theorem getElem!_fftG1_step {m : Nat} (vals : Array G1) (roots : Array Fr)
    (hm : 0 < m) (hsz : vals.size = 2 * m) (p : Nat) (hp : p < 2 * m) :
    (fftG1 vals roots)[p]! =
      (if p < m then
        G1.add (fftG1 (fftHalveG1 vals 0) (fftHalve roots 0))[p]!
          (G1.mul (fftG1 (fftHalveG1 vals 1) (fftHalve roots 0))[p]! roots[p]!)
      else
        G1.add (fftG1 (fftHalveG1 vals 0) (fftHalve roots 0))[p - m]!
          (G1.neg (G1.mul (fftG1 (fftHalveG1 vals 1) (fftHalve roots 0))[p - m]!
            roots[p - m]!))) := by
  set l := fftG1 (fftHalveG1 vals 0) (fftHalve roots 0) with hl
  set r := fftG1 (fftHalveG1 vals 1) (fftHalve roots 0) with hr
  rw [fftG1, ite_eq_right (by omega : ¬ vals.size ≤ 1)]
  rw [getElem!_pos _ p (by simp [hsz, hp])]
  simp only [Array.getElem_ofFn, ← hl, ← hr]
  have hlsize : l.size = m := by
    rw [hl, size_fftG1, size_fftHalveG1, hsz]
    omega
  -- Evaluate the spawned task entry at index q < l.size.
  have htask (q : Nat) (hq : q < l.size) :
      (Array.map Task.get
        (Array.ofFn (n := l.size) fun i =>
          Task.spawn fun _ => G1.mul r[i.val]! roots[i.val]!))[q]! =
        G1.mul r[q]! roots[q]! := by
    rw [getElem!_pos _ q (by simp [hq]), Array.getElem_map, Array.getElem_ofFn]
    rfl
  by_cases hph : p < m
  · have hpl : p < l.size := hlsize ▸ hph
    rw [ite_eq_left hpl, ite_eq_left hph, htask p hpl]
  · have hpl : ¬ p < l.size := hlsize ▸ hph
    have hsub : p - l.size < l.size := by omega
    rw [ite_eq_right hpl, ite_eq_right hph, htask (p - l.size) hsub, hlsize]

/-! ## Curve validity and DFT characterization of `fftG1` -/

/-- `fftG1` preserves curve validity on power-of-two arrays. -/
theorem valid_getElem!_fftG1 {k : Nat} (vals : Array G1) (roots : Array Fr)
    (hn : vals.size = 2 ^ k)
    (hvalid : ∀ i < 2 ^ k, G1.Valid vals[i]!)
    (j : Nat) (hj : j < 2 ^ k) :
    G1.Valid (fftG1 vals roots)[j]! := by
  induction k generalizing vals roots j with
  | zero =>
    simp only [pow_zero] at hn hj hvalid
    rw [fftG1, ite_eq_left (by omega : vals.size ≤ 1)]
    exact hvalid j hj
  | succ k ih =>
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hhalf : vals.size / 2 = 2 ^ k := by rw [hn, h2]; omega
    have hsz : 1 < vals.size := by rw [hn, h2]; omega
    have hsize0 : (fftHalveG1 vals 0).size = 2 ^ k := by rw [size_fftHalveG1, hhalf]
    have hsize1 : (fftHalveG1 vals 1).size = 2 ^ k := by rw [size_fftHalveG1, hhalf]
    have hv0 : ∀ i < 2 ^ k, G1.Valid (fftHalveG1 vals 0)[i]! := by
      intro i hi
      rw [getElem!_fftHalveG1 vals 0 i (hhalf ▸ hi), Nat.zero_add]
      exact hvalid (2 * i) (by rw [h2]; omega)
    have hv1 : ∀ i < 2 ^ k, G1.Valid (fftHalveG1 vals 1)[i]! := by
      intro i hi
      rw [getElem!_fftHalveG1 vals 1 i (hhalf ▸ hi)]
      exact hvalid (1 + 2 * i) (by rw [h2]; omega)
    rw [getElem!_fftG1_step vals roots (Nat.two_pow_pos k) (h2 ▸ hn) j (h2 ▸ hj)]
    by_cases hjk : j < 2 ^ k
    · rw [ite_eq_left hjk]
      exact G1.valid_add
        (ih (fftHalveG1 vals 0) (fftHalve roots 0) hsize0 hv0 j hjk)
        (G1.valid_mul (ih (fftHalveG1 vals 1) (fftHalve roots 0) hsize1 hv1 j hjk) _)
    · rw [ite_eq_right hjk]
      have hq : j - 2 ^ k < 2 ^ k := by omega
      exact G1.valid_add
        (ih (fftHalveG1 vals 0) (fftHalve roots 0) hsize0 hv0 (j - 2 ^ k) hq)
        (G1.valid_neg (G1.valid_mul
          (ih (fftHalveG1 vals 1) (fftHalve roots 0) hsize1 hv1 (j - 2 ^ k) hq) _))

/-- Sum splitting into even and odd indices in any additive commutative monoid. -/
private theorem sum_range_even_odd_add {M : Type*} [AddCommMonoid M]
    (m : Nat) (f : Nat → M) :
    (∑ i ∈ Finset.range (2 * m), f i) =
      (∑ i ∈ Finset.range m, f (2 * i)) + ∑ i ∈ Finset.range m, f (2 * i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    abel

/-- Entry `j` of `fftG1` evaluates the discrete Fourier transform in `G1`.

Let `vals` hold `2^k` valid `r`-torsion points and `roots[i] = omega^i` for a primitive `2^k`-th root `omega`.

Then entry `j` maps under `toPoint` to `sum_{i < 2^k} (omega^(i * j)).val * toPoint vals[i]`.
-/
theorem toPoint_getElem!_fftG1 {k : Nat} {ω : Fr}
    (hω : IsPrimitiveRoot ω (2 ^ k))
    (vals : Array G1) (roots : Array Fr)
    (hn : vals.size = 2 ^ k) (hrs : roots.size = 2 ^ k)
    (hroots : ∀ i, i < 2 ^ k → roots[i]! = ω ^ i)
    (hvalid : ∀ i < 2 ^ k, G1.Valid vals[i]!)
    (htor : ∀ i < 2 ^ k, Fr.modulus • G1.toPoint vals[i]! = 0)
    (j : Nat) (hj : j < 2 ^ k) :
    G1.toPoint (fftG1 vals roots)[j]! =
      ∑ i ∈ Finset.range (2 ^ k), (ω ^ (i * j)).val • G1.toPoint vals[i]! := by
  induction k generalizing ω vals roots j with
  | zero =>
    simp only [pow_zero] at hn hj hroots ⊢
    rw [fftG1, ite_eq_left (by omega : vals.size ≤ 1)]
    have hj0 : j = 0 := by omega
    subst hj0
    rw [Finset.sum_range_one, Nat.zero_mul, fr_pow_zero]
    change (1 : Nat) • G1.toPoint vals[0]! = G1.toPoint vals[0]!
    exact (one_nsmul _).symm
  | succ k ih =>
    have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hhalf : vals.size / 2 = 2 ^ k := by rw [hn, h2]; omega
    have hsz : 1 < vals.size := by rw [hn, h2]; omega
    have hω2 : IsPrimitiveRoot (ω ^ 2) (2 ^ k) :=
      hω.pow (Nat.two_pow_pos (k + 1)) h2
    have hpow1 : ω ^ (2 ^ (k + 1)) = 1 := hω.pow_eq_one
    have hneg : ω ^ (2 ^ k) = -1 := pow_half_eq_neg_one hpk (h2 ▸ hω)
    have hsize0 : (fftHalveG1 vals 0).size = 2 ^ k := by rw [size_fftHalveG1, hhalf]
    have hsize1 : (fftHalveG1 vals 1).size = 2 ^ k := by rw [size_fftHalveG1, hhalf]
    have hsizeR : (fftHalve roots 0).size = 2 ^ k := by
      rw [size_fftHalve, hrs, h2]; omega
    have hroots2 : ∀ i, i < 2 ^ k → (fftHalve roots 0)[i]! = (ω ^ 2) ^ i := by
      intro i hi
      rw [getElem!_fftHalve roots 0 i (by rw [hrs, h2]; omega), Nat.zero_add,
        hroots (2 * i) (by rw [h2]; omega), ← pow_mul]
    have hv0 : ∀ i < 2 ^ k, G1.Valid (fftHalveG1 vals 0)[i]! := by
      intro i hi
      rw [getElem!_fftHalveG1 vals 0 i (hhalf ▸ hi), Nat.zero_add]
      exact hvalid (2 * i) (by rw [h2]; omega)
    have hv1 : ∀ i < 2 ^ k, G1.Valid (fftHalveG1 vals 1)[i]! := by
      intro i hi
      rw [getElem!_fftHalveG1 vals 1 i (hhalf ▸ hi)]
      exact hvalid (1 + 2 * i) (by rw [h2]; omega)
    have ht0 : ∀ i < 2 ^ k, Fr.modulus • G1.toPoint (fftHalveG1 vals 0)[i]! = 0 := by
      intro i hi
      rw [getElem!_fftHalveG1 vals 0 i (hhalf ▸ hi), Nat.zero_add]
      exact htor (2 * i) (by rw [h2]; omega)
    have ht1 : ∀ i < 2 ^ k, Fr.modulus • G1.toPoint (fftHalveG1 vals 1)[i]! = 0 := by
      intro i hi
      rw [getElem!_fftHalveG1 vals 1 i (hhalf ▸ hi)]
      exact htor (1 + 2 * i) (by rw [h2]; omega)
    have hl : ∀ q < 2 ^ k,
        G1.toPoint (fftG1 (fftHalveG1 vals 0) (fftHalve roots 0))[q]! =
          ∑ i ∈ Finset.range (2 ^ k), (ω ^ (2 * i * q)).val • G1.toPoint vals[2 * i]! := by
      intro q hq
      rw [ih hω2 (fftHalveG1 vals 0) (fftHalve roots 0) hsize0 hsizeR hroots2 hv0 ht0 q hq]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [getElem!_fftHalveG1 vals 0 i (hhalf ▸ hi), Nat.zero_add, ← pow_mul, Nat.mul_assoc]
    have hr : ∀ q < 2 ^ k,
        G1.toPoint (fftG1 (fftHalveG1 vals 1) (fftHalve roots 0))[q]! =
          ∑ i ∈ Finset.range (2 ^ k), (ω ^ (2 * i * q)).val • G1.toPoint vals[2 * i + 1]! := by
      intro q hq
      rw [ih hω2 (fftHalveG1 vals 1) (fftHalve roots 0) hsize1 hsizeR hroots2 hv1 ht1 q hq]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [getElem!_fftHalveG1 vals 1 i (hhalf ▸ hi),
        show (1 : Nat) + 2 * i = 2 * i + 1 by omega, ← pow_mul, Nat.mul_assoc]
    -- Unfold one G1 butterfly step and split the target sum into even and odd indices.
    rw [getElem!_fftG1_step vals roots hpk (h2 ▸ hn) j (h2 ▸ hj),
      show (2 : Nat) ^ (k + 1) = 2 * 2 ^ k from h2,
      sum_range_even_odd_add (2 ^ k) (fun i => (ω ^ (i * j)).val • G1.toPoint vals[i]!)]
    by_cases hjk : j < 2 ^ k
    · -- Top half: l[j] + [omega^j] r[j].
      have hvl := valid_getElem!_fftG1 (fftHalveG1 vals 0) (fftHalve roots 0) hsize0 hv0 j hjk
      have hvr := valid_getElem!_fftG1 (fftHalveG1 vals 1) (fftHalve roots 0) hsize1 hv1 j hjk
      rw [ite_eq_left hjk, G1.toPoint_add hvl (G1.valid_mul hvr _),
        G1.toPoint_mul hvr, hl j hjk, hr j hjk, hroots j (by rw [h2]; omega), Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      have hti := htor (2 * i + 1) (by rw [h2]; omega)
      rw [← nsmul_val_mul_of_torsion hti (ω ^ j) (ω ^ (2 * i * j)),
        ← fr_pow_add, show j + 2 * i * j = (2 * i + 1) * j by ring]
    · -- Bottom half: l[q] - [omega^q] r[q] with q = j - 2^k and omega^(2^k) = -1.
      rw [ite_eq_right hjk]
      set q := j - 2 ^ k
      have hjq : j = q + 2 ^ k := by omega
      have hq2 : q < 2 ^ k := by omega
      have hvl := valid_getElem!_fftG1 (fftHalveG1 vals 0) (fftHalve roots 0) hsize0 hv0 q hq2
      have hvr := valid_getElem!_fftG1 (fftHalveG1 vals 1) (fftHalve roots 0) hsize1 hv1 q hq2
      rw [G1.toPoint_add hvl (G1.valid_neg (G1.valid_mul hvr _)),
        G1.toPoint_neg (G1.valid_mul hvr _), G1.toPoint_mul hvr,
        hl q hq2, hr q hq2, hroots q (by rw [h2]; omega), Finset.smul_sum, ← Finset.sum_neg_distrib]
      have hEven :
          (∑ i ∈ Finset.range (2 ^ k), (ω ^ (2 * i * q)).val • G1.toPoint vals[2 * i]!) =
            ∑ i ∈ Finset.range (2 ^ k), (ω ^ (2 * i * j)).val • G1.toPoint vals[2 * i]! := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show 2 * i * j = 2 * i * q + 2 ^ (k + 1) * i by rw [hjq, h2]; ring,
          fr_pow_add, fr_pow_mul ω (2 ^ (k + 1)) i, hpow1, fr_one_pow, fr_mul_one]
      have hOdd :
          (∑ i ∈ Finset.range (2 ^ k),
              -((ω ^ q).val • ((ω ^ (2 * i * q)).val • G1.toPoint vals[2 * i + 1]!))) =
            ∑ i ∈ Finset.range (2 ^ k),
              (ω ^ ((2 * i + 1) * j)).val • G1.toPoint vals[2 * i + 1]! := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        have hti := htor (2 * i + 1) (by rw [h2]; omega)
        rw [← nsmul_val_mul_of_torsion hti (ω ^ q) (ω ^ (2 * i * q)),
          ← nsmul_val_neg_of_torsion hti (ω ^ q * ω ^ (2 * i * q))]
        have hexp : -(ω ^ q * ω ^ (2 * i * q)) = ω ^ ((2 * i + 1) * j) := by
          rw [show (2 * i + 1) * j = (q + 2 * i * q) + 2 ^ (k + 1) * i + 2 ^ k by rw [hjq, h2]; ring,
            fr_pow_add, hneg, fr_pow_add, fr_pow_mul ω (2 ^ (k + 1)) i, hpow1,
            fr_one_pow, fr_mul_one, fr_pow_add, fr_mul_neg, fr_mul_one]
        rw [hexp]
      rw [hEven, hOdd]

end EthLib.Cryptography.Kzg

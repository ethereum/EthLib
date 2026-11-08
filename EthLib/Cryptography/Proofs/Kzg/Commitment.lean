module

public import EthLib.Cryptography.Proofs.Kzg.Evaluation
public import EthLib.Cryptography.Proofs.Kzg.Core
public import EthLib.Cryptography.Proofs.Kzg.TrustedSetup
public import EthLib.Cryptography.Proofs.Bls.Represents

/-!
# Proofs: a commitment is the blob's polynomial at the setup secret

A setup of the secret `τ` holds `[τ^i]_1`, `[τ^i]_2` and `[L_i(τ)]_1`, with `L_i` a Lagrange basis.

A blob's commitment sums its values times the Lagrange points, which gives `[p(τ)]_1`.

Two blobs whose values differ get one commitment only when `τ` is a root of `p - p'`.

Here `p` and `p'` are the interpolants of the two blobs, so `p - p'` is not zero.

A polynomial of degree 1 to 4095 can vanish at `τ`, so no theorem can exclude that root.

The theorems give no bound on the cost of finding two such blobs when `τ` is secret.

A polynomial of degree below 4096, committed with the monomial points, also gives `[p(τ)]_1`.

The setup built from the powers `[τ^i]_1` and `[τ^i]_2` is a well-formed setup of `τ`.

The scheme is PolyCommit_DL, §3.2 of Kate, Zaverucha and Goldberg, ASIACRYPT 2010:

<https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf>
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

/-- The setup of the secret `τ`.

The monomial points represent the powers of `τ`, in `G1` and in `G2`.

Lagrange point `i` represents basis polynomial `i` of the blob domain, at `τ`.

The domain is the 4096-th roots of unity in bit-reversed order.

The decoder bit-reverses the Lagrange points, so point `i` belongs to domain point `i`. -/
structure TrustedSetup.WellFormed (s : TrustedSetup) (τ : Fr) : Prop where
  /-- Lagrange point `i` represents `[L_i(τ)]_1`. -/
  lagrange_g1 : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB,
    G1.Represents s.g1LagrangeBrp[i] ((Lagrange.basis Finset.univ evalDomain i).eval τ)
  /-- Monomial point `i` of `G1` represents `[τ^i]_1`. -/
  monomial_g1 : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.Represents s.g1Monomial[i] (τ ^ i.val)
  /-- Monomial point `i` of `G2` represents `[τ^i]_2`. -/
  monomial_g2 : ∀ i : Fin KZG_SETUP_G2_LENGTH, G2.Represents s.g2Monomial[i] (τ ^ i.val)

/-- A well-formed setup is valid: every point is on its curve. -/
theorem TrustedSetup.WellFormed.valid {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ) :
    s.Valid :=
  ⟨fun i => (hs.lagrange_g1 i).1, fun i => (hs.monomial_g1 i).1, fun i => (hs.monomial_g2 i).1⟩

/-- In a well-formed setup, `r` times each monomial point of `G1` is zero. -/
theorem TrustedSetup.WellFormed.torsion {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {t : Nat} (ht : t < FIELD_ELEMENTS_PER_BLOB) :
    Fr.modulus • G1.toPoint s.g1Monomial.toArray[t]! = 0 := by
  rw [getElem!_pos s.g1Monomial.toArray t (by simpa using ht)]
  have h := (hs.monomial_g1 ⟨t, ht⟩).2
  simp only [Fin.getElem_fin] at h
  simp only [Vector.getElem_toArray]
  rw [h, G1.toPoint_mul_generator, G1.ofFr, ← mul_nsmul', mul_nsmul, G1.modulus_smul_generator,
    nsmul_zero]

/-- The polynomial of degree below 4096 that takes the given values on the blob domain. -/
noncomputable def interpolant (poly : Polynomial) : _root_.Polynomial Fr :=
  Lagrange.interpolate Finset.univ evalDomain fun i => poly[i.val]!

/-- The value of the interpolant at `τ` is the sum of the values times the basis at `τ`. -/
theorem eval_interpolant (poly : Polynomial) (τ : Fr) :
    (interpolant poly).eval τ =
      ∑ i : Fin FIELD_ELEMENTS_PER_BLOB,
        poly[i.val]! * (Lagrange.basis Finset.univ evalDomain i).eval τ := by
  rw [interpolant, Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C]

/-- On a decoded blob, the commitment compresses the sum of the values times the points. -/
theorem blobToKzgCommitment_eq_ok (s : TrustedSetup) {blob : Blob} {poly : Polynomial}
    (hblob : blobToPolynomial blob = .ok poly) :
    blobToKzgCommitment s blob = .ok (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)) := by
  have hsize : s.g1LagrangeBrp.toArray.size = poly.size := by
    rw [Vector.size_toArray, size_blobToPolynomial blob poly hblob]
  unfold blobToKzgCommitment
  rw [hblob]
  change (g1LincombPoints s.g1LagrangeBrp.toArray poly >>= fun c => pure (compressG1 c)) = _
  rw [g1LincombPoints_eq_msm hsize]
  rfl

/-- The sum of 4096 values times the Lagrange points represents the interpolant at `τ`. -/
theorem represents_lagrange_msm {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {poly : Polynomial} (hsize : poly.size = FIELD_ELEMENTS_PER_BLOB) :
    G1.Represents (G1.msm s.g1LagrangeBrp.toArray poly) ((interpolant poly).eval τ) := by
  let a : Nat → Fr := fun j =>
    if h : j < FIELD_ELEMENTS_PER_BLOB then (Lagrange.basis Finset.univ evalDomain ⟨j, h⟩).eval τ
    else 0
  have hpts : ∀ j < s.g1LagrangeBrp.toArray.size,
      G1.Represents s.g1LagrangeBrp.toArray[j]! (a j) := by
    intro j hj
    rw [Vector.size_toArray] at hj
    rw [getElem!_pos s.g1LagrangeBrp.toArray j (by simpa using hj)]
    simpa [a, hj] using hs.lagrange_g1 ⟨j, hj⟩
  have h := G1.represents_msm (by rw [Vector.size_toArray, hsize]) hpts
  rw [Vector.size_toArray] at h
  convert h using 1
  rw [eval_interpolant, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [a]

/-- On a decoded blob of a well-formed setup, the commitment holds `[p(τ)]_1`.

Here `p` is the polynomial of degree below 4096 that takes the blob's values on the domain. -/
theorem blobToKzgCommitment_represents {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {blob : Blob} {poly : Polynomial} (hblob : blobToPolynomial blob = .ok poly) :
    blobToKzgCommitment s blob = .ok (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)) ∧
      G1.Represents (G1.msm s.g1LagrangeBrp.toArray poly) ((interpolant poly).eval τ) :=
  ⟨blobToKzgCommitment_eq_ok s hblob,
    represents_lagrange_msm hs (size_blobToPolynomial blob poly hblob)⟩

/-! ## Commitments that collide at the setup secret -/

/-- Two valid points with the same 48-byte compressed form have the same group element. -/
private theorem toPoint_eq_of_compressG1_eq {P Q : G1} (hP : G1.Valid P) (hQ : G1.Valid Q)
    (heq : compressG1 P = compressG1 Q) :
    G1.toPoint P = G1.toPoint Q := by
  have hcomp : G1.compress P = G1.compress Q :=
    ByteArray.ext (congrArg Vector.toArray heq)
  obtain ⟨p, hp, hptP⟩ := G1.uncompress_compress hP
  obtain ⟨q, hq, hptQ⟩ := G1.uncompress_compress hQ
  rw [hcomp, hq] at hp
  cases hp
  exact hptP.symm.trans hptQ

/-- Two representatives with the same 48-byte compressed form represent the same scalar. -/
private theorem represents_eq_of_compressG1_eq {P Q : G1} {a b : Fr}
    (hP : G1.Represents P a) (hQ : G1.Represents Q b) (heq : compressG1 P = compressG1 Q) :
    a = b :=
  hP.unique ⟨hP.1, (toPoint_eq_of_compressG1_eq hP.1 hQ.1 heq).trans hQ.2⟩

/-- Two 4096-element arrays have the same interpolant exactly when they are equal. -/
private theorem interpolant_eq_iff {poly poly' : Polynomial}
    (hsize : poly.size = FIELD_ELEMENTS_PER_BLOB)
    (hsize' : poly'.size = FIELD_ELEMENTS_PER_BLOB) :
    interpolant poly = interpolant poly' ↔ poly = poly' := by
  constructor
  · intro h
    refine Array.ext (hsize.trans hsize'.symm) fun i hi hi' => ?_
    have hiF : i < FIELD_ELEMENTS_PER_BLOB := hsize ▸ hi
    have hev := congrArg (eval (evalDomain ⟨i, hiF⟩)) h
    rw [interpolant, interpolant,
      Lagrange.eval_interpolate_at_node _ evalDomain_injective.injOn (Finset.mem_univ _),
      Lagrange.eval_interpolate_at_node _ evalDomain_injective.injOn (Finset.mem_univ _),
      getElem!_pos poly i hi, getElem!_pos poly' i hi'] at hev
    exact hev
  · rintro rfl
    rfl

/-- On a well-formed setup of `τ`, two blobs with one commitment agree on their interpolants at `τ`.

The interpolant of each blob is the polynomial of degree below 4096 with its 4096 decoded values. -/
theorem eval_interpolant_eq_of_blobToKzgCommitment_eq {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {blob blob' : Blob} {poly poly' : Polynomial} {c : KZGCommitment}
    (hblob : blobToPolynomial blob = .ok poly) (hblob' : blobToPolynomial blob' = .ok poly')
    (hc : blobToKzgCommitment s blob = .ok c) (hc' : blobToKzgCommitment s blob' = .ok c) :
    (interpolant poly).eval τ = (interpolant poly').eval τ := by
  obtain ⟨hC, hr⟩ := blobToKzgCommitment_represents hs hblob
  obtain ⟨hC', hr'⟩ := blobToKzgCommitment_represents hs hblob'
  have heq : compressG1 (G1.msm s.g1LagrangeBrp.toArray poly) =
      compressG1 (G1.msm s.g1LagrangeBrp.toArray poly') :=
    Except.ok.inj (hC.symm.trans (hc.trans (hc'.symm.trans hC')))
  exact represents_eq_of_compressG1_eq hr hr' heq

/-- Two blobs whose values differ and whose commitments agree make `τ` a root of `p - p'`.

Here `s` is a well-formed setup of `τ`, `p` and `p'` are the two interpolants, and `p - p' ≠ 0`. -/
theorem blobToKzgCommitment_binding {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {blob blob' : Blob} {poly poly' : Polynomial} {c : KZGCommitment}
    (hblob : blobToPolynomial blob = .ok poly) (hblob' : blobToPolynomial blob' = .ok poly')
    (hne : poly ≠ poly')
    (hc : blobToKzgCommitment s blob = .ok c) (hc' : blobToKzgCommitment s blob' = .ok c) :
    interpolant poly - interpolant poly' ≠ 0 ∧
      (interpolant poly - interpolant poly').eval τ = 0 := by
  have hint : interpolant poly ≠ interpolant poly' :=
    mt (interpolant_eq_iff (size_blobToPolynomial blob poly hblob)
      (size_blobToPolynomial blob' poly' hblob')).mp hne
  have hsub (f g : _root_.Polynomial Fr) : (f - g).eval τ = f.eval τ - g.eval τ :=
    eval_sub f g τ
  have hne0 (f g : _root_.Polynomial Fr) (h : f ≠ g) : f - g ≠ 0 :=
    sub_ne_zero.mpr h
  refine ⟨hne0 _ _ hint, ?_⟩
  rw [hsub, sub_eq_zero]
  exact eval_interpolant_eq_of_blobToKzgCommitment_eq hs hblob hblob' hc hc'

/-! ## Commitments from monomial points and the setup of a secret -/

/-- The commitment to a polynomial: its first 4096 coefficients times the monomial points. -/
def commitPoly (s : TrustedSetup) (p : _root_.Polynomial Fr) : G1 :=
  G1.msm s.g1Monomial.toArray (Array.ofFn fun k : Fin FIELD_ELEMENTS_PER_BLOB => p.coeff k)

/-- The commitment to a polynomial of degree below 4096 represents its value at the secret.

Only the monomial points of `G1` must represent the powers of the secret. -/
theorem represents_commitPoly_of_monomial {s : TrustedSetup} {τ : Fr}
    (hm : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.Represents s.g1Monomial[i] (τ ^ i.val))
    {p : _root_.Polynomial Fr} (hp : p.natDegree < FIELD_ELEMENTS_PER_BLOB) :
    G1.Represents (commitPoly s p) (p.eval τ) := by
  have h := G1.represents_msm (points := s.g1Monomial.toArray)
    (scalars := Array.ofFn fun k : Fin FIELD_ELEMENTS_PER_BLOB => p.coeff k)
    (a := fun j => τ ^ j) (by simp) fun j hj => by
      have hj' : j < FIELD_ELEMENTS_PER_BLOB := by simpa using hj
      rw [getElem!_pos _ j hj, Vector.getElem_toArray]
      exact hm ⟨j, hj'⟩
  rw [commitPoly]
  convert h using 1
  rw [eval_eq_sum_range' hp, Vector.size_toArray]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

/-- The commitment to a polynomial of degree below 4096 represents its value at the secret. -/
theorem represents_commitPoly {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {p : _root_.Polynomial Fr} (hp : p.natDegree < FIELD_ELEMENTS_PER_BLOB) :
    G1.Represents (commitPoly s p) (p.eval τ) :=
  represents_commitPoly_of_monomial hs.monomial_g1 hp

/-- Points that stand for the powers of a secret: 4096 in `G1` and 65 in `G2`.

In security games they are `[τ^i]_1` for `i ≤ 4095` and `[τ^i]_2` for `i ≤ 64`. -/
abbrev SetupPowers : Type := Vector G1 FIELD_ELEMENTS_PER_BLOB × Vector G2 KZG_SETUP_G2_LENGTH

/-- The powers of the secret `τ` in `G1` and in `G2`. -/
def setupPowers (τ : Fr) : SetupPowers :=
  (Vector.ofFn fun i => G1.mul G1.generator (τ ^ i.val),
    Vector.ofFn fun i => G2.mul G2.generator (τ ^ i.val))

/-- The full setup built from the powers.

Lagrange point `i` is the commitment to basis polynomial `i` of the blob domain.

So anyone who holds the powers can compute it. -/
noncomputable def TrustedSetup.ofPowers (pw : SetupPowers) : TrustedSetup where
  g1LagrangeBrp := Vector.ofFn fun i =>
    G1.msm pw.1.toArray (Array.ofFn fun k : Fin FIELD_ELEMENTS_PER_BLOB =>
      (Lagrange.basis Finset.univ evalDomain i).coeff k)
  g1Monomial := pw.1
  g2Monomial := pw.2

/-- Monomial point `i` of `G1` from the secret `τ`. -/
theorem setupPowers_g1 (τ : Fr) (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    (setupPowers τ).1[i] = G1.mul G1.generator (τ ^ i.val) :=
  Vector.getElem_ofFn _

/-- Monomial point `i` of `G2` from the secret `τ`. -/
theorem setupPowers_g2 (τ : Fr) (i : Fin KZG_SETUP_G2_LENGTH) :
    (setupPowers τ).2[i] = G2.mul G2.generator (τ ^ i.val) :=
  Vector.getElem_ofFn _

/-- Lagrange point `i` of the setup built from the powers. -/
theorem ofPowers_g1LagrangeBrp (pw : SetupPowers) (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    (TrustedSetup.ofPowers pw).g1LagrangeBrp[i] =
      commitPoly (TrustedSetup.ofPowers pw) (Lagrange.basis Finset.univ evalDomain i) :=
  by simp only [TrustedSetup.ofPowers, commitPoly, Fin.getElem_fin, Vector.getElem_ofFn]

/-- The setup built from the powers of `τ` is a well-formed setup of `τ`. -/
theorem wellFormed_ofPowers (τ : Fr) : (TrustedSetup.ofPowers (setupPowers τ)).WellFormed τ := by
  have hm : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB,
      G1.Represents (TrustedSetup.ofPowers (setupPowers τ)).g1Monomial[i] (τ ^ i.val) :=
    fun i => (setupPowers_g1 τ i).symm ▸ G1.represents_mul_generator _
  refine ⟨fun i => ?_, hm, fun i => (setupPowers_g2 τ i).symm ▸ G2.represents_mul_generator _⟩
  have hdeg : (Lagrange.basis Finset.univ evalDomain i).natDegree < FIELD_ELEMENTS_PER_BLOB := by
    rw [Lagrange.natDegree_basis evalDomain_injective.injOn (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    decide
  rw [ofPowers_g1LagrangeBrp]
  exact represents_commitPoly_of_monomial hm hdeg

end EthLib.Cryptography.Kzg

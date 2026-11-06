module

public import EthLib.Cryptography.Bls.Pairing
public import EthLib.Cryptography.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.FrZMod
public import EthLib.Cryptography.Proofs.Bls.G1Group
public import EthLib.Cryptography.Proofs.Bls.G1Order
public import EthLib.Cryptography.Proofs.Bls.PairingLaws
public import EthLib.Cryptography.Proofs.Bls.KeyValidate

/-!
# Sufficiency of the ceremony pairing checks

The KZG ceremony sequencer runs three pairing checks on each contribution.

The source is the sequencer document of `kzg-ceremony-specs`, section "Pairing checks":
<https://github.com/ethereum/kzg-ceremony-specs/blob/master/docs/sequencer/sequencer.md#pairing-checks>

Under the pairing law, the checks force each point to represent a power of the new trapdoor.

A point represents a scalar when its group element is that multiple of the generator.

The theorems cover the exact checks, not their batched form.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.CeremonyChecks

open EthLib.Cryptography.Bls (Fr G1 G2)
open scoped EthLib.Cryptography.Bls.Fr

/-- Point-level ceremony validation for `G1`: non-infinity and in the prime-order subgroup. -/
def g1Validate (p : G1) : Bool :=
  !p.isInfinity && p.inSubgroup

/-- Point-level ceremony validation for `G2`: non-infinity and in the prime-order subgroup. -/
def g2Validate (p : G2) : Bool :=
  !p.isInfinity && p.inSubgroup

/-- `g1Validate` rejects the `G1` identity (`G1.zero`). -/
@[simp] theorem g1Validate_zero_eq_false : g1Validate G1.zero = false := by
  rw [g1Validate, G1.isInfinity_zero]
  rfl

/-- `g2Validate` rejects the `G2` identity (`G2.zero`). -/
@[simp] theorem g2Validate_zero_eq_false : g2Validate G2.zero = false := by
  rw [g2Validate, G2.isInfinity_zero]
  rfl

/-- Any point accepted by `g1Validate` is non-infinity. -/
theorem g1Validate_isInfinity_eq_false {p : G1} (h : g1Validate p = true) :
    p.isInfinity = false := by
  unfold g1Validate at h
  cases hp : p.isInfinity <;> simp_all

/-- Any point accepted by `g2Validate` is non-infinity. -/
theorem g2Validate_isInfinity_eq_false {p : G2} (h : g2Validate p = true) :
    p.isInfinity = false := by
  unfold g2Validate at h
  cases hp : p.isInfinity <;> simp_all

/-- Adding from `G1.zero` on the left returns the right operand. -/
@[simp] theorem G1.zero_add (q : G1) : G1.add G1.zero q = q := by
  unfold Bls.G1.add
  have hz : BaseField.isZero (G1.zero : G1).z = true := G1.isInfinity_zero
  simp [hz]

/-- Adding `G1.zero` on the right of a non-infinity point returns the point unchanged. -/
@[simp] theorem G1.add_zero {p : G1} (hp : p.isInfinity = false) :
    G1.add p G1.zero = p := by
  unfold Bls.G1.add
  have hpz : BaseField.isZero p.z = false := hp
  have hz : BaseField.isZero (G1.zero : G1).z = true := G1.isInfinity_zero
  simp [hpz, hz]

/-- Scalar multiplication of any `G1` point by `0` gives `G1.zero`. -/
@[simp] theorem G1.mul_zero (p : G1) : G1.mul p (0 : Fr) = G1.zero := by
  rw [G1.mul, Fr.val_zero, G1.mulNat_def]
  rfl

/-- Scalar multiplication of a non-infinity `G1` point by `1` returns the point unchanged. -/
@[simp] theorem G1.mul_one {p : G1} (hp : p.isInfinity = false) :
    G1.mul p (1 : Fr) = p := by
  rw [G1.mul, Fr.val_one, G1.mulNat_def]
  norm_num
  rw [G1.mulNat_def]
  norm_num
  exact G1.add_zero hp

/-- Adding from `G2.zero` on the left returns the right operand. -/
@[simp] theorem G2.zero_add (q : G2) : G2.add G2.zero q = q := by
  unfold Bls.G2.add
  have hz : (G2.zero : G2).z.isZero = true := G2.isInfinity_zero
  simp [hz]

/-- Adding `G2.zero` on the right of a non-infinity point returns the point unchanged. -/
@[simp] theorem G2.add_zero {p : G2} (hp : p.isInfinity = false) :
    G2.add p G2.zero = p := by
  unfold Bls.G2.add
  have hpz : p.z.isZero = false := hp
  have hz : (G2.zero : G2).z.isZero = true := G2.isInfinity_zero
  simp [hpz, hz]

/-- Unfolding equation for the executable G2 double-and-add multiplication. -/
private theorem g2MulNat_def (p : G2) (k : Nat) :
    G2.mulNat p k = if k = 0 then G2.zero
      else if k % 2 = 1 then G2.add p (G2.mulNat (G2.double p) (k / 2))
      else G2.mulNat (G2.double p) (k / 2) := by
  rw [G2.mulNat]

/-- Scalar multiplication of any `G2` point by `0` gives `G2.zero`. -/
@[simp] theorem G2.mul_zero (p : G2) : G2.mul p (0 : Fr) = G2.zero := by
  rw [G2.mul, Fr.val_zero, g2MulNat_def]
  rfl

/-- Scalar multiplication of a non-infinity `G2` point by `1` returns the point unchanged. -/
@[simp] theorem G2.mul_one {p : G2} (hp : p.isInfinity = false) :
    G2.mul p (1 : Fr) = p := by
  rw [G2.mul, Fr.val_one, g2MulNat_def]
  norm_num
  rw [g2MulNat_def]
  norm_num
  exact G2.add_zero hp

/-- For any valid `G1` point `p`, `p.isInfinity = true` iff `G1.toPoint p = 0`. -/
theorem isInfinity_eq_true_iff_toPoint_eq_zero {p : G1} (hp : G1.Valid p) :
    p.isInfinity = true ↔ G1.toPoint p = 0 := by
  constructor
  · intro h
    exact WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero (G1.isZero_iff.mp h)
  · intro h
    by_contra hne
    have hz : (p.z : ZMod Bls.Fp.modulus) ≠ 0 :=
      fun hz0 => hne (G1.isZero_iff.mpr hz0)
    rw [G1.toPoint, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hp hz] at h
    cases h

/-- A `G1` generator multiple is non-infinity exactly when its scalar is nonzero.
Discharges the `G1` non-infinity law unconditionally using the kernel-verified
generator order (`G1.addOrderOf_toPoint_generator`). -/
theorem g1Mul_nonzero_iff (s : Fr) :
    G1.isInfinity (G1.mul (G1.generator : G1) s) = false ↔ s ≠ 0 := by
  rw [Bool.eq_false_iff, Ne, isInfinity_eq_true_iff_toPoint_eq_zero
      (G1.valid_mul G1.valid_generator s), G1.toPoint_mul_generator, G1.ofFr]
  refine not_congr ?_
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero, G1.addOrderOf_toPoint_generator]
  constructor
  · intro hdvd
    exact Fr.ext (by rw [Fr.val_zero]; exact Nat.eq_zero_of_dvd_of_lt hdvd (Fr.val_lt s))
  · rintro rfl
    rw [Fr.val_zero]
    exact Nat.dvd_zero _

/-- Non-infinity of a `G1` scalar multiple implies the scalar is nonzero. -/
theorem g1Mul_ne_zero_of_isInfinity_eq_false {p : G1} {s : Fr}
    (h : G1.isInfinity (G1.mul p s) = false) : s ≠ 0 := by
  rintro rfl
  rw [G1.mul_zero, G1.isInfinity_zero] at h
  cases h

/-- Non-infinity of a `G2` scalar multiple implies the scalar is nonzero. -/
theorem g2Mul_ne_zero_of_isInfinity_eq_false {p : G2} {x : Fr}
    (h : G2.isInfinity (G2.mul p x) = false) : x ≠ 0 := by
  rintro rfl
  rw [G2.mul_zero, G2.isInfinity_zero] at h
  cases h

/-- Equality of two pairings, expressed using the repository's product-pairing checker.

`pairingEq p₁ q₁ p₂ q₂` represents `e(p₁, q₁) = e(p₂, q₂)` as
`e(p₁, q₁) * e(-p₂, q₂) = 1`. -/
def pairingEq (p₁ : G1) (q₁ : G2) (p₂ : G1) (q₂ : G2) : Prop :=
  EthLib.Cryptography.Bls.pairingCheck #[(p₁, q₁), (G1.neg p₂, q₂)] = true

/-- A single submitted ceremony contribution, using the repository's concrete point
representations. -/
structure Contribution where
  g1Powers : Array G1
  g2Powers : Array G2
  potPubkey : G2

/-- The part of the previous transcript used by the tau-update check. -/
structure Transcript where
  previousTau : G1

/-- The three sequencer pairing checks over concrete G1/G2 points.

The size hypotheses make every checked index explicit and avoid the silent-truncation
behavior of pseudocode `zip`. -/
structure Checks (contribution : Contribution) (transcript : Transcript) : Prop where
  one_lt_g1 : 1 < contribution.g1Powers.size
  one_lt_g2 : 1 < contribution.g2Powers.size
  g2_le_g1 : contribution.g2Powers.size ≤ contribution.g1Powers.size

  /-- Tau update:
  `e(previousTau, potPubkey) = e(g1Powers[1], G2.generator)`. -/
  tauUpdate :
    pairingEq transcript.previousTau contribution.potPubkey
      (contribution.g1Powers[1]'one_lt_g1) G2.generator

  /-- G1 recurrence:
  `e(g1Powers[i+1], G2.generator) = e(g1Powers[i], g2Powers[1])`. -/
  g1Powers : ∀ i (hi : i + 1 < contribution.g1Powers.size),
    pairingEq
      (contribution.g1Powers[i + 1]'hi) G2.generator
      (contribution.g1Powers[i]'(Nat.lt_trans (Nat.lt_succ_self i) hi))
      (contribution.g2Powers[1]'one_lt_g2)

  /-- G1/G2 consistency:
  `e(G1.generator, g2Powers[i]) = e(g1Powers[i], G2.generator)`. -/
  g2Powers : ∀ i (hi : i < contribution.g2Powers.size),
    pairingEq G1.generator
      (contribution.g2Powers[i]'hi)
      (contribution.g1Powers[i]'(Nat.lt_of_lt_of_le hi g2_le_g1))
      G2.generator

/-- Exponents of the checked points: each point represents its exponent times the generator.

A point represents `a • g` when it is valid and its group element is `a` times the generator.

So the witness speaks of group elements, not of the coordinates of one representative.

The subgroup checks of the sequencer give such exponents. -/
structure SubgroupExponents
    (contribution : Contribution) (transcript : Transcript) where
  s : Fr
  x : Fr
  a : Nat → Fr
  b : Nat → Fr
  previousTau_rep : G1.Represents transcript.previousTau s
  potPubkey_rep : G2.Represents contribution.potPubkey x
  g1_rep : ∀ i (hi : i < contribution.g1Powers.size),
    G1.Represents (contribution.g1Powers[i]'hi) (a i)
  g2_rep : ∀ i (hi : i < contribution.g2Powers.size),
    G2.Represents (contribution.g2Powers[i]'hi) (b i)

/-- The scalar identity of a pairing equality. -/
private theorem add_neg_mul_eq_zero_iff (a b c d : Fr) :
    a * b + -c * d = 0 ↔ a * b = c * d := by
  constructor <;> intro h <;> linear_combination h

/-- Under the pairing law, a pairing equality of representatives is an equality of scalars.

`e(a • g1, b • g2) = e(c • g1, d • g2)` holds exactly when `a * b = c * d`. -/
theorem pairingEq_iff (laws : Bls.PairingLaws) {p₁ p₂ : G1} {q₁ q₂ : G2} {a b c d : Fr}
    (hp₁ : G1.Represents p₁ a) (hq₁ : G2.Represents q₁ b)
    (hp₂ : G1.Represents p₂ c) (hq₂ : G2.Represents q₂ d) :
    pairingEq p₁ q₁ p₂ q₂ ↔ a * b = c * d := by
  unfold pairingEq
  rw [laws.two_pairs hp₁ hq₁ hp₂.neg hq₂]
  exact add_neg_mul_eq_zero_iff a b c d

/-- A representative of `0 • g1` is the point at infinity. -/
theorem g1_ne_zero_of_isInfinity_eq_false {p : G1} {a : Fr} (h : G1.Represents p a)
    (hp : G1.isInfinity p = false) : a ≠ 0 := by
  rintro rfl
  have h0 : G1.toPoint p = 0 := by rw [h.2, G1.toPoint_mul_generator, G1.ofFr_zero]
  rw [(isInfinity_eq_true_iff_toPoint_eq_zero h.1).mpr h0] at hp
  cases hp

/-- A representative of `0 • g2` is the point at infinity. -/
theorem g2_ne_zero_of_isInfinity_eq_false {q : G2} {b : Fr} (h : G2.Represents q b)
    (hq : G2.isInfinity q = false) : b ≠ 0 := by
  rintro rfl
  have h0 : G2.toPoint q = 0 := by rw [h.2, G2.toPoint_mul_generator, G2.ofFr_zero]
  rw [(G2.isInfinity_eq_true_iff_toPoint_eq_zero h.1).mpr h0] at hq
  cases hq

/-- **Scalar consequence of the three pairing checks.**

Under the pairing law, the exponent of point `i` is `(s * x)^i`, in both groups. -/
theorem exponentChecksSufficient
    (laws : Bls.PairingLaws)
    (contribution : Contribution) (transcript : Transcript)
    (checks : Checks contribution transcript)
    (exponents : SubgroupExponents contribution transcript)
    (previousTauNonzero : G1.isInfinity transcript.previousTau = false)
    (pubkeyNonzero : G2.isInfinity contribution.potPubkey = false) :
    (∀ i, i < contribution.g1Powers.size →
      exponents.a i = Fr.powNat (exponents.s * exponents.x) i) ∧
    (∀ i, i < contribution.g2Powers.size →
      exponents.b i = Fr.powNat (exponents.s * exponents.x) i) := by
  have s_ne_zero : exponents.s ≠ 0 :=
    g1_ne_zero_of_isInfinity_eq_false exponents.previousTau_rep previousTauNonzero

  have x_ne_zero : exponents.x ≠ 0 :=
    g2_ne_zero_of_isInfinity_eq_false exponents.potPubkey_rep pubkeyNonzero

  -- The tau update: `e([s], [x]) = e([a_1], [1])`.
  have updateScalar : exponents.s * exponents.x = exponents.a 1 := by
    have hmul := (pairingEq_iff laws exponents.previousTau_rep exponents.potPubkey_rep
      (exponents.g1_rep 1 checks.one_lt_g1) G2.represents_generator).mp checks.tauUpdate
    exact hmul.trans (mul_one (exponents.a 1))

  -- The G1 recurrence: `e([a_(i+1)], [1]) = e([a_i], [b_1])`.
  have g1Recurrence : ∀ i (hi : i + 1 < contribution.g1Powers.size),
      exponents.a (i + 1) = exponents.a i * exponents.b 1 := by
    intro i hi
    have hmul := (pairingEq_iff laws (exponents.g1_rep (i + 1) hi) G2.represents_generator
      (exponents.g1_rep i (Nat.lt_trans (Nat.lt_succ_self i) hi))
      (exponents.g2_rep 1 checks.one_lt_g2)).mp (checks.g1Powers i hi)
    exact
      calc
        exponents.a (i + 1) = exponents.a (i + 1) * (1 : Fr) :=
          (mul_one (exponents.a (i + 1))).symm
        _ = exponents.a i * exponents.b 1 := hmul

  -- The cross-group check: `e([1], [b_i]) = e([a_i], [1])`.
  have crossGroup : ∀ i (hi : i < contribution.g2Powers.size),
      exponents.b i = exponents.a i := by
    intro i hi
    have hmul := (pairingEq_iff laws G1.represents_generator (exponents.g2_rep i hi)
      (exponents.g1_rep i (Nat.lt_of_lt_of_le hi checks.g2_le_g1))
      G2.represents_generator).mp (checks.g2Powers i hi)
    exact
      calc
        exponents.b i = (1 : Fr) * exponents.b i :=
          (one_mul (exponents.b i)).symm
        _ = exponents.a i * (1 : Fr) := hmul
        _ = exponents.a i := mul_one (exponents.a i)

  let tau : Fr := exponents.s * exponents.x

  have a_one : exponents.a 1 = tau := updateScalar.symm

  have tau_ne_zero : tau ≠ 0 := by
    dsimp [tau]
    intro hzero
    have hmulInv := congrArg (fun z : Fr => z * exponents.x⁻¹) hzero
    have hxInv : exponents.x * exponents.x⁻¹ = 1 :=
      mul_inv_cancel₀ x_ne_zero
    apply s_ne_zero
    calc
      exponents.s = exponents.s * 1 := (mul_one exponents.s).symm
      _ = exponents.s * (exponents.x * exponents.x⁻¹) :=
        congrArg (fun z : Fr => exponents.s * z) hxInv.symm
      _ = (exponents.s * exponents.x) * exponents.x⁻¹ :=
        (mul_assoc _ _ _).symm
      _ = 0 * exponents.x⁻¹ := hmulInv
      _ = 0 := zero_mul _

  have b_one : exponents.b 1 = exponents.a 1 :=
    crossGroup 1 checks.one_lt_g2

  have a_one_ne_zero : exponents.a 1 ≠ 0 := by
    rw [a_one]
    exact tau_ne_zero

  -- `a_1 = a_0 * b_1 = a_0 * a_1`, and `a_1 ≠ 0`, so `a_0 = 1`.
  have a_zero : exponents.a 0 = 1 := by
    have recurrence_zero : exponents.a 1 = exponents.a 0 * exponents.b 1 :=
      g1Recurrence 0 checks.one_lt_g1
    have hcancel : (1 : Fr) * exponents.a 1 =
        exponents.a 0 * exponents.a 1 := by
      calc
        (1 : Fr) * exponents.a 1 = exponents.a 1 := one_mul _
        _ = exponents.a 0 * exponents.b 1 := recurrence_zero
        _ = exponents.a 0 * exponents.a 1 := by rw [b_one]
    have hcancelInv :=
      congrArg (fun z : Fr => z * (exponents.a 1)⁻¹) hcancel
    have haInv : exponents.a 1 * (exponents.a 1)⁻¹ = 1 :=
      mul_inv_cancel₀ a_one_ne_zero
    have one_eq_a_zero : (1 : Fr) = exponents.a 0 := by
      calc
        (1 : Fr) = exponents.a 1 * (exponents.a 1)⁻¹ := haInv.symm
        _ = ((1 : Fr) * exponents.a 1) * (exponents.a 1)⁻¹ := by
          rw [one_mul]
        _ = (exponents.a 0 * exponents.a 1) * (exponents.a 1)⁻¹ := hcancelInv
        _ = exponents.a 0 * (exponents.a 1 * (exponents.a 1)⁻¹) :=
          mul_assoc _ _ _
        _ = exponents.a 0 * 1 :=
          congrArg (fun z : Fr => exponents.a 0 * z) haInv
        _ = exponents.a 0 := mul_one _
    exact one_eq_a_zero.symm

  have g1_is_powers : ∀ i, i < contribution.g1Powers.size →
      exponents.a i = Fr.powNat tau i := by
    intro i
    induction i with
    | zero =>
        intro _
        calc
          exponents.a 0 = 1 := a_zero
          _ = Fr.powNat tau 0 := (Fr.powNat_zero tau).symm
    | succ i ih =>
        intro i_succ_lt
        have i_lt : i < contribution.g1Powers.size :=
          Nat.lt_trans (Nat.lt_succ_self i) i_succ_lt
        calc
          exponents.a (i + 1) = exponents.a i * exponents.b 1 :=
            g1Recurrence i i_succ_lt
          _ = exponents.a i * exponents.a 1 := by rw [b_one]
          _ = Fr.powNat tau i * tau := by rw [ih i_lt, a_one]
          _ = tau * Fr.powNat tau i := EthLib.Cryptography.Bls.Fr.mul_comm _ _
          _ = Fr.powNat tau (i + 1) := (Fr.powNat_succ tau i).symm

  have g2_is_powers : ∀ i, i < contribution.g2Powers.size →
      exponents.b i = Fr.powNat tau i := by
    intro i hi
    calc
      exponents.b i = exponents.a i := crossGroup i hi
      _ = Fr.powNat tau i :=
        g1_is_powers i (Nat.lt_of_lt_of_le hi checks.g2_le_g1)

  exact ⟨g1_is_powers, g2_is_powers⟩

/-- **Sufficiency of the three pairing checks.**

Assume the pairing law, and that the previous tau point and the public key are not at infinity.

If the three checks hold, point `i` represents `(s * x)^i` times the generator, in both groups.

The assumptions on infinity are the previous transcript's validity and a check of the public key. -/
theorem checksSufficient
    (laws : Bls.PairingLaws)
    (contribution : Contribution) (transcript : Transcript)
    (checks : Checks contribution transcript)
    (exponents : SubgroupExponents contribution transcript)
    (previousTauNonzero : G1.isInfinity transcript.previousTau = false)
    (pubkeyNonzero : G2.isInfinity contribution.potPubkey = false) :
    (∀ i (hi : i < contribution.g1Powers.size),
      G1.Represents (contribution.g1Powers[i]'hi)
        (Fr.powNat (exponents.s * exponents.x) i)) ∧
    (∀ i (hi : i < contribution.g2Powers.size),
      G2.Represents (contribution.g2Powers[i]'hi)
        (Fr.powNat (exponents.s * exponents.x) i)) := by
  have scalarPowers := exponentChecksSufficient laws contribution transcript checks
    exponents previousTauNonzero pubkeyNonzero
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [← scalarPowers.1 i hi]
    exact exponents.g1_rep i hi
  · rw [← scalarPowers.2 i hi]
    exact exponents.g2_rep i hi

/-- The checks force the zeroth exponent in `G1` to be one. -/
theorem g1ZeroExponentEqOne
    (laws : Bls.PairingLaws)
    (contribution : Contribution) (transcript : Transcript)
    (checks : Checks contribution transcript)
    (exponents : SubgroupExponents contribution transcript)
    (previousTauNonzero : G1.isInfinity transcript.previousTau = false)
    (pubkeyNonzero : G2.isInfinity contribution.potPubkey = false) :
    exponents.a 0 = 1 := by
  have zero_lt_g1 : 0 < contribution.g1Powers.size :=
    Nat.lt_trans (Nat.zero_lt_succ 0) checks.one_lt_g1
  have h := (exponentChecksSufficient laws contribution transcript checks exponents
    previousTauNonzero pubkeyNonzero).1 0 zero_lt_g1
  simpa [Fr.powNat_zero] using h

/-- The zeroth point in `G1` represents the generator itself. -/
theorem g1ZeroPointRepresentsOne
    (laws : Bls.PairingLaws)
    (contribution : Contribution) (transcript : Transcript)
    (checks : Checks contribution transcript)
    (exponents : SubgroupExponents contribution transcript)
    (previousTauNonzero : G1.isInfinity transcript.previousTau = false)
    (pubkeyNonzero : G2.isInfinity contribution.potPubkey = false) :
    G1.Represents
      (contribution.g1Powers[0]'(Nat.lt_trans (Nat.zero_lt_succ 0) checks.one_lt_g1)) 1 := by
  have h := (checksSufficient laws contribution transcript checks exponents
    previousTauNonzero pubkeyNonzero).1 0
      (Nat.lt_trans (Nat.zero_lt_succ 0) checks.one_lt_g1)
  simpa [Fr.powNat_zero] using h

/-- The subgroup checks give the exponents.

Let every point be valid and pass the subgroup check of its group.

Then each point represents some multiple of its generator. -/
theorem nonempty_subgroupExponents
    (contribution : Contribution) (transcript : Transcript)
    (hτ : G1.Valid transcript.previousTau ∧ transcript.previousTau.inSubgroup = true)
    (hpk : G2.Valid contribution.potPubkey ∧ contribution.potPubkey.inSubgroup = true)
    (hg1 : ∀ i (hi : i < contribution.g1Powers.size),
      G1.Valid (contribution.g1Powers[i]'hi) ∧ (contribution.g1Powers[i]'hi).inSubgroup = true)
    (hg2 : ∀ i (hi : i < contribution.g2Powers.size),
      G2.Valid (contribution.g2Powers[i]'hi) ∧ (contribution.g2Powers[i]'hi).inSubgroup = true) :
    Nonempty (SubgroupExponents contribution transcript) := by
  classical
  -- Each check gives one exponent.
  have e1 : ∀ i (hi : i < contribution.g1Powers.size),
      ∃ a, G1.Represents (contribution.g1Powers[i]'hi) a :=
    fun i hi => (G1.inSubgroup_iff_exists_represents (hg1 i hi).1).mp (hg1 i hi).2
  have e2 : ∀ i (hi : i < contribution.g2Powers.size),
      ∃ b, G2.Represents (contribution.g2Powers[i]'hi) b :=
    fun i hi => (G2.inSubgroup_iff_exists_represents (hg2 i hi).1).mp (hg2 i hi).2
  obtain ⟨s, hs⟩ := (G1.inSubgroup_iff_exists_represents hτ.1).mp hτ.2
  obtain ⟨x, hx⟩ := (G2.inSubgroup_iff_exists_represents hpk.1).mp hpk.2
  refine ⟨{
    s := s
    x := x
    a := fun i => if hi : i < contribution.g1Powers.size then (e1 i hi).choose else 0
    b := fun i => if hi : i < contribution.g2Powers.size then (e2 i hi).choose else 0
    previousTau_rep := hs
    potPubkey_rep := hx
    g1_rep := fun i hi => by simpa [hi] using (e1 i hi).choose_spec
    g2_rep := fun i hi => by simpa [hi] using (e2 i hi).choose_spec }⟩

/-- **Sufficiency of the checks of the sequencer, with the subgroup checks.**

Assume the pairing law and the three pairing checks.

Assume that every point is valid and in its subgroup, and that two points are not at infinity.

Then some `τ` makes point `i` represent `τ^i` times the generator, in both groups. -/
theorem checksSufficient_of_subgroupChecks
    (laws : Bls.PairingLaws)
    (contribution : Contribution) (transcript : Transcript)
    (checks : Checks contribution transcript)
    (hτ : G1.Valid transcript.previousTau ∧ transcript.previousTau.inSubgroup = true)
    (hpk : G2.Valid contribution.potPubkey ∧ contribution.potPubkey.inSubgroup = true)
    (hg1 : ∀ i (hi : i < contribution.g1Powers.size),
      G1.Valid (contribution.g1Powers[i]'hi) ∧ (contribution.g1Powers[i]'hi).inSubgroup = true)
    (hg2 : ∀ i (hi : i < contribution.g2Powers.size),
      G2.Valid (contribution.g2Powers[i]'hi) ∧ (contribution.g2Powers[i]'hi).inSubgroup = true)
    (previousTauNonzero : G1.isInfinity transcript.previousTau = false)
    (pubkeyNonzero : G2.isInfinity contribution.potPubkey = false) :
    ∃ τ : Fr,
      (∀ i (hi : i < contribution.g1Powers.size),
        G1.Represents (contribution.g1Powers[i]'hi) (Fr.powNat τ i)) ∧
      (∀ i (hi : i < contribution.g2Powers.size),
        G2.Represents (contribution.g2Powers[i]'hi) (Fr.powNat τ i)) := by
  obtain ⟨exponents⟩ := nonempty_subgroupExponents contribution transcript hτ hpk hg1 hg2
  exact ⟨_, checksSufficient laws contribution transcript checks exponents
    previousTauNonzero pubkeyNonzero⟩

end EthLib.Cryptography.Kzg.CeremonyChecks

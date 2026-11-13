module

public import EthLib.Cryptography.Proofs.X25519
public import EthLib.Cryptography.Proofs.X25519.Field
public import EthLib.Cryptography.Proofs.MontgomeryCurve

/-!
# Proofs: the X25519 ladder computes a scalar multiple

Curve25519 is the curve `v^2 = u^3 + 486662 u^2 + u` over the integers modulo `2^255 - 19`.

Let `P` be a point on it whose u-coordinate is not `0`, and `k` a scalar below `2^255`.

The ladder of [RFC 7748 §5][rfc] reads the bits of `k`.

After the pending swap, its first pair is a projective u-coordinate of `[k] P`.

So X25519 of the encoded u-coordinate of `P` encodes that of `[k] P`, for the clamped scalar `k`.

It returns `0` when `[k] P` is the point at infinity.

[rfc]: https://www.rfc-editor.org/rfc/rfc7748#section-5
-/

@[expose] public section

namespace EthLib.Cryptography.X25519

open MontgomeryCurve

/-- Curve25519, `v^2 = u^3 + 486662 u^2 + u`, RFC 7748 §4.1. -/
abbrev curve25519 : WeierstrassCurve.Affine (ZMod modulus) :=
  MontgomeryCurve.curve (486662 : ZMod modulus)

/-- Swapping by an exclusive or is swapping twice. -/
private theorem conditionalSwap_bne (a b : Bool) (s : LadderState) :
    conditionalSwap (a != b) s = conditionalSwap b (conditionalSwap a s) := by
  cases a <;> cases b <;> rfl

/-- The new first pair of a step is the doubling of the swapped first pair. -/
private theorem ladderStep_first (u : Fp) (bit : Bool) (s : LadderState) :
    let t := conditionalSwap (s.swap != bit) s
    toZMod (ladderStep u bit s).x2 = (double 121665 (toZMod t.x2) (toZMod t.z2)).1 ∧
      toZMod (ladderStep u bit s).z2 = (double 121665 (toZMod t.x2) (toZMod t.z2)).2 := by
  constructor <;> rfl

/-- The new second pair of a step is the differential addition of the swapped pairs. -/
private theorem ladderStep_second (u : Fp) (bit : Bool) (s : LadderState) :
    let t := conditionalSwap (s.swap != bit) s
    toZMod (ladderStep u bit s).x3 =
        (diffAdd (toZMod u) (toZMod t.x2) (toZMod t.z2) (toZMod t.x3) (toZMod t.z3)).1 ∧
      toZMod (ladderStep u bit s).z3 =
        (diffAdd (toZMod u) (toZMod t.x2) (toZMod t.z2) (toZMod t.x3) (toZMod t.z3)).2 := by
  constructor <;> rfl

/-- The constant of the doubling is `(A - 2) / 4` for Curve25519. -/
private theorem four_mul_a24 : 4 * (121665 : ZMod modulus) = 486662 - 2 := by
  norm_num

/-- `2` is not zero in the field of Curve25519. -/
private theorem two_ne_zero' : (2 : ZMod modulus) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod modulus) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact absurd (Nat.le_of_dvd (by norm_num) h2) (by unfold modulus; norm_num)

/-- A point and its negation share their u-coordinate. -/
private theorem uCoord_neg (P : curve25519.Point) : uCoord (-P) = uCoord P := by
  cases P <;> rfl

/-- A pair of `(n • P, (n + 1) • P)` after the pending swap. -/
private def Inv (P : curve25519.Point) (s : LadderState) (n : Nat) : Prop :=
  let t := conditionalSwap s.swap s
  Represents (toZMod t.x2) (toZMod t.z2) (n • P) ∧
    Represents (toZMod t.x3) (toZMod t.z3) ((n + 1) • P)

/-- One step with bit `b` takes the pairs of `n` to the pairs of `2 n + b`. -/
private theorem inv_ladderStep {P : curve25519.Point} {u : Fp} (hu : toZMod u = uCoord P)
    (hP : uCoord P ≠ 0) {s : LadderState} {n : Nat} (h : Inv P s n) (b : Bool) :
    Inv P (ladderStep u b s) (2 * n + b.toNat) := by
  obtain ⟨h1, h2⟩ := ladderStep_first u b s
  obtain ⟨h3, h4⟩ := ladderStep_second u b s
  rw [conditionalSwap_bne] at h1 h2 h3 h4
  obtain ⟨hQ, hR⟩ := h
  have hswap : (ladderStep u b s).swap = b := rfl
  unfold Inv
  rw [hswap]
  generalize conditionalSwap s.swap s = t at hQ hR h1 h2 h3 h4
  generalize ladderStep u b s = s' at h1 h2 h3 h4
  have hu0 : toZMod u ≠ 0 := hu ▸ hP
  cases b
  · simp only [conditionalSwap, Bool.false_eq_true, ite_false] at h1 h2 h3 h4 ⊢
    rw [h1, h2, h3, h4]
    refine ⟨?_, ?_⟩
    · have := hQ.double four_mul_a24
      rwa [← add_nsmul, ← two_mul] at this
    · have hd : uCoord ((n + 1) • P - n • P) = toZMod u := by
        rw [add_nsmul, one_nsmul, add_sub_cancel_left, hu]
      have := hQ.diffAdd two_ne_zero' hR hd hu0
      rwa [← add_nsmul, ← add_assoc, ← two_mul] at this
  · simp only [conditionalSwap, ite_true] at h1 h2 h3 h4 ⊢
    rw [h1, h2, h3, h4]
    refine ⟨?_, ?_⟩
    · have hd : uCoord (n • P - (n + 1) • P) = toZMod u := by
        rw [add_nsmul, one_nsmul, sub_add_cancel_left, uCoord_neg, hu]
      have := hR.diffAdd two_ne_zero' hQ hd hu0
      rwa [← add_nsmul, add_comm (n + 1) n, ← add_assoc, ← two_mul] at this
    · have := hR.double four_mul_a24
      rw [← add_nsmul] at this
      convert this using 2
      simp only [Bool.toNat_true]
      omega

/-- The initial state holds the pairs of `0` and `1`. -/
private theorem inv_init {P : curve25519.Point} {u : Fp} (hu : toZMod u = uCoord P)
    (hP : uCoord P ≠ 0) : Inv P ⟨1, 0, u, 1, false⟩ 0 := by
  refine ⟨⟨1, one_ne_zero, ?_, ?_⟩, ?_⟩
  · simp [conditionalSwap]
  · simp [conditionalSwap]
  · cases P with
    | zero => exact absurd rfl hP
    | some x y h =>
      refine ⟨1, one_ne_zero, ?_, ?_⟩
      · simp [conditionalSwap, hu, uCoord]
      · simp [conditionalSwap]

/-- Reading bit `m` appends it below the bits above it. -/
private theorem div_two_pow_eq (k m : Nat) :
    k / 2 ^ m = 2 * (k / 2 ^ (m + 1)) + (k.testBit m).toNat := by
  rw [Nat.toNat_testBit, pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- After `j` steps, the state holds the pairs of the top `j` bits of `k`. -/
private theorem inv_foldl {P : curve25519.Point} {u : Fp} (hu : toZMod u = uCoord P)
    (hP : uCoord P ≠ 0) {k : Nat} (hk : k < 2 ^ 255) : ∀ j ≤ 255,
    Inv P ((List.range j).foldl (fun s i => ladderStep u (k.testBit (254 - i)) s)
      ⟨1, 0, u, 1, false⟩) (k / 2 ^ (255 - j))
  | 0, _ => by
    rw [Nat.sub_zero, Nat.div_eq_of_lt hk]
    exact inv_init hu hP
  | j + 1, hj => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have := inv_ladderStep hu hP (inv_foldl hu hP hk j (by omega)) (k.testBit (254 - j))
    have e : 255 - j = 254 - j + 1 := by omega
    rw [e, ← div_two_pow_eq] at this
    rwa [show 255 - (j + 1) = 254 - j by omega]

/-- The power `z ^ (p - 2)` is the inverse, `0` included. -/
private theorem pow_sub_two_eq_inv (z : ZMod modulus) : z ^ (modulus - 2) = z⁻¹ := by
  have h2 : 2 < modulus := by unfold modulus; norm_num
  by_cases hz : z = 0
  · rw [hz, inv_zero, zero_pow (by omega)]
  · apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show modulus - 2 + 1 = modulus - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one hz

/-- A reduced natural number is its cast to the field. -/
private theorem toZMod_ofNat (n : Nat) : toZMod (Fin.ofNat modulus n) = (n : ZMod modulus) := by
  rfl

/-- An element is the cast of its value. -/
private theorem toZMod_eq_val (x : Fp) : toZMod x = (x.val : ZMod modulus) :=
  (ZMod.natCast_zmod_val (toZMod x)).symm

/-- The final division of X25519 is a field division. -/
private theorem toZMod_div (x z : Fp) :
    toZMod (Fin.ofNat modulus (x.val * Nat.powMod z.val (modulus - 2) modulus)) =
      toZMod x * (toZMod z)⁻¹ := by
  rw [toZMod_ofNat, Nat.powMod_def, ← pow_sub_two_eq_inv, toZMod_eq_val x, toZMod_eq_val z]
  push_cast
  rw [ZMod.natCast_mod, Nat.cast_pow]

/-- After all 255 bits, the first pair is a projective u-coordinate of `[k] P`.

The pending swap is applied first, as X25519 applies it.

The second pair is then a projective u-coordinate of `[k + 1] P`. -/
theorem ladder_represents (k : Nat) (hk : k < 2 ^ 255) (P : curve25519.Point)
    (hP : uCoord P ≠ 0) :
    let s := conditionalSwap (ladder k (toZMod.symm (uCoord P))).swap
      (ladder k (toZMod.symm (uCoord P)))
    Represents (toZMod s.x2) (toZMod s.z2) (k • P) ∧
      Represents (toZMod s.x3) (toZMod s.z3) ((k + 1) • P) := by
  intro s
  have hu : toZMod (toZMod.symm (uCoord P)) = uCoord P := toZMod.apply_symm_apply _
  have := inv_foldl hu hP hk 255 le_rfl
  rw [Nat.sub_self, pow_zero, Nat.div_one] at this
  exact this

/-- X25519 of the encoded u-coordinate of `P` encodes the u-coordinate of `[k] P`.

Here `k` is the clamped scalar, and the u-coordinate of the point at infinity is `0`. -/
theorem x25519_encodeUCoordinate (key : Key) (P : curve25519.Point) (hP : uCoord P ≠ 0) :
    x25519 key (encodeUCoordinate (toZMod.symm (uCoord P))) =
      encodeUCoordinate (toZMod.symm (uCoord (decodeScalar key • P))) := by
  obtain ⟨h, -⟩ := ladder_represents (decodeScalar key) (decodeScalar_lt key) P hP
  rw [h.uCoord_eq, ← toZMod_div, RingEquiv.symm_apply_apply]
  simp only [x25519, decodeUCoordinate_encodeUCoordinate]

end EthLib.Cryptography.X25519

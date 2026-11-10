module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.Game
public import EthLib.Cryptography.Proofs.Secp256k1.Sign

/-!
# Proofs: EthLib's ECDSA verification is the verification of the game

The group is the group of the curve, of prime order `n`, and the scalars are the integers mod `n`.

The encoding `φ` of a point is its `x` coordinate as a 256-bit string, and `ψ` reduces it mod `n`.

The bijection `Π` permutes all `2^256` strings, as in the source with `L = 256`.

A message is hashed to 32 bytes, which are read big-endian as an integer mod `n`.

The source is [Fersch, Kiltz, Poettering](https://doi.org/10.1145/2976749.2978413).

That is ECDSA as GenDSA, by their §3.1.

The normal form of `s` is the low-s rule of [EIP-2](https://eips.ethereum.org/EIPS/eip-2).

GenDSA does not have it.

It is harmless: anyone can negate `s`, and the negation keeps a signature valid.

With `Π` the identity, the game's verification is EthLib's, for `r` and `s` below `n`.

The game draws `Π` uniformly, so a bound on it says nothing provable about `Π` the identity.

Applying it to EthLib assumes that the identity behaves as a bijective random oracle.

That is the heuristic of the source, which notes in §1 that it fails at the bit level.

The `x` coordinate meets part (b) of Definition 2 of the source, which their Lemma 2 proves.

Opposite points share their `x` coordinate, so negating `s` keeps a signature valid in the game too.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open Ecdsa Point

/-- The scalars: the integers mod `n`. -/
abbrev Scalar := ZMod Fn.modulus

/-- The coordinates of the points: the integers mod `p`. -/
abbrev Coord := ZMod Fp.modulus

/-- The `x` coordinate of a group element, and `0` for the identity, which no signature reads. -/
def xCoord : curve.Point → Coord
  | 0 => 0
  | .some x _ _ => x

/-- The 256-bit strings, read as integers below `2^256`: the set that the bijection permutes. -/
abbrev Bits256 := Fin (2 ^ 256)

/-- The encoding `φ` of a point: its `x` coordinate as a 256-bit string. -/
def encodeX (R : curve.Point) : Bits256 :=
  ⟨(xCoord R).val, (ZMod.val_lt (xCoord R)).trans Fp.modulus_lt_two_pow⟩

variable {M : Type}

/-- EthLib's ECDSA as a GenDSA scheme, for messages that `H` hashes to 32 bytes.

A message is what `H` hashes, such as a transaction.

With `H` the identity on digests, forging needs no signature.

Pick `a` and `b`, and let `t` be the conversion of `a g + b X`.

If `b`, `t` and `a g + b X` are nonzero, `(t, t / b)` is valid on each digest read as `a t / b`. -/
noncomputable def ecdsaScheme (H : M → Vector UInt8 32) : Scheme Scalar curve.Point Bits256 M where
  g := toPoint generator
  encode := encodeX
  reduce a := (a.val : Scalar)
  hash m := (hashToInt (H m) : Scalar)
  normalize s := if isLowS s.val then s else -s

variable (H : M → Vector UInt8 32)

/-- The base point is not the identity. -/
theorem ecdsaScheme_g_ne_zero : (ecdsaScheme H).g ≠ 0 :=
  toPoint_generator_ne_zero

/-- Opposite points have the same `x` coordinate. -/
theorem ecdsaScheme_encodeNeg : (ecdsaScheme H).EncodeNeg := by
  intro X
  cases X with
  | zero => rfl
  | some x y h => rfl

/-- Two nonzero points with the same `x` coordinate are equal or opposite.

That is part (b) of Definition 2 of the source, which their Lemma 2 proves. -/
theorem ecdsaScheme_semiInjective : (ecdsaScheme H).SemiInjective := by
  intro X Y hX hY h
  cases X with
  | zero => exact absurd rfl hX
  | some x1 y1 h1 =>
    cases Y with
    | zero => exact absurd rfl hY
    | some x2 y2 h2 =>
      have hv := congrArg Fin.val h
      simp only [ecdsaScheme, encodeX, xCoord] at hv
      obtain rfl : x1 = x2 := ZMod.val_injective _ hv
      rcases Fp.eq_or_eq_neg_of_mul_self
          (((equation_iff _ _).mp h2.1).trans ((equation_iff _ _).mp h1.1).symm) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (by rw [WeierstrassCurve.Affine.Point.neg_some]; simp only [negY_eq])

/-- The low-s rule keeps `s` or negates it. -/
theorem ecdsaScheme_normalizeSign : (ecdsaScheme H).NormalizeSign := by
  intro s
  simp only [ecdsaScheme]
  split_ifs <;> simp

/-- A nonzero group element whose `x` reduces to `r` is a point `(x, y)` with `x mod n = r`. -/
private theorem xCoord_iff {r : Nat} (hr : r < Fn.modulus) (R : curve.Point) :
    (R ≠ 0 ∧ ((xCoord R).val : Scalar) = r) ↔
      ∃ x y : Fp, (affine x y).isOnCurve = true ∧ toPoint (affine x y) = R ∧
        x.val % Fn.modulus = r := by
  have hval (x : Fp) : (Fp.toZMod x).val = x.val := rfl
  constructor
  · rintro ⟨hR0, hx⟩
    obtain ⟨p, hp, rfl⟩ := toPoint_surjective R
    cases p with
    | infinity => exact absurd toPoint_infinity hR0
    | affine x y =>
      refine ⟨x, y, hp, rfl, ?_⟩
      rw [toPoint_affine hp] at hx
      simp only [xCoord] at hx
      rw [hval, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr] at hx
      exact hx
  · rintro ⟨x, y, hc, rfl, hx⟩
    rw [toPoint_affine hc]
    refine ⟨(fun h => nomatch h), ?_⟩
    simp only [xCoord]
    rw [hval, ← hx, ZMod.natCast_mod]

/-- EthLib's verification is the game's, with `Π` the identity, when `r` and `s` are below `n`.

The key is any pair: one off the curve maps to the identity, which both reject. -/
theorem ecdsa_verify_eq_verify_ecdsaScheme (q : Point) (m : M) (r s : Nat) :
    Ecdsa.verify q (H m) r s = (decide (r < Fn.modulus ∧ s < Fn.modulus) &&
      verify (ecdsaScheme H) (Equiv.refl Bits256) (toPoint q) m r s) := by
  cases hq : q.isOnCurve with
  | false =>
    rw [verify_of_not_isOnCurve hq, toPoint_eq_zero_of_isOnCurve_eq_false hq]
    simp [Security.verify]
  | true =>
    rw [Bool.eq_iff_iff, verify_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
    by_cases hrs : r < Fn.modulus ∧ s < Fn.modulus
    swap
    · exact iff_of_false (fun h => hrs ⟨h.1.2, h.2.1.2⟩) (fun h => hrs h.1)
    obtain ⟨hr, hs⟩ := hrs
    have hr0 : (r : Scalar) ≠ 0 ↔ 0 < r := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact ⟨fun h => Nat.pos_of_ne_zero fun h0 => h (h0 ▸ dvd_zero _),
        fun h hd => by have := Nat.eq_zero_of_dvd_of_lt hd hr; omega⟩
    have hs0 : (s : Scalar) ≠ 0 ↔ 0 < s := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact ⟨fun h => Nat.pos_of_ne_zero fun h0 => h (h0 ▸ dvd_zero _),
        fun h hd => by have := Nat.eq_zero_of_dvd_of_lt hd hs; omega⟩
    have hq0 : toPoint q ≠ 0 ↔ q ≠ infinity := not_congr (toPoint_eq_zero hq)
    have hU : ((s : Scalar)⁻¹ • ((hashToInt (H m) : Scalar) • toPoint generator +
        (r : Scalar) • toPoint q)) = ((hashToInt (H m) : Scalar) / s) • toPoint generator +
        ((r : Scalar) / s) • toPoint q := by
      rw [smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
    rw [Security.verify, decide_eq_true_iff]
    simp only [ecdsaScheme, conversion, Equiv.refl_apply]
    rw [hq0, hr0, hs0, hU]
    constructor
    · rintro ⟨hr', hs', hqi, -, x, y, hc, hR, hx⟩
      have hR0 := (xCoord_iff hr _).mpr ⟨x, y, hc, hR, hx⟩
      refine ⟨⟨hr, hs⟩, hqi, hr'.1, hs'.1, fun hU0 => hR0.1 ?_, hR0.2⟩
      rw [← hU, hU0, smul_zero]
    · rintro ⟨-, hqi, hr', hs', hU0, hx⟩
      have hR0 : ((hashToInt (H m) : Scalar) / s) • toPoint generator +
          ((r : Scalar) / s) • toPoint q ≠ 0 := by
        rw [← hU]
        exact smul_ne_zero (inv_ne_zero (hs0.mpr hs')) hU0
      obtain ⟨x, y, hc, hR, hx'⟩ := (xCoord_iff hr _).mp ⟨hR0, hx⟩
      exact ⟨⟨hr', hr⟩, ⟨hs', hs⟩, hqi, hq, x, y, hc, hR, hx'⟩

/-- EthLib's verification against the key of `sk` is the game's against the key `sk g`. -/
theorem ecdsa_verify_mul_generator_eq_verify_ecdsaScheme (sk : Fn) (m : M) (r s : Nat) :
    Ecdsa.verify (mul sk generator) (H m) r s = (decide (r < Fn.modulus ∧ s < Fn.modulus) &&
      verify (ecdsaScheme H) (Equiv.refl Bits256) (Fn.toZMod sk • (ecdsaScheme H).g) m r s) := by
  rw [ecdsa_verify_eq_verify_ecdsaScheme, toPoint_mul' _ isOnCurve_generator]
  rfl

/-- Every signature from EthLib's signing is the game's signature from some nonzero nonce.

EthLib draws the nonce by [RFC 6979](https://www.rfc-editor.org/rfc/rfc6979#section-3.2).

The game draws it uniformly.

The theorem does not say which nonce, and drops the recovery bit, which the game has no use for.

Any valid low-s signature has such a nonce, so this is correctness of signing in the game's terms.

It says nothing about how the nonces are drawn. -/
theorem exists_signNonce_of_sign {sk r s : Fn} {odd : Bool} {m : M}
    (h : Ecdsa.sign sk (H m) = .ok (r, s, odd)) :
    ∃ k : Scalar, k ≠ 0 ∧ signNonce (ecdsaScheme H) (Equiv.refl Bits256) (Fn.toZMod sk) m k =
      some (Fn.toZMod r, Fn.toZMod s) := by
  obtain ⟨-, s0, odd0, hw, hs⟩ := sign_spec h
  obtain ⟨k, x, y, hk, hR, -, rfl, hr0, rfl, hs0, -⟩ := signWith_spec hw
  have hc : (affine x y).isOnCurve = true := hR ▸ isOnCurve_mul k isOnCurve_generator
  have hconv : conversion (ecdsaScheme H) (Equiv.refl Bits256)
      (Fn.toZMod k • (ecdsaScheme H).g) = Fn.toZMod (Fin.ofNat _ x.val) := by
    simp only [conversion, ecdsaScheme, Equiv.refl_apply]
    rw [← toPoint_mul' k isOnCurve_generator, hR, toPoint_affine hc, toZMod_ofNat]
    rfl
  refine ⟨Fn.toZMod k, toZMod_ne_zero hk, ?_⟩
  set r := (Fin.ofNat Fn.modulus x.val : Fn)
  set e := (Fin.ofNat Fn.modulus (hashToInt (H m)) : Fn)
  have hu : (ecdsaScheme H).hash m + Fn.toZMod sk * Fn.toZMod r = Fn.toZMod (e + r * sk) := by
    simp only [ecdsaScheme, map_add, map_mul, e, toZMod_ofNat]
    ring
  have hdiv : Fn.toZMod (e + r * sk) / Fn.toZMod k = Fn.toZMod (k.inv * (e + r * sk)) := by
    rw [map_mul, Fn.toZMod_inv, div_eq_inv_mul]
  have hu0 : Fn.toZMod (e + r * sk) ≠ 0 :=
    fun h0 => toZMod_ne_zero hs0 (by rw [← hdiv, h0, zero_div])
  simp only [signNonce, hconv, hu]
  have hcond : (Fn.toZMod k = 0 ∨ Fn.toZMod r = 0 ∨ Fn.toZMod (e + r * sk) = 0) = False :=
    eq_false (by simp only [not_or]; exact ⟨toZMod_ne_zero hk, toZMod_ne_zero hr0, hu0⟩)
  rw [ite_eq_right_of_eq_false _ _ hcond, hdiv]
  simp only [ecdsaScheme]
  rcases hs with ⟨hl, rfl, -⟩ | ⟨hl, rfl, -⟩
  · have hl' : isLowS (Fn.toZMod (k.inv * (e + r * sk))).val = true := hl
    rw [ite_eq_left_of_eq_true _ _ (eq_true hl')]
  · have hl' : isLowS (Fn.toZMod (k.inv * (e + r * sk))).val = false := hl
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hl']; decide)), Fn.toZMod_neg]

end EthLib.Cryptography.Secp256k1.Security

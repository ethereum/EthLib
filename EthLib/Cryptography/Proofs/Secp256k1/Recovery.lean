module

public import EthLib.Base.Proofs.Nat
public import EthLib.Cryptography.Secp256k1.Recovery
public import EthLib.Cryptography.Proofs.Secp256k1.Ecdsa
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding
import EthLib.Cryptography.Proofs.Secp256k1.RecoveryMul
import EthLib.Cryptography.Proofs.Secp256k1.RecoveryField

/-!
# Proofs: public key recovery

- A recovered key verifies the signature.
- Recovery returns the key of the signer, with the parity of `R` as the id.
- When `r + n >= p`, every key that verifies a signature is recovered by one of the two ids.
- The swap of `s` for `n - s` swaps the two ids: EIP-2 removes that malleability.
- The two ids give two different keys.

The bound `r + n >= p` covers every `r` but the smallest `p - n`.

That is about `2^128` values of `r` out of `2^256`.

Below it, `R` could have `x = r + n`, which only the ids 2 and 3 reach.

Ethereum does not use those ids.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Fp.RecoveryField

/-- Passing the residue words individually preserves each field step. -/
theorem repeatFieldStep_eq (step : Element → Element) (n : Nat) (a : Element) :
    repeatFieldStep step n a = repeatSquare step n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    obtain ⟨⟨w0, w1, w2, w3⟩, h⟩ := a
    exact ih (step ⟨⟨w0, w1, w2, w3⟩, h⟩)

private theorem read_mul (a b : Element) : toFin (a * b) = toFin a * toFin b :=
  (toFin_eq _).trans <|
    (congrArg Montgomery.toFin (toMont_mul a b)).trans <|
      (Point.toFin_embedding.map_mul (toMont a) (toMont b)).trans <|
        congrArg₂ (· * ·) (toFin_eq a).symm (toFin_eq b).symm

private theorem read_input (a : Fp) : toFin (ofFin a) = a :=
  (toFin_eq _).trans <|
    (congrArg Montgomery.toFin (toMont_ofFin a)).trans <|
      Montgomery.toFin_ofFin (M := Fp.params) a

private theorem read_injective : Function.Injective toFin := by
  intro a b h
  exact toMont_injective (Point.toFin_embedding.injective ((toFin_eq a).symm.trans
    (h.trans (toFin_eq b))))

private theorem read_product (a b : Element) :
    Fp.toZMod (toFin (a * b)) = Fp.toZMod (toFin a) * Fp.toZMod (toFin b) := by
  rw [read_mul, map_mul]

private theorem read_squares {A R : Type} [Mul A] [Monoid R] (f : A → R)
    (readMul : ∀ a b, f (a * b) = f a * f b) (n : Nat) (a : A) :
    f (squareTimes n a) = f a ^ ((2 : Nat) ^ n) := by
  induction n generalizing a with
  | zero => exact (pow_one (f a)).symm
  | succ n ih =>
    change f (squareTimes n (a * a)) = _
    rw [ih, readMul, ← pow_two, ← pow_mul, Nat.pow_succ']

private theorem repeatSquare_eq (n : Nat) (a : Element) :
    repeatSquare square n a = squareTimes n a :=
  congrArg (fun step => repeatSquare step n a) (funext square_eq_mul)

private theorem read_chain {R : Type} [Monoid R] (f : Element → R)
    (readMul : ∀ a b, f (a * b) = f a * f b) (a : Element) :
    f (sqrtCandidate a) = f a ^ ((Fp.modulus + 1) / 4) := by
  simp only [sqrtCandidate, repeatFieldStep_eq, repeatSquare_eq, readMul, read_squares f readMul,
    ← pow_mul, ← pow_add, ← pow_succ]
  rfl

private theorem sqrt_candidate_eq (a : Fp) :
    toFin (sqrtCandidate (ofFin a)) = a.pow ((Fp.modulus + 1) / 4) := by
  apply Fp.toZMod.injective
  rw [Fp.toZMod_pow a ((Fp.modulus + 1) / 4) (by decide)]
  exact (read_chain (fun x => Fp.toZMod (toFin x)) read_product (ofFin a)).trans
    (congrArg (fun x => Fp.toZMod x ^ ((Fp.modulus + 1) / 4)) (read_input a))

private theorem sqrt_check_eq (a : Fp) (c : Element) :
    Option.map toFin (if square c = ofFin a then some c else none) =
      (if toFin c * toFin c = a then some (toFin c) else none) := by
  have hc : toFin c * toFin c = a ↔ c * c = ofFin a := by
    rw [← read_mul]
    exact (congrArg (toFin (c * c) = ·) (read_input a)).symm ▸ read_injective.eq_iff
  by_cases h : c * c = ofFin a
  · simp only [square_eq_mul, h, hc.mpr h, ite_true, Option.map_some]
  · have hn : ¬ toFin c * toFin c = a := mt hc.mp h
    simp only [square_eq_mul, h, hn, ite_false, Option.map_none]

/-- The addition chain returns the same checked square root as `Fp.sqrt`. -/
theorem sqrt_eq (a : Fp) : RecoveryField.sqrt a = Fp.sqrt a := by
  refine (sqrt_check_eq a (sqrtCandidate (ofFin a))).trans ?_
  rw [Fp.sqrt_eq_ite_pow, ← sqrt_candidate_eq a]

private theorem read_add (a b : Element) : toFin (a + b) = toFin a + toFin b := by
  simp only [toFin_eq, toMont_add, Point.toFin_embedding.map_add]
  rfl

private theorem read_sub (a b : Element) : toFin (a - b) = toFin a - toFin b := by
  simp only [toFin_eq, toMont_sub, Point.toFin_embedding.map_sub]
  rfl

private theorem read_zero : toFin (0 : Element) = 0 := by
  simp only [toFin_eq, toMont_zero, Point.toFin_embedding.map_zero]
  rfl

private theorem read_one : toFin (1 : Element) = 1 := by
  simp only [toFin_eq, toMont_one, Point.toFin_embedding.map_one]
  rfl

private theorem encode_decode (a : Element) : ofFin (toFin a) = a :=
  read_injective (read_input (toFin a))

private theorem encode_one : ofFin 1 = 1 :=
  read_injective ((read_input 1).trans read_one.symm)

private theorem encode_neg (a : Element) : ofFin (-toFin a) = 0 - a := by
  apply read_injective
  rw [read_input, read_sub, read_zero, zero_sub]

private theorem parity_word_eq (r : Raw) :
    (r.w0 &&& 1 == 1) = decide (rawToNat r % 2 = 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.toNat_and]
  rw [show (1 : UInt64).toNat = 2 ^ 1 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  unfold rawToNat
  simp only [Nat.shiftLeft_eq]
  omega

private theorem isOdd_eq (a : Element) : isOdd a = decide ((toFin a).val % 2 = 1) :=
  parity_word_eq (a * rawOne).raw

private theorem encode_affine (x y : Fp) :
    RecoveryMul.toRecoveryCoords (Point.affine x y) = ⟨ofFin x, ofFin y, 1⟩ := by
  unfold RecoveryMul.toRecoveryCoords Point.toJacobian Jacobian.ofAffine
  simp only [Jacobian.Coords.map, encode_one]

private theorem choose_root_eq (x : Fp) (c : Element) (odd : Bool) :
    (⟨ofFin x, if isOdd c = odd then c else 0 - c, 1⟩ : RecoveryMul.Coordinates) =
      RecoveryMul.toRecoveryCoords
        (Point.affine x (if decide ((toFin c).val % 2 = 1) = odd then toFin c else -toFin c)) := by
  rw [encode_affine, isOdd_eq]
  split <;> simp only [*, encode_decode, encode_neg]

private def pointWithRoot (x : Fp) (odd : Bool) (root : Option Fp) :
    Except Secp256k1Error Point :=
  root.elim (.error .noPointWithX) fun y =>
    .ok (.affine x (if decide (y.val % 2 = 1) = odd then y else -y))

private theorem selectRoot_eq (x : Fp) (r : Option Element) (odd : Bool) :
    selectRoot (ofFin x) r odd =
      (pointWithRoot x odd (r.map toFin)).map RecoveryMul.toRecoveryCoords := by
  cases r with
  | none => rfl
  | some c => exact congrArg Except.ok (choose_root_eq x c odd)

private theorem polynomial_eq (x : Fp) :
    square (ofFin x) * ofFin x + ofFin b = ofFin (x * x * x + b) := by
  apply read_injective
  simp only [square_eq_mul, read_add, read_mul, read_input]

private theorem decompress_polynomial_congr (x : Fp) (odd : Bool) :
    decompressCoords x odd =
      selectRoot (ofFin x) (sqrtElement (ofFin (x * x * x + b))) odd :=
  congrArg (fun rhs => selectRoot (ofFin x) (sqrtElement rhs) odd) (polynomial_eq x)

/-- Decompression gives the same point in the recovery representation. -/
theorem decompressCoords_eq (x : Fp) (odd : Bool) :
    decompressCoords x odd = (Point.decompress x odd).map RecoveryMul.toRecoveryCoords :=
  (decompress_polynomial_congr x odd).trans
    ((selectRoot_eq x (sqrtElement (ofFin (x * x * x + b))) odd).trans
      (congrArg (fun root => (pointWithRoot x odd root).map RecoveryMul.toRecoveryCoords)
        (sqrt_eq (x * x * x + b))))

end Fp.RecoveryField

namespace Ecdsa

open Point

/-- A field element below `n` read back as an integer, since `n < p`. -/
private theorem val_ofNat_of_lt {r : Nat} (hr : r < Fn.modulus) : (Fin.ofNat Fp.modulus r : Fp).val = r :=
  Nat.mod_eq_of_lt (Nat.lt_trans hr (by decide))

/-- A nonzero scalar stays nonzero in `ZMod n`. -/
theorem toZMod_ne_zero {a : Fn} (h : a ≠ 0) : Fn.toZMod a ≠ 0 :=
  fun h0 => h (Fn.toZMod.injective (h0.trans (map_zero _).symm))

/-- The point recovery computes, in the group: `r^(-1) s R - r^(-1) e G`. -/
private theorem toPoint_recovered (rInv sF e : Fn) {R : Point} (hR : R.isOnCurve = true) :
    toPoint (mul (rInv * sF) R + mul (-(rInv * e)) generator)
      = (Fn.toZMod rInv * Fn.toZMod sF) • toPoint R - (Fn.toZMod rInv * Fn.toZMod e) • toPoint generator := by
  rw [toPoint_add (isOnCurve_mul _ hR) (isOnCurve_mul _ isOnCurve_generator), toPoint_mul' _ hR,
    toPoint_mul' _ isOnCurve_generator, map_mul, map_neg, map_mul, neg_smul, sub_eq_add_neg]

private theorem recoverResult_eq (k l : Fn) {p : Point} (hp : p.isOnCurve = true) :
    (let q := RecoveryMul.mul k p l
     if q = .infinity then .error .pointAtInfinity else .ok q : Except Secp256k1Error Point) =
    (let q := mul k p + mul l generator
     if q = .infinity then .error .pointAtInfinity else .ok q) :=
  congrArg (fun q : Point =>
      if q = .infinity then (.error .pointAtInfinity : Except Secp256k1Error Point) else .ok q)
    ((RecoveryMul.mul_eq k l hp).trans (mulAdd_eq k l hp isOnCurve_generator))

private theorem bind_eq_of_ok {E A B : Type} {input : Except E A} {f g : A → Except E B}
    (h : ∀ a, input = .ok a → f a = g a) : input.bind f = input.bind g := by
  cases input with
  | error e => rfl
  | ok a => exact h a rfl

private theorem isOnCurve_of_decompress {x : Fp} {id : Bool} {p : Point}
    (h : decompress x id = .ok p) : p.isOnCurve = true := by
  obtain ⟨_, he, hc, -⟩ := decompress_eq_ok_iff.mp h
  exact he ▸ hc

private theorem rawOfNat_rawToNat (r : Fp.RecoveryField.Raw) :
    Fp.RecoveryField.rawOfNat (Fp.RecoveryField.rawToNat r) = r := by
  cases r with
  | mk a b c d =>
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have hc := c.toNat_lt
    have hd := d.toNat_lt
    unfold Fp.RecoveryField.rawOfNat Fp.RecoveryField.rawToNat
    dsimp only
    congr 1 <;> apply UInt64.toNat_inj.mp <;>
      (change _ % 2^64 = _
       simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
       omega)

private theorem writeRaw_eq (out : ByteArray) (r : Fp.RecoveryField.Raw) :
    Base.pushWord64
      (Base.pushWord64 (Base.pushWord64 (Base.pushWord64 out r.w3) r.w2) r.w1) r.w0 =
      Base.pushNatBytes32 out (Fp.RecoveryField.rawToNat r) := by
  have h := rawOfNat_rawToNat r
  have h0 := congrArg Fp.RecoveryField.Raw.w0 h
  have h1 := congrArg Fp.RecoveryField.Raw.w1 h
  have h2 := congrArg Fp.RecoveryField.Raw.w2 h
  have h3 := congrArg Fp.RecoveryField.Raw.w3 h
  simp only [Fp.RecoveryField.rawOfNat] at h0 h1 h2 h3
  simp only [Base.pushNatBytes32, h0, h1, h2, h3]

private theorem pushCoordinate_eq (out : ByteArray) (x : Fp.RecoveryField.Element) :
    pushCoordinate out x = Base.pushNatBytes32 out (Fp.RecoveryField.toFin x).val :=
  writeRaw_eq out (x * Fp.RecoveryField.rawOne).raw

private theorem encodeAffine_eq (x y : Fp.RecoveryField.Element) :
    encodeAffine x y = Point.encodeUncompressedDirect
      (.affine (Fp.RecoveryField.toFin x) (Fp.RecoveryField.toFin y)) := by
  simp only [encodeAffine, Point.encodeUncompressedDirect, pushCoordinate_eq]

private theorem map_affine_result {A B : Type}
    (finish : Fp.RecoveryField.Element → Fp.RecoveryField.Element → A) (f : A → B)
    (q : Option (Fp.RecoveryField.Element × Fp.RecoveryField.Element)) :
    (match q with
     | none => (.error .pointAtInfinity : Except Secp256k1Error A)
     | some (x, y) => .ok (finish x y)).map f =
      (match q with
      | none => .error .pointAtInfinity
      | some (x, y) => .ok (f (finish x y))) := by
  cases q <;> rfl

private theorem bind_finish_map {A B : Type}
    (finish : Fp.RecoveryField.Element → Fp.RecoveryField.Element → A)
    (f : A → B) (result : Except Secp256k1Error RecoveryMul.Coordinates) :
    (result.bind (finishProjective finish)).map f =
      result.bind (finishProjective (fun x y => f (finish x y))) := by
  cases result with
  | error e => rfl
  | ok q => exact map_affine_result finish f _

private theorem recoverUsing_map {A B : Type}
    (finish : Fp.RecoveryField.Element → Fp.RecoveryField.Element → A) (f : A → B)
    (hash : Vector UInt8 32) (r s : Nat) (id : Fin 2) :
    (recoverUsing finish hash r s id).map f =
      recoverUsing (fun x y => f (finish x y)) hash r s id :=
  bind_finish_map finish f (recoverProjective hash r s id)

section

open Fp.RecoveryField (Raw rawToNat rawToNat_eq)
open FnRecoveryWords (toFin)

private theorem rawScalarMul_lt (a b : Raw) : (FnRecoveryWords.mul a b).val < Fn.modulus := by
  rw [FnRecoveryWords.mul_val]
  exact Nat.mod_lt _ (by decide)

private theorem rawScalarNegate_lt (a : Raw) (ha : a.val < Fn.modulus) :
    (FnRecoveryWords.negate a).val < Fn.modulus := by
  rw [FnRecoveryWords.negate_val a ha]
  split <;> omega

private theorem rawScalarMul_toFin (a b : Raw) :
    toFin (FnRecoveryWords.mul a b) = toFin a * toFin b := by
  apply Fin.ext
  change rawToNat (FnRecoveryWords.mul a b) % Fn.modulus =
    (rawToNat a % Fn.modulus * (rawToNat b % Fn.modulus)) % Fn.modulus
  simp only [rawToNat_eq, FnRecoveryWords.mul_val, Nat.mod_mod]
  exact Nat.mul_mod _ _ _

private theorem rawScalarNegate_toFin (a : Raw) (ha : a.val < Fn.modulus) :
    toFin (FnRecoveryWords.negate a) = -toFin a := by
  apply Fin.ext
  rw [Fin.val_neg', FnRecoveryWords.toFin_val_of_lt a ha]
  change rawToNat (FnRecoveryWords.negate a) % Fn.modulus = (Fn.modulus - a.val) % Fn.modulus
  rw [rawToNat_eq, FnRecoveryWords.negate_val a ha]
  by_cases h : a.val = 0 <;> simp [h]

private theorem scalarWords_toFin (a : Raw) (h : rawToNat a < Fn.modulus) :
    toFin a = ⟨rawToNat a, h⟩ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt h

private theorem rawDecompress_eq (r : Raw) (hr : rawToNat r < Fp.modulus) (odd : Bool) :
    Fp.RecoveryField.decompressField (Fp.RecoveryField.ofRaw r (rawToNat_eq r ▸ hr)) odd =
      Fp.RecoveryField.decompressCoords (Fin.ofNat Fp.modulus (rawToNat r)) odd := by
  have hf : Fin.ofNat Fp.modulus (rawToNat r) = ⟨rawToNat r, hr⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hr)
  rw [Fp.RecoveryField.ofRaw_eq_ofFin r hr, hf]
  rfl

private theorem rawRecoveryProducts_eq (hash : Vector UInt8 32) (digest r s : Raw)
    (hd : rawToNat digest = hashToInt hash)
    (hr : rawToNat r < Fn.modulus) (hs : rawToNat s < Fn.modulus)
    (p : RecoveryMul.Coordinates) :
    let rInv := RecoveryInverse.invFnWords r
    let k := FnRecoveryWords.mul rInv s
    let l := FnRecoveryWords.negate (FnRecoveryWords.mul rInv digest)
    let a := RecoveryInverse.invFn ⟨rawToNat r, hr⟩
    RecoveryMul.mulProjectiveWords k p l =
      RecoveryMul.mulProjective (a * ⟨rawToNat s, hs⟩) p (-(a * Fin.ofNat _ (hashToInt hash))) := by
  let rInv := RecoveryInverse.invFnWords r
  let k := FnRecoveryWords.mul rInv s
  let m := FnRecoveryWords.mul rInv digest
  let l := FnRecoveryWords.negate m
  let a := RecoveryInverse.invFn ⟨rawToNat r, hr⟩
  have hm : m.val < Fn.modulus := rawScalarMul_lt _ _
  have hk : k.val < Fn.modulus := rawScalarMul_lt _ _
  have hl : l.val < Fn.modulus := rawScalarNegate_lt m hm
  have hInv : toFin rInv = a := by
    dsimp only [rInv, a]
    rw [RecoveryInverse.invFnWords_eq, FnRecoveryWords.toFin_fromFin,
      scalarWords_toFin r hr, RecoveryInverse.invFn_eq]
  have hK : toFin k = a * ⟨rawToNat s, hs⟩ := by
    dsimp only [k]
    rw [rawScalarMul_toFin, hInv, scalarWords_toFin s hs]
  have hDigest : toFin digest = Fin.ofNat Fn.modulus (hashToInt hash) := by
    unfold FnRecoveryWords.toFin
    rw [hd]
  have hL : toFin l = -(a * Fin.ofNat Fn.modulus (hashToInt hash)) := by
    dsimp only [l]
    rw [rawScalarNegate_toFin m hm]
    dsimp only [m]
    rw [rawScalarMul_toFin, hInv, hDigest]
  have h := RecoveryMul.mulProjectiveWords_eq_mulProjective k l p hk hl
  exact h.trans (congrArg₂ (fun x y => RecoveryMul.mulProjective x p y) hK hL)


end

private def affinePoint (x y : Fp.RecoveryField.Element) : Point :=
  .affine (Fp.RecoveryField.toFin x) (Fp.RecoveryField.toFin y)

private def checkPoint (p : Point) : Except Secp256k1Error Point :=
  if p = .infinity then .error .pointAtInfinity else .ok p

private theorem finishRecovery_eq (q : RecoveryMul.Coordinates) :
    finishProjective affinePoint q = checkPoint (RecoveryMul.ofRecoveryCoords q) := by
  unfold finishProjective checkPoint RecoveryMul.ofRecoveryCoords
  have h : RecoveryInverse.invMontgomery = RecoveryMul.batchInverse := rfl
  rw [h]
  unfold Point.ofCoords
  cases q.toAffine RecoveryMul.batchInverse <;> rfl

private theorem finish_mul (k l : Fn) (p : Point) :
    finishProjective affinePoint (RecoveryMul.mulProjective k (RecoveryMul.toRecoveryCoords p) l) =
      checkPoint (RecoveryMul.mul k p l) := by
  have hm : RecoveryMul.ofRecoveryCoords
      (RecoveryMul.mulProjective k (RecoveryMul.toRecoveryCoords p) l) =
        RecoveryMul.mul k p l := RecoveryMul.mulCoords_toRecovery k l p
  exact (finishRecovery_eq _).trans (congrArg checkPoint hm)

private theorem projective_in_range (hash : Vector UInt8 32) (r s : Nat) (id : Fin 2)
    (hr : 0 < r ∧ r < Fn.modulus) (hs : 0 < s ∧ s < Fn.modulus) :
    recoverProjective hash r s id =
      (Fp.RecoveryField.decompressCoords (Fin.ofNat _ r) (id == 1)).map (fun R =>
        let a := RecoveryInverse.invFn ⟨r, hr.2⟩
        RecoveryMul.mulProjective (a * ⟨s, hs.2⟩) R (-(a * Fin.ofNat _ (hashToInt hash)))) :=
  (dite_eq_left hr).trans (dite_eq_left hs)

section

open Fp.RecoveryField (Raw rawToNat)

private theorem bind_map_congr {E A B C : Type} (res : Except E A)
    (left : A → Except E C) (f : A → B) (g : B → Except E C)
    (h : ∀ a, left a = g (f a)) : res.bind left = (res.map f).bind g := by
  cases res with
  | error err => rfl
  | ok a => exact h a

private theorem recoverWords_decode (digest r s : Raw) (id : Fin 2)
    (h : ¬ (invalidSignatureWords r s = true)) (hp : r.val < Fp.modulus) :
    recoverEncodedFromWords digest r s id =
      (Fp.RecoveryField.decompressField (Fp.RecoveryField.ofRaw r hp) (id == 1)).bind
        (fun point => finishProjective encodeAffine
          (RecoveryMul.mulProjectiveWords
            (FnRecoveryWords.mul (RecoveryInverse.invFnWords r) s) point
            (FnRecoveryWords.negate
              (FnRecoveryWords.mul (RecoveryInverse.invFnWords r) digest)))) :=
  dite_eq_right h

private theorem recoverWords_invalid (digest r s : Raw) (id : Fin 2)
    (h : invalidSignatureWords r s = true) :
    recoverEncodedFromWords digest r s id =
      .error (.scalarOutOfRange (rawToNat (if invalidSignatureWord r then r else s))) :=
  dite_eq_left h

private theorem recoverUsing_invalid {A : Type}
    (finish : Fp.RecoveryField.Element → Fp.RecoveryField.Element → A)
    (hash : Vector UInt8 32) (r s : Nat) (id : Fin 2)
    (h : ¬ ((0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus))) :
    recoverUsing finish hash r s id =
      .error (.scalarOutOfRange (if 0 < r ∧ r < Fn.modulus then s else r)) := by
  have hProjective : recoverProjective hash r s id =
      .error (.scalarOutOfRange (if 0 < r ∧ r < Fn.modulus then s else r)) := by
    by_cases hr : 0 < r ∧ r < Fn.modulus
    · rw [ite_eq_left hr]
      exact (dite_eq_left hr).trans (dite_eq_right (fun hs => h ⟨hr, hs⟩))
    · rw [ite_eq_right hr]
      exact dite_eq_right hr
  exact congrArg (fun res => res.bind (finishProjective finish)) hProjective

private theorem invalidScalarValue_eq (r s : Raw) :
    rawToNat (if invalidSignatureWord r then r else s) =
      if 0 < rawToNat r ∧ rawToNat r < Fn.modulus then rawToNat s else rawToNat r := by
  by_cases hr : 0 < rawToNat r ∧ rawToNat r < Fn.modulus
  · have h : ¬ (invalidSignatureWord r = true) := fun h => (invalidSignatureWord_iff r).mp h hr
    rw [ite_eq_right h, ite_eq_left hr]
  · have h : invalidSignatureWord r = true := (invalidSignatureWord_iff r).mpr hr
    rw [ite_eq_left h, ite_eq_right hr]

private theorem recoverWords_valid_eq (hash : Vector UInt8 32) (digest r s : Raw)
    (hd : rawToNat digest = hashToInt hash) (id : Fin 2)
    (hr : 0 < rawToNat r ∧ rawToNat r < Fn.modulus)
    (hs : 0 < rawToNat s ∧ rawToNat s < Fn.modulus) :
    recoverEncodedFromWords digest r s id = recoverEncoded hash (rawToNat r) (rawToNat s) id := by
  have hgood : ¬ (invalidSignatureWords r s = true) := by
    intro h
    exact (invalidSignatureWords_iff r s).mp h ⟨hr, hs⟩
  have hp : rawToNat r < Fp.modulus := Nat.lt_trans hr.2 (by decide)
  let k := FnRecoveryWords.mul (RecoveryInverse.invFnWords r) s
  let l := FnRecoveryWords.negate (FnRecoveryWords.mul (RecoveryInverse.invFnWords r) digest)
  let a := RecoveryInverse.invFn ⟨rawToNat r, hr.2⟩
  let wordFinish : RecoveryMul.Coordinates → Except Secp256k1Error ByteArray := fun point =>
    finishProjective encodeAffine (RecoveryMul.mulProjectiveWords k point l)
  let finMul : RecoveryMul.Coordinates → RecoveryMul.Coordinates := fun point =>
    RecoveryMul.mulProjective (a * ⟨rawToNat s, hs.2⟩) point (-(a * Fin.ofNat _ (hashToInt hash)))
  let finish := finishProjective encodeAffine
  let dec := Fp.RecoveryField.decompressCoords (Fin.ofNat Fp.modulus (rawToNat r)) (id == 1)
  have hRead : recoverEncodedFromWords digest r s id = dec.bind wordFinish :=
    (recoverWords_decode digest r s id hgood (Fp.RecoveryField.rawToNat_eq r ▸ hp)).trans
      (congrArg (fun res => res.bind wordFinish) (rawDecompress_eq r hp (id == 1)))
  have hUse : recoverEncoded hash (rawToNat r) (rawToNat s) id = (dec.map finMul).bind finish :=
    congrArg (fun res => res.bind finish)
      (projective_in_range hash (rawToNat r) (rawToNat s) id hr hs)
  have hMul (point : RecoveryMul.Coordinates) : wordFinish point = finish (finMul point) :=
    congrArg finish (rawRecoveryProducts_eq hash digest r s hd hr.2 hs.2 point)
  exact hRead.trans ((bind_map_congr dec wordFinish finMul finish hMul).trans hUse.symm)

/-- Reading the digest and signature in words preserves the encoded recovery result. -/
theorem recoverEncodedFromWords_eq (hash : Vector UInt8 32) (digest r s : Raw)
    (hd : rawToNat digest = hashToInt hash) (id : Fin 2) :
    recoverEncodedFromWords digest r s id = recoverEncoded hash (rawToNat r) (rawToNat s) id := by
  by_cases h : (0 < rawToNat r ∧ rawToNat r < Fn.modulus) ∧
      (0 < rawToNat s ∧ rawToNat s < Fn.modulus)
  · exact recoverWords_valid_eq hash digest r s hd id h.1 h.2
  · have hWords := recoverWords_invalid digest r s id ((invalidSignatureWords_iff r s).mpr h)
    rw [invalidScalarValue_eq] at hWords
    exact hWords.trans (recoverUsing_invalid encodeAffine hash (rawToNat r) (rawToNat s) id h).symm

end

private theorem bind_map_twice {E A B C D : Type} (result : Except E A)
    (f : A → B) (g : B → C) (h : C → Except E D) :
    ((result.map f).map g).bind h = result.bind (fun a => h (g (f a))) := by
  cases result <;> rfl

private theorem recover_point (hash : Vector UInt8 32) (r s : Nat)
    (hr : 0 < r ∧ r < Fn.modulus) (hs : 0 < s ∧ s < Fn.modulus)
    (p : Point) (hp : p.isOnCurve = true) :
    let e := Fin.ofNat Fn.modulus (hashToInt hash)
    let a := RecoveryInverse.invFn ⟨r, hr.2⟩
    let k := a * ⟨s, hs.2⟩
    let l := -(a * e)
    finishProjective affinePoint (RecoveryMul.mulProjective k (RecoveryMul.toRecoveryCoords p) l) =
      checkPoint (mul (Fn.inv ⟨r, hr.2⟩ * ⟨s, hs.2⟩) p +
        mul (-(Fn.inv ⟨r, hr.2⟩ * e)) generator) := by
  dsimp only
  refine (finish_mul _ _ p).trans ?_
  have hinv := congrArg (fun a : Fn =>
    checkPoint (RecoveryMul.mul (a * ⟨s, hs.2⟩) p (-(a * Fin.ofNat _ (hashToInt hash)))))
      (RecoveryInverse.invFn_eq ⟨r, hr.2⟩)
  exact hinv.trans (recoverResult_eq _ _ hp)

private theorem recoverUsing_affine_in_range (hash : Vector UInt8 32) (r s : Nat) (id : Fin 2)
    (hr : 0 < r ∧ r < Fn.modulus) (hs : 0 < s ∧ s < Fn.modulus) :
    recoverUsing affinePoint hash r s id = (decompress (Fin.ofNat _ r) (id == 1)).bind fun R =>
      let a := Fn.inv ⟨r, hr.2⟩
      let e := Fin.ofNat _ (hashToInt hash)
      checkPoint (mul (a * ⟨s, hs.2⟩) R + mul (-(a * e)) generator) := by
  let output := finishProjective affinePoint
  let scale (R : RecoveryMul.Coordinates) :=
    let a := RecoveryInverse.invFn ⟨r, hr.2⟩
    RecoveryMul.mulProjective (a * ⟨s, hs.2⟩) R (-(a * Fin.ofNat _ (hashToInt hash)))
  let orig := decompress (Fin.ofNat _ r) (id == 1)
  let decoded := Fp.RecoveryField.decompressCoords (Fin.ofNat _ r) (id == 1)
  calc
    recoverUsing affinePoint hash r s id = (recoverProjective hash r s id).bind output := rfl
    _ = (decoded.map scale).bind output :=
      congrArg (fun q => q.bind output) (projective_in_range hash r s id hr hs)
    _ = ((orig.map RecoveryMul.toRecoveryCoords).map scale).bind output :=
      congrArg (fun q => (q.map scale).bind output)
        (Fp.RecoveryField.decompressCoords_eq (Fin.ofNat _ r) (id == 1))
    _ = orig.bind (fun p => output (scale (RecoveryMul.toRecoveryCoords p))) :=
      bind_map_twice orig RecoveryMul.toRecoveryCoords scale output
    _ = _ := bind_eq_of_ok (fun p hp =>
      recover_point hash r s hr hs p (isOnCurve_of_decompress hp))

/-- Recovery in steps: the ranges, then the point `R`, then the key. -/
private theorem recover_eq (hash : Vector UInt8 32) (r s : Nat) (id : Fin 2) (hr : 0 < r ∧ r < Fn.modulus)
    (hs : 0 < s ∧ s < Fn.modulus) :
    recover hash r s id = (decompress (Fin.ofNat _ r) (id == 1)).bind fun R =>
      if mul (Fn.inv ⟨r, hr.2⟩ * ⟨s, hs.2⟩) R + mul (-(Fn.inv ⟨r, hr.2⟩ * Fin.ofNat _ (hashToInt hash))) generator
          = .infinity then .error .pointAtInfinity
      else .ok (mul (Fn.inv ⟨r, hr.2⟩ * ⟨s, hs.2⟩) R
        + mul (-(Fn.inv ⟨r, hr.2⟩ * Fin.ofNat _ (hashToInt hash))) generator) := by
  rw [recover, dite_eq_left hr, dite_eq_left hs]
  -- `R` comes from the decoder, so it is on the curve.
  cases hd : decompress (Fin.ofNat _ r) (id == 1) with
  | error e => rfl
  | ok R =>
    obtain ⟨y, rfl, hc, -⟩ := decompress_eq_ok_iff.mp hd
    simp only [bind, Except.bind]
    rw [mulAdd_eq _ _ hc isOnCurve_generator]

/-- A recovery fails outside the ranges `[1, n - 1]`. -/
theorem recover_range {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2} {q : Point}
    (h : recover hash r s id = .ok q) : (0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus) := by
  unfold recover at h
  split at h
  · split at h
    · exact ⟨by assumption, by assumption⟩
    · cases h
  · cases h

private theorem recoverUsing_affine_eq (hash : Vector UInt8 32) (r s : Nat) (id : Fin 2) :
    recoverUsing affinePoint hash r s id = recover hash r s id := by
  by_cases h : (0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus)
  · exact (recoverUsing_affine_in_range hash r s id h.1 h.2).trans
      (recover_eq hash r s id h.1 h.2).symm
  · have hSlow : recover hash r s id =
        .error (.scalarOutOfRange (if 0 < r ∧ r < Fn.modulus then s else r)) := by
      by_cases hr : 0 < r ∧ r < Fn.modulus
      · rw [ite_eq_left hr]
        exact (dite_eq_left hr).trans (dite_eq_right (fun hs => h ⟨hr, hs⟩))
      · rw [ite_eq_right hr]
        exact dite_eq_right hr
    exact (recoverUsing_invalid affinePoint hash r s id h).trans hSlow.symm

/-- Writing the recovered coordinates directly gives the same SEC 1 bytes. -/
theorem recoverEncoded_eq (hash : Vector UInt8 32) (r s : Nat) (id : Fin 2) :
    recoverEncoded hash r s id = (recover hash r s id).map Point.encodeUncompressedDirect := by
  unfold recoverEncoded
  rw [← recoverUsing_affine_eq, recoverUsing_map]
  exact congrArg (fun finish => recoverUsing finish hash r s id)
    (funext fun x => funext fun y => encodeAffine_eq x y)

/-- A recovered key is on the curve and is not `O`. -/
theorem recover_valid {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2} {q : Point}
    (h : recover hash r s id = .ok q) : q.isOnCurve = true ∧ q ≠ .infinity := by
  obtain ⟨hr, hs⟩ := recover_range h
  rw [recover_eq hash r s id hr hs] at h
  cases hd : decompress (Fin.ofNat _ r) (id == 1) with
  | error e => rw [hd] at h; cases h
  | ok R =>
    rw [hd] at h
    simp only [Except.bind] at h
    obtain ⟨y, rfl, hc, -⟩ := decompress_eq_ok_iff.mp hd
    split_ifs at h with hne
    obtain rfl := Except.ok.inj h
    exact ⟨isOnCurve_add (isOnCurve_mul _ hc) (isOnCurve_mul _ isOnCurve_generator), hne⟩

/-- Soundness of recovery: a recovered key verifies the signature. -/
theorem verify_recover {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2} {q : Point}
    (h : recover hash r s id = .ok q) : verify q hash r s = true := by
  obtain ⟨hr, hs⟩ := recover_range h
  obtain ⟨hqc, hqi⟩ := recover_valid h
  rw [recover_eq hash r s id hr hs] at h
  cases hd : decompress (Fin.ofNat _ r) (id == 1) with
  | error e => rw [hd] at h; cases h
  | ok R =>
    rw [hd] at h
    simp only [Except.bind] at h
    obtain ⟨y, rfl, hc, -⟩ := decompress_eq_ok_iff.mp hd
    split_ifs at h with hne
    obtain rfl := Except.ok.inj h
    · rw [verify, dite_eq_left hr, dite_eq_left hs, ite_eq_left ⟨hqi, hqc⟩]
      dsimp only
      have hG := isOnCurve_generator
      rw [mulAdd_eq _ _ hG hqc]
      -- The verifier rebuilds `R`: `e s^(-1) G + r s^(-1) (r^(-1) s R - r^(-1) e G) = R`.
      have hrebuilt : toPoint (mul (Fin.ofNat _ (hashToInt hash) * Fn.inv ⟨s, hs.2⟩) generator
          + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv ⟨s, hs.2⟩) (mul (Fn.inv ⟨r, hr.2⟩ * ⟨s, hs.2⟩) (.affine (Fin.ofNat _ r) y)
            + mul (-(Fn.inv ⟨r, hr.2⟩ * Fin.ofNat _ (hashToInt hash))) generator))
          = toPoint (.affine (Fin.ofNat _ r) y) := by
        have hr0 : Fn.toZMod ⟨r, hr.2⟩ ≠ 0 := toZMod_ne_zero (fun h0 => by
          have := congrArg Fin.val h0; simp at this; omega)
        have hs0 : Fn.toZMod ⟨s, hs.2⟩ ≠ 0 := toZMod_ne_zero (fun h0 => by
          have := congrArg Fin.val h0; simp at this; omega)
        rw [toPoint_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc), toPoint_mul' _ hG, toPoint_mul' _ hqc,
          toPoint_recovered _ _ _ hc]
        simp only [map_mul, Fn.toZMod_inv, smul_sub, smul_smul]
        -- Collect the two coefficients: `0` on `G`, `1` on `R`.
        have hA : Fn.toZMod (Fin.ofNat _ (hashToInt hash)) * (Fn.toZMod ⟨s, hs.2⟩)⁻¹
            = Fn.toZMod ⟨r, hr.2⟩ * (Fn.toZMod ⟨s, hs.2⟩)⁻¹
              * ((Fn.toZMod ⟨r, hr.2⟩)⁻¹ * Fn.toZMod (Fin.ofNat _ (hashToInt hash))) := by
          field_simp
        have hB : Fn.toZMod ⟨r, hr.2⟩ * (Fn.toZMod ⟨s, hs.2⟩)⁻¹ * ((Fn.toZMod ⟨r, hr.2⟩)⁻¹ * Fn.toZMod ⟨s, hs.2⟩) = 1 := by
          field_simp
        rw [hA, hB, one_smul]
        abel
      split
      · rename_i heq
        rw [heq, toPoint_infinity] at hrebuilt
        exact absurd ((toPoint_eq_zero hc).mp hrebuilt.symm) (by simp)
      · rename_i x' y' heq
        rw [heq] at hrebuilt
        have := (toPoint_inj (heq ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)) hc).mp hrebuilt
        cases this
        simp only [beq_iff_eq]
        rw [val_ofNat_of_lt hr.2, Nat.mod_eq_of_lt hr.2]

/-- Recovery returns `q` once `R` is found and the computed key is `q`, in the group. -/
private theorem recover_of_decompress {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2}
    (hr : 0 < r ∧ r < Fn.modulus) (hs : 0 < s ∧ s < Fn.modulus) {R q : Point}
    (hd : decompress (Fin.ofNat _ r) (id == 1) = .ok R) (hq : q.isOnCurve = true) (hqi : q ≠ .infinity)
    (heq : (Fn.toZMod (Fn.inv ⟨r, hr.2⟩) * Fn.toZMod ⟨s, hs.2⟩) • toPoint R
      - (Fn.toZMod (Fn.inv ⟨r, hr.2⟩) * Fn.toZMod (Fin.ofNat _ (hashToInt hash))) • toPoint generator = toPoint q) :
    recover hash r s id = .ok q := by
  obtain ⟨y, rfl, hc, -⟩ := decompress_eq_ok_iff.mp hd
  have hpt : mul (Fn.inv ⟨r, hr.2⟩ * ⟨s, hs.2⟩) (.affine (Fin.ofNat _ r) y)
      + mul (-(Fn.inv ⟨r, hr.2⟩ * Fin.ofNat _ (hashToInt hash))) generator = q :=
    (toPoint_inj (isOnCurve_add (isOnCurve_mul _ hc) (isOnCurve_mul _ isOnCurve_generator)) hq).mp
      ((toPoint_recovered _ _ _ hc).trans heq)
  rw [recover_eq hash r s id hr hs, hd]
  simp only [Except.bind]
  rw [hpt, ite_eq_right hqi]

/-- `d G` is not `O` when `d != 0`, since `G` has order `n`. -/
theorem mul_generator_ne_infinity {d : Fn} (hd : d ≠ 0) : mul d generator ≠ .infinity := by
  intro h
  have h0 := congrArg toPoint h
  rw [toPoint_mul' d isOnCurve_generator, toPoint_infinity, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact toZMod_ne_zero hd h0
  · exact toPoint_generator_ne_zero h0

/-- The recovery id of a point: the parity of its `y`. -/
def parityId (y : Fp) : Fin 2 := if y.val % 2 = 1 then 1 else 0

private theorem parityId_beq (y : Fp) : (parityId y == 1) = decide (y.val % 2 = 1) := by
  unfold parityId
  split <;> simp_all

/-- Completeness of recovery: the signer's key comes back.

The signer has the key `d` and the nonce `k`, and `R = k G` has coordinates `(x, y)` with `x < n`.

Then `r = x`, `s = k^(-1) (e + r d)`, and the id is the parity of `y`. -/
theorem recover_sign (d k : Fn) (hash : Vector UInt8 32) (hd : d ≠ 0) {x y : Fp}
    (hR : mul k generator = .affine x y) (hx : x.val < Fn.modulus) (hx0 : x.val ≠ 0)
    (hs : k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ x.val * d) ≠ 0) :
    recover hash x.val (k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ x.val * d)).val (parityId y)
      = .ok (mul d generator) := by
  set sig := k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ x.val * d) with hsig
  have hG := isOnCurve_generator
  have hrr : 0 < x.val ∧ x.val < Fn.modulus := ⟨Nat.pos_of_ne_zero hx0, hx⟩
  have hss : 0 < sig.val ∧ sig.val < Fn.modulus := ⟨Nat.pos_of_ne_zero (fun h => hs (Fin.ext h)), sig.isLt⟩
  have hk : k ≠ 0 := ne_zero_of_inv_mul_ne_zero hs
  -- `R` is the point with `x` and the parity of `y`.
  have hxx : (Fin.ofNat _ x.val : Fp) = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
  have hd' : decompress (Fin.ofNat _ x.val) (parityId y == 1) = .ok (.affine x y) := by
    rw [hxx, parityId_beq]
    exact decompress_eq_ok_iff.mpr ⟨y, rfl, hR ▸ isOnCurve_mul k hG, rfl⟩
  refine recover_of_decompress hrr hss hd' (isOnCurve_mul d hG) (mul_generator_ne_infinity hd) ?_
  -- `r^(-1) (s k G - e G) = r^(-1) (r d) G = d G`, since `s k = e + r d`.
  rw [← hR, toPoint_mul' k hG, toPoint_mul' d hG, smul_smul, ← sub_smul, Fin.eta sig hss.2]
  refine congrArg (· • toPoint generator) ?_
  have hr' : Fn.toZMod ⟨x.val, hrr.2⟩ = Fn.toZMod (Fin.ofNat _ x.val) :=
    congrArg Fn.toZMod (Fin.ext (Nat.mod_eq_of_lt hx).symm)
  have hr0 : Fn.toZMod (Fin.ofNat Fn.modulus x.val) ≠ 0 := by
    rw [← hr']
    exact toZMod_ne_zero (fun h0 => hx0 (by have h1 := congrArg Fin.val h0; rwa [Fin.val_zero] at h1))
  have hk0 := toZMod_ne_zero hk
  simp only [Fn.toZMod_inv, hr', hsig, map_mul, map_add]
  field_simp
  ring

/-- What a valid signature gives: the ranges, a valid key, and the rebuilt point `R`.

That point has `x_R mod n = r`. -/
theorem verify_rebuilt {q : Point} {hash : Vector UInt8 32} {r s : Nat} (hv : verify q hash r s = true) :
    ∃ (hr : 0 < r ∧ r < Fn.modulus) (hs : 0 < s ∧ s < Fn.modulus), q ≠ .infinity ∧ q.isOnCurve = true ∧
      ∃ x y : Fp, mul (Fin.ofNat _ (hashToInt hash) * Fn.inv ⟨s, hs.2⟩) generator
        + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv ⟨s, hs.2⟩) q = .affine x y ∧ x.val % Fn.modulus = r := by
  obtain ⟨hr, hs⟩ := verify_range hv
  have hq : q ≠ .infinity ∧ q.isOnCurve = true := by
    by_cases hi : q = .infinity
    · subst hi; rw [verify_infinity] at hv; cases hv
    · cases hc : q.isOnCurve
      · rw [verify_of_not_isOnCurve hc] at hv; cases hv
      · exact ⟨hi, rfl⟩
  refine ⟨hr, hs, hq.1, hq.2, ?_⟩
  rw [verify, dite_eq_left hr, dite_eq_left hs, ite_eq_left hq] at hv
  dsimp only at hv
  rw [mulAdd_eq _ _ isOnCurve_generator hq.2] at hv
  split at hv
  · cases hv
  · rename_i x y hR
    exact ⟨x, y, hR, by simpa using hv⟩

/-- A scalar read from a natural number is that number in `ZMod n`. -/
theorem toZMod_ofNat (e : Nat) : Fn.toZMod (Fin.ofNat _ e) = (e : ZMod Fn.modulus) := by
  apply ZMod.val_injective
  simp [Fn.toZMod, ZMod.val_natCast]
  rfl

/-- The scalars `e / s` and `r / s` that the verifier computes, in `ZMod n`. -/
private theorem toZMod_scalars (e r s : Nat) (hr : r < Fn.modulus) (hs : s < Fn.modulus) :
    Fn.toZMod (Fin.ofNat _ e * Fn.inv ⟨s, hs⟩) = (e : ZMod Fn.modulus) / s ∧
      Fn.toZMod ((⟨r, hr⟩ : Fn) * Fn.inv ⟨s, hs⟩) = (r : ZMod Fn.modulus) / s := by
  have hs' : (⟨s, hs⟩ : Fn) = Fin.ofNat _ s := Fin.ext (Nat.mod_eq_of_lt hs).symm
  have hr' : (⟨r, hr⟩ : Fn) = Fin.ofNat _ r := Fin.ext (Nat.mod_eq_of_lt hr).symm
  rw [map_mul, map_mul, Fn.toZMod_inv, hs', hr', toZMod_ofNat, toZMod_ofNat,
    toZMod_ofNat, div_eq_mul_inv, div_eq_mul_inv]
  exact ⟨rfl, rfl⟩

/-- Verification against a key is the verifying operation of SEC 1 v2 §4.1.4, in the group.

Let `e` be the hash read as a natural number.

A signature `(r, s)` is valid under the key `Q` exactly when these hold:

- `r` and `s` lie in `[1, n - 1]`;
- `Q` lies on the curve and is not `O`;
- `R = (e / s) G + (r / s) Q` is a point `(x, y)` other than `O`, with `x mod n = r`.

The scalars `e / s` and `r / s` are taken modulo `n`.

It is about verification against a given key; recovery, which ECRECOVER runs, is not covered. -/
theorem verify_eq_true_iff {q : Point} {hash : Vector UInt8 32} {r s : Nat} :
    verify q hash r s = true ↔
      (0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus) ∧ q ≠ .infinity ∧
        q.isOnCurve = true ∧
        ∃ x y : Fp, (affine x y).isOnCurve = true ∧
          toPoint (affine x y) = ((hashToInt hash : ZMod Fn.modulus) / s) • toPoint generator
            + ((r : ZMod Fn.modulus) / s) • toPoint q ∧
          x.val % Fn.modulus = r := by
  have hG := isOnCurve_generator
  constructor
  · intro hv
    obtain ⟨hr, hs, hqi, hqc, x, y, hR, hx⟩ := verify_rebuilt hv
    obtain ⟨h1, h2⟩ := toZMod_scalars (hashToInt hash) r s hr.2 hs.2
    have hc : (affine x y).isOnCurve = true :=
      hR ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)
    refine ⟨hr, hs, hqi, hqc, x, y, hc, ?_, hx⟩
    rw [← hR, toPoint_rebuilt _ _ hqc, h1, h2]
  · rintro ⟨hr, hs, hqi, hqc, x, y, hc, hR, hx⟩
    obtain ⟨h1, h2⟩ := toZMod_scalars (hashToInt hash) r s hr.2 hs.2
    rw [verify, dite_eq_left hr, dite_eq_left hs, ite_eq_left ⟨hqi, hqc⟩]
    dsimp only
    rw [mulAdd_eq _ _ isOnCurve_generator hqc]
    -- The point that the verifier rebuilds is `(x, y)`, since both have one image in the group.
    have heq : mul (Fin.ofNat _ (hashToInt hash) * Fn.inv ⟨s, hs.2⟩) generator
        + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv ⟨s, hs.2⟩) q = affine x y := by
      apply (toPoint_inj (isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)) hc).mp
      rw [toPoint_rebuilt _ _ hqc, h1, h2, hR]
    rw [heq]
    simp [hx]

/-- Completeness of recovery: a key that verifies a signature is recovered by one of the two ids.

The bound `p <= r + n` makes `x_R = r`: the other candidate `r + n` is not below `p`. -/
theorem recover_of_verify {q : Point} {hash : Vector UInt8 32} {r s : Nat} (hv : verify q hash r s = true)
    (hp : Fp.modulus ≤ r + Fn.modulus) : ∃ id : Fin 2, recover hash r s id = .ok q := by
  obtain ⟨hr, hs, hqi, hqc, x, y, hR, hx⟩ := verify_rebuilt hv
  have hG := isOnCurve_generator
  have hr0 : Fn.toZMod ⟨r, hr.2⟩ ≠ 0 :=
    toZMod_ne_zero (fun h0 => by have h1 := congrArg Fin.val h0; simp at h1; omega)
  have hs0 : Fn.toZMod ⟨s, hs.2⟩ ≠ 0 :=
    toZMod_ne_zero (fun h0 => by have h1 := congrArg Fin.val h0; simp at h1; omega)
  -- `x_R = r`, since `x_R = r mod n` and `x_R < p <= r + n`.
  have hxr : x.val = r := Base.eq_of_mod_eq_of_lt hx x.isLt hp
  have hxx : (Fin.ofNat _ r : Fp) = x := Fin.ext (by rw [Fin.val_ofNat, ← hxr, Nat.mod_eq_of_lt x.isLt])
  have hRc : (Point.affine x y).isOnCurve = true := hR ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)
  refine ⟨parityId y, recover_of_decompress (R := .affine x y) hr hs ?_ hqc hqi ?_⟩
  · rw [hxx, parityId_beq]
    exact decompress_eq_ok_iff.mpr ⟨y, rfl, hRc, rfl⟩
  · -- `r^(-1) (s R - e G) = Q`, since `s R = e G + r Q`.
    rw [← hR, toPoint_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc), toPoint_mul' _ hG, toPoint_mul' _ hqc]
    simp only [map_mul, Fn.toZMod_inv, smul_add, smul_smul]
    have hA : (Fn.toZMod ⟨r, hr.2⟩)⁻¹ * Fn.toZMod ⟨s, hs.2⟩ * (Fn.toZMod (Fin.ofNat _ (hashToInt hash))
        * (Fn.toZMod ⟨s, hs.2⟩)⁻¹) = (Fn.toZMod ⟨r, hr.2⟩)⁻¹ * Fn.toZMod (Fin.ofNat _ (hashToInt hash)) := by
      field_simp
    have hB : (Fn.toZMod ⟨r, hr.2⟩)⁻¹ * Fn.toZMod ⟨s, hs.2⟩ * (Fn.toZMod ⟨r, hr.2⟩ * (Fn.toZMod ⟨s, hs.2⟩)⁻¹) = 1 := by
      field_simp
    rw [hA, hB, one_smul]
    abel

/-- What a recovery gives: the point `R` with `x = r` and the parity of the id.

The key is then `r^(-1) (s R - e G)`. -/
private theorem recover_spec {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2} {q : Point}
    (h : recover hash r s id = .ok q) :
    ∃ (hr : 0 < r ∧ r < Fn.modulus) (hs : 0 < s ∧ s < Fn.modulus) (y : Fp),
      decompress (Fin.ofNat _ r) (id == 1) = .ok (.affine (Fin.ofNat _ r) y)
      ∧ (Point.affine (Fin.ofNat _ r) y).isOnCurve = true ∧ decide (y.val % 2 = 1) = (id == 1)
      ∧ toPoint q = (Fn.toZMod (Fn.inv ⟨r, hr.2⟩) * Fn.toZMod ⟨s, hs.2⟩) • toPoint (.affine (Fin.ofNat _ r) y)
        - (Fn.toZMod (Fn.inv ⟨r, hr.2⟩) * Fn.toZMod (Fin.ofNat _ (hashToInt hash))) • toPoint generator := by
  obtain ⟨hr, hs⟩ := recover_range h
  rw [recover_eq hash r s id hr hs] at h
  cases hd : decompress (Fin.ofNat _ r) (id == 1) with
  | error e => rw [hd] at h; cases h
  | ok R =>
    rw [hd] at h
    simp only [Except.bind] at h
    obtain ⟨y, rfl, hc, hpar⟩ := decompress_eq_ok_iff.mp hd
    split_ifs at h
    obtain rfl := Except.ok.inj h
    refine ⟨hr, hs, y, rfl, hc, hpar, ?_⟩
    exact toPoint_recovered (Fn.inv ⟨r, hr.2⟩) ⟨s, hs.2⟩ (Fin.ofNat _ (hashToInt hash)) hc

/-- A point of the curve has `y != 0`: `-7` is not a cube. -/
private theorem y_ne_zero {x y : Fp} (h : (Point.affine x y).isOnCurve = true) : y ≠ 0 := by
  rintro rfl
  have h0 := (isOnCurve_affine x 0).mp h
  exact cube_ne_neg_seven (Fp.toZMod x) (by rw [Fp.toZMod_zero] at h0; linear_combination -h0)

/-- `n - s` is `-s` mod `n`. -/
private theorem toZMod_sub_eq_neg {s : Nat} (hs : 0 < s ∧ s < Fn.modulus) (hs' : Fn.modulus - s < Fn.modulus) :
    Fn.toZMod ⟨Fn.modulus - s, hs'⟩ = -Fn.toZMod ⟨s, hs.2⟩ := by
  rw [← Fn.toZMod_neg]
  exact congrArg Fn.toZMod (Fin.ext (by simp only [Fin.neg_def]; exact (Nat.mod_eq_of_lt hs').symm))

/-- Replacing `s` by `n - s` swaps the recovery ids, and the key stays the same.

EIP-2 removes this malleability.

The flipped signature, with the flipped id, still names the sender. -/
theorem recover_neg_s {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2} {q : Point}
    (h : recover hash r s id = .ok q) : recover hash r (Fn.modulus - s) (1 - id) = .ok q := by
  obtain ⟨hqc, hqi⟩ := recover_valid h
  obtain ⟨hr, hs, y, -, hc, hpar, hq⟩ := recover_spec h
  have hs' : 0 < Fn.modulus - s ∧ Fn.modulus - s < Fn.modulus := by omega
  -- The other id picks `-R = (x, -y)`, whose `y` has the other parity.
  have hflip : ((1 - id) == 1) = !(id == 1) := by fin_cases id <;> rfl
  have hneg := Fp.val_neg_mod_two (y_ne_zero hc)
  have hd : decompress (Fin.ofNat _ r) ((1 - id) == 1) = .ok (.affine (Fin.ofNat _ r) (-y)) := by
    refine decompress_eq_ok_iff.mpr ⟨-y, rfl, isOnCurve_neg hc, ?_⟩
    rw [hflip, ← hpar]
    have h2 := Nat.mod_two_eq_zero_or_one y.val
    have h2' := Nat.mod_two_eq_zero_or_one (-y).val
    rcases h2 with h2 | h2 <;> simp [h2] <;> omega
  refine recover_of_decompress hr hs' hd hqc hqi ?_
  -- `(-s) (-R) = s R`.
  rw [hq, show (Point.affine (Fin.ofNat _ r) (-y)) = -(Point.affine (Fin.ofNat _ r) y) from rfl, toPoint_neg hc,
    toZMod_sub_eq_neg hs hs'.2, smul_neg, mul_neg, neg_smul, neg_neg]

/-- The two recovery ids give two different keys.

Their difference is `2 r^(-1) s R`.

It is not `O`, since `R` is not `O` and `2 r^(-1) s != 0` mod `n`. -/
theorem recover_ne {hash : Vector UInt8 32} {r s : Nat} {q0 q1 : Point} (h0 : recover hash r s 0 = .ok q0)
    (h1 : recover hash r s 1 = .ok q1) : q0 ≠ q1 := by
  obtain ⟨hr, hs, y0, -, hc0, hpar0, hq0⟩ := recover_spec h0
  obtain ⟨hr', hs', y1, -, hc1, hpar1, hq1⟩ := recover_spec h1
  intro heq
  subst heq
  -- `y1 = -y0`: same `x`, other parity.
  have hy : y1 = -y0 := by
    rcases Fp.eq_or_eq_neg_of_mul_self (((isOnCurve_affine _ _).mp hc1).trans ((isOnCurve_affine _ _).mp hc0).symm)
      with h | h
    · have := Fp.toZMod.injective h
      subst this
      simp at hpar0 hpar1
      omega
    · exact Fp.toZMod.injective (h.trans (Fp.toZMod_neg y0).symm)
  subst hy
  rw [show (Point.affine (Fin.ofNat _ r) (-y0)) = -(Point.affine (Fin.ofNat _ r) y0) from rfl, toPoint_neg hc0,
    hq0] at hq1
  -- The two keys agree only if `2 r^(-1) s R = O`.
  have h2 : ((2 : ZMod Fn.modulus) * (Fn.toZMod (Fn.inv ⟨r, hr.2⟩) * Fn.toZMod ⟨s, hs.2⟩))
      • toPoint (.affine (Fin.ofNat _ r) y0) = 0 := by
    rw [mul_smul, two_smul]
    rw [smul_neg] at hq1
    linear_combination (norm := module) hq1
  rcases smul_eq_zero.mp h2 with h2 | h2
  · have hr0 : Fn.toZMod ⟨r, hr.2⟩ ≠ 0 :=
      toZMod_ne_zero (fun h0 => by have h1 := congrArg Fin.val h0; simp at h1; omega)
    have hs0 : Fn.toZMod ⟨s, hs.2⟩ ≠ 0 :=
      toZMod_ne_zero (fun h0 => by have h1 := congrArg Fin.val h0; simp at h1; omega)
    rw [Fn.toZMod_inv] at h2
    simp only [mul_eq_zero, inv_eq_zero, hr0, hs0, or_false] at h2
    exact absurd h2 (by decide)
  · exact absurd ((toPoint_eq_zero hc0).mp h2) (by simp)

/-- The scalars `s / r` and `e / r` that recovery computes, in `ZMod n`. -/
private theorem toZMod_recover_scalars (e r s : Nat) (hr : r < Fn.modulus) (hs : s < Fn.modulus) :
    Fn.toZMod (Fn.inv ⟨r, hr⟩) * Fn.toZMod ⟨s, hs⟩ = (s : ZMod Fn.modulus) / r ∧
      Fn.toZMod (Fn.inv ⟨r, hr⟩) * Fn.toZMod (Fin.ofNat _ e) = (e : ZMod Fn.modulus) / r := by
  have hs' : (⟨s, hs⟩ : Fn) = Fin.ofNat _ s := Fin.ext (Nat.mod_eq_of_lt hs).symm
  have hr' : (⟨r, hr⟩ : Fn) = Fin.ofNat _ r := Fin.ext (Nat.mod_eq_of_lt hr).symm
  rw [Fn.toZMod_inv, hs', hr', toZMod_ofNat, toZMod_ofNat, toZMod_ofNat, div_eq_mul_inv,
    div_eq_mul_inv, mul_comm, mul_comm (e : ZMod Fn.modulus)]
  exact ⟨rfl, rfl⟩

/-- Recovery is the public key recovery of SEC 1 v2 §4.1.6, read in the group of the curve.

Let `e` be the hash read as a natural number, and `R` the point `(r, y)` of the curve.

Recovery returns the key `Q` exactly when these hold:

- `r` and `s` lie in `[1, n - 1]`;
- `R` lies on the curve, and the parity of `y` is the recovery id;
- `Q` is a point of the curve other than `O`, and `Q = (s / r) R - (e / r) G`.

The scalars `s / r` and `e / r` are taken modulo `n`.

The recovery ids are 0 and 1, so `R` always has `x = r`.

SEC 1 also tries `x = r + n`, for `x_R >= n`; recovery never does, so it leaves that case out. -/
theorem recover_eq_ok_iff {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2} {q : Point} :
    recover hash r s id = .ok q ↔
      (0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus) ∧ q ≠ .infinity ∧
        q.isOnCurve = true ∧
        ∃ y : Fp, (affine (Fin.ofNat _ r) y).isOnCurve = true ∧
          decide (y.val % 2 = 1) = (id == 1) ∧
          toPoint q = ((s : ZMod Fn.modulus) / r) • toPoint (affine (Fin.ofNat _ r) y)
            - ((hashToInt hash : ZMod Fn.modulus) / r) • toPoint generator := by
  constructor
  · intro h
    obtain ⟨hr, hs⟩ := recover_range h
    obtain ⟨hqc, hqi⟩ := recover_valid h
    obtain ⟨h1, h2⟩ := toZMod_recover_scalars (hashToInt hash) r s hr.2 hs.2
    refine ⟨hr, hs, hqi, hqc, ?_⟩
    rw [recover_eq hash r s id hr hs] at h
    cases hd : decompress (Fin.ofNat _ r) (id == 1) with
    | error e => rw [hd] at h; cases h
    | ok R =>
      rw [hd] at h
      simp only [Except.bind] at h
      obtain ⟨y, rfl, hc, hpar⟩ := decompress_eq_ok_iff.mp hd
      split_ifs at h
      obtain rfl := Except.ok.inj h
      refine ⟨y, hc, hpar, ?_⟩
      rw [toPoint_recovered _ _ _ hc, h1, h2]
  · rintro ⟨hr, hs, hqi, hqc, y, hc, hpar, hq⟩
    obtain ⟨h1, h2⟩ := toZMod_recover_scalars (hashToInt hash) r s hr.2 hs.2
    refine recover_of_decompress hr hs (decompress_eq_ok_iff.mpr ⟨y, rfl, hc, hpar⟩) hqc hqi ?_
    rw [h1, h2, hq]

end Ecdsa

end EthLib.Cryptography.Secp256k1

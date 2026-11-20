module

public import EthLib.Cryptography.Secp256k1.RecoveryField
import all EthLib.Cryptography.Secp256k1.RecoveryField
import all EthLib.Cryptography.Montgomery.Fin
import EthLib.Cryptography.Proofs.Montgomery.Core

/-!
# Proofs: the recovery field of secp256k1

The four-word recovery field agrees with the shared Montgomery field.

Its specialized square, shifts and fused operations give the corresponding field operations.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Fp.RecoveryField

open EthLib.Cryptography.Montgomery (Limbs)

private theorem product_sum (a : Words64) (b : UInt64) (r : Words64) (ha : a.top = 0) :
    let m0 := mac a.w0 b r.w0 0
    let m1 := mac a.w1 b r.w1 m0.hi
    let m2 := mac a.w2 b r.w2 m1.hi
    let m3 := mac a.w3 b r.w3 m2.hi
    let s4 := m3.hi + r.top
    let s5 := yes (s4 < m3.hi)
    m0.lo.toNat + wordRadix * value ⟨m1.lo, m2.lo, m3.lo, s4, s5⟩ =
      value r + value a * b.toNat := by
  dsimp only
  have h0 := mac_spec a.w0 b r.w0 0
  have h1 := mac_spec a.w1 b r.w1 (mac a.w0 b r.w0 0).hi
  have h2 := mac_spec a.w2 b r.w2
    (mac a.w1 b r.w1 (mac a.w0 b r.w0 0).hi).hi
  have h3 := mac_spec a.w3 b r.w3
    (mac a.w2 b r.w2
      (mac a.w1 b r.w1 (mac a.w0 b r.w0 0).hi).hi).hi
  have ht := add_with_carry
    (mac a.w3 b r.w3 (mac a.w2 b r.w2
      (mac a.w1 b r.w1 (mac a.w0 b r.w0 0).hi).hi).hi).hi r.top
  simp only [value, lowValue, ha, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero,
    Nat.add_mul, Nat.mul_assoc]
  simp only [wordRadix] at *
  simp only [UInt64.toNat_zero, Nat.add_zero] at h0
  omega

private theorem stage_spec (a : Words64) (b : UInt64) (r : Words64)
    (ha : a.top = 0) (hap : value a < Fp.modulus) (hr : value r < 2 * Fp.modulus) :
    value (stage a b r) < 2 * Fp.modulus ∧
      ∃ q, wordRadix * value (stage a b r) = value r + value a * b.toNat + q * Fp.modulus := by
  let m0 := mac a.w0 b r.w0 0
  let m1 := mac a.w1 b r.w1 m0.hi
  let m2 := mac a.w2 b r.w2 m1.hi
  let m3 := mac a.w3 b r.w3 m2.hi
  let s4 := m3.hi + r.top
  let s5 := yes (s4 < m3.hi)
  have hs5 : s5.toNat ≤ 1 := by
    change (yes (decide _)).toNat ≤ 1
    cases decide (s4 < m3.hi) <;> decide
  have h := red_spec (fun q _ => mulHighComplement q) mulHighComplement_spec
    m0.lo m1.lo m2.lo m3.lo s4 s5 (by omega)
  have hs := product_sum a b r ha
  change m0.lo.toNat + wordRadix * value ⟨m1.lo, m2.lo, m3.lo, s4, s5⟩ =
    value r + value a * b.toNat at hs
  rw [hs] at h
  change wordRadix * value (stage a b r) = value r + value a * b.toNat + _ at h
  refine ⟨?_, _, h⟩
  have hb := b.toNat_lt
  have hq := (m0.lo * inverseComplement).toNat_lt
  have H1 : value a * b.toNat ≤ Fp.modulus * (wordRadix-1) :=
    Nat.mul_le_mul (by omega) (by simp only [wordRadix]; omega)
  have H2 : (m0.lo * inverseComplement).toNat * Fp.modulus ≤ (wordRadix-1) * Fp.modulus :=
    Nat.mul_le_mul_right _ (by simp only [wordRadix]; omega)
  rw [Nat.mul_comm Fp.modulus] at H1
  simp only [wordRadix, Fp.modulus] at *
  omega

private theorem fold_mod (a t s f x q k : Nat)
    (h : wordRadix * t = s + a*x + q*Fp.modulus)
    (hprev : (f*s) % Fp.modulus = (a*k) % Fp.modulus) :
    (wordRadix*f*t) % Fp.modulus = (a*(k+f*x)) % Fp.modulus := by
  have hsum : f * (s + a*x + q*Fp.modulus) =
      f*s + a*(f*x) + (f*q)*Fp.modulus := by grind
  calc
    _ = (f * (wordRadix*t)) % Fp.modulus := by rw [Nat.mul_assoc, Nat.mul_left_comm]
    _ = _ := by
      rw [h, hsum, Nat.add_mul_mod_self_right, Nat.mul_add a,
        Nat.add_mod (f*s), Nat.add_mod (a*k), hprev]

theorem accum_spec (a b : Words64) (ha : a.top = 0) (hb : b.top = 0)
    (hap : value a < Fp.modulus) :
    value (accum a b) < 2 * Fp.modulus ∧
      (wordRadix^4 * value (accum a b)) % Fp.modulus = (value a * value b) % Fp.modulus := by
  let zero : Words64 := ⟨0,0,0,0,0⟩
  let s0 := stage a b.w0 zero
  let s1 := stage a b.w1 s0
  let s2 := stage a b.w2 s1
  let s3 := stage a b.w3 s2
  have hz : value zero = 0 := rfl
  obtain ⟨hb0, q0, h0⟩ := stage_spec a b.w0 zero ha hap (by rw [hz]; decide)
  obtain ⟨hb1, q1, h1⟩ := stage_spec a b.w1 s0 ha hap hb0
  obtain ⟨hb2, q2, h2⟩ := stage_spec a b.w2 s1 ha hap hb1
  obtain ⟨hb3, q3, h3⟩ := stage_spec a b.w3 s2 ha hap hb2
  refine ⟨hb3, ?_⟩
  have e0 := fold_mod (value a) (value s0) (value zero) 1 b.w0.toNat q0 0 h0 (by simp [hz])
  simp only [Nat.mul_one, Nat.one_mul, Nat.zero_add] at e0
  have e1 := fold_mod (value a) (value s1) (value s0) wordRadix b.w1.toNat q1 b.w0.toNat h1 e0
  have e2 := fold_mod (value a) (value s2) (value s1) (wordRadix^2) b.w2.toNat q2
    (b.w0.toNat + wordRadix*b.w1.toNat) h2 (by exact e1)
  have e3 := fold_mod (value a) (value s3) (value s2) (wordRadix^3) b.w3.toNat q3
    (b.w0.toNat + wordRadix*b.w1.toNat + wordRadix^2*b.w2.toNat) h3 (by exact e2)
  change (wordRadix^4 * value s3) % Fp.modulus = (value a * value b) % Fp.modulus
  simpa only [value, lowValue, hb, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero,
    show wordRadix * wordRadix^3 = wordRadix^4 by decide] using e3

private theorem Raw.words_fromWords (w : Words64) (h : w.top = 0) :
    (Raw.fromWords w).words = w := by
  cases w
  cases h
  rfl

/-- Four words represent a value smaller than `2^256`. -/
theorem rawToNat_lt (w : Raw) : rawToNat w < 2^256 := by
  rw [rawToNat_eq]
  exact lowValue_lt w.words

private theorem shifted_left (s x : UInt64) (hs : s.toNat ≤ 3) :
    (x <<< s).toNat = (x.toNat % 2^(64-s.toNat)) <<< s.toNat := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt (by omega : s.toNat < 64),
    Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have h := radix_split s hs
  change 2^64 = _ at h
  rw [h, Nat.mul_mod_mul_right]

private theorem shifted_lane (s hi lo : UInt64) (hpos : 0 < s.toNat) (hs : s.toNat ≤ 3) :
    ((hi <<< s) ||| (lo >>> (64-s))).toNat =
      (hi <<< s).toNat + (lo >>> (64-s)).toNat := by
  rw [UInt64.toNat_or, shifted_left s hi hs, ← Nat.shiftLeft_add_eq_or_of_lt
    (shifted_right_lt s lo hpos hs)]

private theorem shifted_word (s x : UInt64) (hpos : 0 < s.toNat) (hs : s.toNat ≤ 3) :
    (x <<< s).toNat + wordRadix * (x >>> (64-s)).toNat = x.toNat * 2^s.toNat := by
  rw [shifted_left s x hs, shifted_right s x hpos hs, Nat.shiftLeft_eq, radix_split s hs]
  rw [Nat.mul_right_comm _ (2^s.toNat), ← Nat.add_mul, Nat.mod_add_div]

/-- A shift keeps the bits above the four-word value in its fifth word. -/
theorem shift_val (s : UInt64) (w : Raw) (hpos : 0 < s.toNat) (hs : s.toNat ≤ 3) :
    (shift s w).val = w.val * 2^s.toNat := by
  have h0 := shifted_word s w.w0 hpos hs
  have h1 := shifted_word s w.w1 hpos hs
  have h2 := shifted_word s w.w2 hpos hs
  have h3 := shifted_word s w.w3 hpos hs
  simp only [shift, word_value_for_scale, raw_val_add, Words64.rawWords, Raw.fromWords]
  simp only [shifted_lane _ _ _ hpos hs, Nat.add_mul]
  rw [Nat.mul_right_comm w.w1.toNat wordRadix (2^s.toNat),
    Nat.mul_right_comm w.w2.toNat (wordRadix^2) (2^s.toNat),
    Nat.mul_right_comm w.w3.toNat (wordRadix^3) (2^s.toNat)]
  simp only [wordRadix] at *
  omega

/-- The reducer input folds the high part of the shifted value at `Fp.modulus`. -/
theorem scaleInput_val (s : UInt64) (w : Raw) (hpos : 0 < s.toNat) (hs : s.toNat ≤ 3) :
    (scaleInput s w).val + (shift s w).top.toNat * Fp.modulus = w.val * 2^s.toNat := by
  let shifted := shift s w
  have htop : shifted.top.toNat < 2^s.toNat := shifted_right_lt s w.w3 hpos hs
  have h8 : 2^s.toNat ≤ 8 := Nat.pow_le_pow_right (by decide) hs
  have hprod : (shifted.top * complement).toNat = shifted.top.toNat * 4294968273 := by
    rw [UInt64.toNat_mul]
    change shifted.top.toNat * 4294968273 % wordRadix = shifted.top.toNat * 4294968273
    apply Nat.mod_eq_of_lt
    simp only [wordRadix]
    omega
  change (addLow shifted.rawWords (shifted.top * complement)).val +
    shifted.top.toNat * Fp.modulus = _
  rw [addLow_val, hprod]
  have hshift := shift_val s w hpos hs
  rw [word_value_for_scale] at hshift
  change shifted.rawWords.val + shifted.top.toNat * (2^256) = _ at hshift
  simp only [Fp.modulus] at *
  omega

private theorem toMont_val (a : Element) : Limbs.val (n := 8) (toMont a).limbs = a.raw.val := by
  exact (val_narrow _ rfl).trans a.raw.val_eq.symm

private theorem ofMont_val (a : Fp.Montgomery) : (ofMont a).raw.val = Limbs.val (n := 8) a.limbs :=
  (Raw.fromWords_val _ rfl).trans (value_wide _)

private theorem mont_ext {a b : Fp.Montgomery} (h : Limbs.val (n := 8) a.limbs =
    Limbs.val (n := 8) b.limbs) : a = b := by
  have h := Limbs.val_injective (n := 8) h
  cases a
  cases b
  cases h
  rfl

/-- A change of limb packing preserves the original Montgomery residue. -/
theorem toMont_ofMont (a : Fp.Montgomery) : toMont (ofMont a) = a :=
  mont_ext ((toMont_val (ofMont a)).trans (ofMont_val a))

private theorem join_split (w : UInt64) :
    join w.toUInt32 (w >>> 32).toUInt32 = w :=
  UInt64.toNat_inj.mp ((join_value _ _).trans (split_value w))

private theorem wide_narrow (w : Words64) (h : w.top = 0) : wide (narrow w) = w := by
  cases w
  cases h
  simp only [wide, narrow, join_split]
  rfl

/-- Canonical residues have an injective representation in the general field. -/
theorem toMont_injective : Function.Injective toMont := by
  intro a b h
  have h := congrArg (fun z : Fp.Montgomery => wide z.limbs) h
  change wide (narrow a.raw.words) = wide (narrow b.raw.words) at h
  rw [wide_narrow _ rfl, wide_narrow _ rfl] at h
  have he := congrArg Raw.fromWords h
  cases a with
  | mk x hx =>
    cases b with
    | mk y hy =>
      change x = y at he
      cases he
      rfl

/-- Zero has the same residue in either representation. -/
theorem toMont_zero : toMont (0 : Element) = 0 := toMont_ofMont 0

/-- One has the same residue in either representation. -/
theorem toMont_one : toMont (1 : Element) = 1 := toMont_ofMont 1

private theorem finish_val (t : Words64) (ht : value t < 2*Fp.modulus) :
    (finish t ht).raw.val = value t % Fp.modulus := by
  have hu := reduceFast_spec t ht
  exact (Raw.fromWords_val (reduceFast t) hu.1).trans hu.2

private theorem scaled_residue (x y v : Nat)
    (h : (2^256 * v) % Fp.modulus = x*y % Fp.modulus) :
    (2^256 * (v % Fp.modulus)) % Fp.modulus = x*y % Fp.modulus :=
  (Nat.mul_mod_mod _ _ _).trans h

private theorem mul_val (a b : Element) :
    (2^256 * (mul a b).raw.val) % Fp.modulus = a.raw.val * b.raw.val % Fp.modulus := by
  let w := multiplyColumns a.raw.words b.raw.words
  let h := reduceWideInverse_spec w.1 w.2 (multiplyColumns_bound a.raw.words b.raw.words a.lt b.lt)
  have hv : (mul a b).raw.val = value (reduceWideInverse w.1 w.2) % Fp.modulus := finish_val _ h.1
  rw [hv]
  apply scaled_residue
  have hh := h.2
  change (wordRadix^4 * value (reduceWideInverse w.1 w.2)) % Fp.modulus =
    (lowValue (multiplyColumns a.raw.words b.raw.words).1 +
      wordRadix^4 * lowValue (multiplyColumns a.raw.words b.raw.words).2) % Fp.modulus at hh
  rw [multiplyColumns_spec] at hh
  exact hh

private theorem eq_of_radix_mul_mod {x y : Nat} (hx : x < Fp.modulus) (hy : y < Fp.modulus)
    (he : 2^256 * x % Fp.modulus = 2^256 * y % Fp.modulus) : x = y := by
  let inverse := 0xc9bd1905155383999c46c2c295f2b761bcb223fedc24a059d838091d0868192a
  have hi : (inverse * 2^256) % Fp.modulus = 1 := by decide
  have inv (v : Nat) : (inverse * (2^256 * v % Fp.modulus)) % Fp.modulus = v % Fp.modulus := by
    rw [Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, hi, Nat.one_mul]
  have h := congrArg (fun v => (inverse * v) % Fp.modulus) he
  rw [inv, inv, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
  exact h

/-- Squaring gives the same residue as multiplying a value by itself. -/
theorem square_eq_mul (a : Element) : square a = a * a := by
  let w := squareColumns a.raw.words
  let h := reduceWideInverse_spec w.1 w.2 (squareColumns_bound a.raw.words a.lt)
  have hv : (square a).raw.val = value (reduceWideInverse w.1 w.2) % Fp.modulus := finish_val _ h.1
  have hs : (2^256*(square a).raw.val) % Fp.modulus = (a.raw.val*a.raw.val) % Fp.modulus := by
    rw [hv]
    apply scaled_residue
    have hh := h.2
    change (wordRadix^4 * value (reduceWideInverse w.1 w.2)) % Fp.modulus =
      (lowValue (squareColumns a.raw.words).1 +
        wordRadix^4*lowValue (squareColumns a.raw.words).2) % Fp.modulus at hh
    rw [squareColumns_spec] at hh
    exact hh
  have he : (square a).raw.val = (a*a).raw.val := eq_of_radix_mul_mod
    (square a).lt (a*a).lt (hs.trans (mul_val a a).symm)
  apply toMont_injective
  apply mont_ext
  rw [toMont_val, toMont_val, he]

/-- Multiplication gives the same Montgomery residue in either representation. -/
theorem toMont_mul (a b : Element) : toMont (a*b) = toMont a * toMont b := by
  let x := toMont a
  let y := toMont b
  have hspec := (Montgomery.mulLimbs_spec Fp.params x.limbs x.lt y.limbs).2
  have hEq : Limbs.val (n := 8) (x*y).limbs =
      Limbs.val (n := 8) (Montgomery.mulWords (Limbs.get Fp.params.pLimbs) Fp.params.pinv
        (Limbs.get x.limbs) (Limbs.get y.limbs) Limbs.pack) := by
    change Limbs.val (n := 8) (Fp.params.mul x.limbs y.limbs) = _
    rw [Fp.params.mul_spec x.limbs y.limbs x.lt]
  change _ = x*y
  apply mont_ext
  have aeq := toMont_val a
  have beq := toMont_val b
  have hm := mul_val a b
  have hc := toMont_val (a*b)
  change (2^256 * _) % Fp.modulus =
    (Limbs.val (n := 8) x.limbs * Limbs.val (n := 8) y.limbs) % Fp.modulus at hspec
  rw [← hEq, aeq, beq] at hspec
  exact eq_of_radix_mul_mod (toMont (a*b)).lt (x*y).lt
    ((congrArg (fun v => (2^256 * v) % Fp.modulus) hc).trans (hm.trans hspec.symm))

/-- Reading the words directly gives the same field element as reading their integer value. -/
theorem ofRaw_eq_ofFin (w : Raw) (h : rawToNat w < Fp.modulus) :
    ofRaw w (rawToNat_eq w ▸ h) = ofFin ⟨rawToNat w, h⟩ := by
  unfold ofRaw ofFin
  congr 1
  apply toMont_injective
  apply mont_ext
  rw [toMont_val, toMont_val]
  change w.val = (rawOfNat (rawToNat w)).val
  exact (rawToNat_eq w).symm.trans (rawOfNat_val _ (rawToNat_lt w)).symm

private theorem toMont_readRaw (a : Fp) :
    (toMont (readRaw a)).limbs = Limbs.ofNat a.val := by
  apply Limbs.val_injective
  rw [toMont_val, Limbs.val_ofNat]
  change (rawOfNat a.val).val = a.val % 2^256
  have h : a.val < 2^256 := Nat.lt_trans a.isLt (by decide)
  rw [rawOfNat_val _ h, Nat.mod_eq_of_lt h]

/-- Both field implementations encode a canonical integer the same way. -/
theorem toMont_ofFin (a : Fp) : toMont (ofFin a) = Montgomery.ofFin a := by
  have h : toMont montgomerySquare = ⟨Fp.params.r2, Fp.params.r2_lt⟩ := by
    apply mont_ext
    decide
  simp only [ofFin, toMont_mul, h]
  change Montgomery.mulLimbs Fp.params Fp.params.r2 Fp.params.r2_lt
    (toMont (readRaw a)).limbs = Montgomery.mulLimbs Fp.params Fp.params.r2 Fp.params.r2_lt
      (Limbs.ofNat (a.val % Fp.modulus))
  rw [Nat.mod_eq_of_lt a.isLt, toMont_readRaw]

/-- Leaving either Montgomery representation gives the same field element. -/
theorem toFin_eq (a : Element) : toFin a = Montgomery.toFin (toMont a) := by
  apply Fin.ext
  change rawToNat (a * rawOne).raw = (toMont a).toNat
  rw [rawToNat_eq, ← toMont_val, toMont_mul, Montgomery.toNat_eq_val]
  have h : (toMont rawOne).limbs = Limbs.ofNat (n := 8) 1 := by decide
  exact congrArg (fun limbs =>
    Limbs.val (Montgomery.mulLimbs Fp.params (toMont a).limbs (toMont a).lt limbs).limbs) h

private theorem add_val (a b : Element) : (a+b).raw.val = (a.raw.val + b.raw.val) % Fp.modulus := by
  let u := add64 reduceFast a.raw.words b.raw.words
  have hu := add64_spec reduceFast reduceFast_spec a.raw.words b.raw.words rfl rfl
    (a.raw.val_eq ▸ a.lt) (b.raw.val_eq ▸ b.lt)
  change (Raw.fromWords u).val = _
  rw [Raw.fromWords_val u hu.1, hu.2, ← a.raw.val_eq, ← b.raw.val_eq]

private theorem sub_val (a b : Element) : (a-b).raw.val =
    (a.raw.val + Fp.modulus - b.raw.val) % Fp.modulus := by
  let u := subMasked a.raw.words b.raw.words
  have hu := subMasked_spec a.raw.words b.raw.words rfl rfl
    (a.raw.val_eq ▸ a.lt) (b.raw.val_eq ▸ b.lt)
  change (Raw.fromWords u).val = _
  rw [Raw.fromWords_val u hu.1, hu.2, ← a.raw.val_eq, ← b.raw.val_eq]

/-- Addition gives the same Montgomery residue in either representation. -/
theorem toMont_add (a b : Element) : toMont (a+b) = toMont a + toMont b := by
  apply mont_ext
  let x := toMont a
  let y := toMont b
  have h := Montgomery.addLimbs_spec Fp.params x.limbs y.limbs x.lt y.lt
  change Limbs.val (n := 8) (toMont (a+b)).limbs =
    Limbs.val (n := 8) (Montgomery.addCore (n := 8) x.limbs y.limbs Fp.params.pLimbs)
  rw [toMont_val, add_val]
  unfold Montgomery.addCore
  rw [h, toMont_val, toMont_val]
  rfl

/-- Subtraction gives the same Montgomery residue in either representation. -/
theorem toMont_sub (a b : Element) : toMont (a-b) = toMont a - toMont b := by
  apply mont_ext
  let x := toMont a
  let y := toMont b
  change Limbs.val (n := 8) (toMont (a-b)).limbs =
    Limbs.val (n := 8) (Montgomery.subLimbs Fp.params x.limbs y.limbs)
  rw [Montgomery.subLimbs_spec Fp.params x.lt y.lt, toMont_val, sub_val]
  rw [toMont_val, toMont_val]
  rfl

private theorem scale_val (s : UInt64) (w : Element) (hpos : 0 < s.toNat) (hs : s.toNat ≤ 3) :
    (scale s w hpos hs).raw.val = (w.raw.val * 2^s.toNat) % Fp.modulus := by
  let t := scaleInput s w.raw
  let u := reduceMasked t
  have hr := reduceMasked_spec t (scaleInput_lt s w.raw hpos hs)
  change (Raw.fromWords u).val = _
  rw [Raw.fromWords_val u hr.1, hr.2, ← scaleInput_val s w.raw hpos hs,
    Nat.add_mul_mod_self_right]

private theorem element_ext {a b : Element} (h : a.raw.val = b.raw.val) : a = b :=
  toMont_injective (mont_ext ((toMont_val a).trans (h.trans (toMont_val b).symm)))

private theorem add_self_val (x : Element) : (x+x).raw.val = x.raw.val * 2 % Fp.modulus := by
  rw [add_val, Nat.mul_two]

/-- A one-bit shift gives the same residue as doubling. -/
theorem scale_one (x : Element) : scale 1 x (by decide) (by decide) = x+x := by
  apply element_ext
  exact (scale_val 1 x (by decide) (by decide)).trans (add_self_val x).symm

/-- A two-bit shift gives the same residue as doubling twice. -/
theorem scale_two (x : Element) : scale 2 x (by decide) (by decide) = (x+x)+(x+x) := by
  apply element_ext
  rw [scale_val, add_self_val, add_self_val, Nat.mod_mul_mod, Nat.mul_assoc]
  rfl

/-- A three-bit shift gives the same residue as doubling three times. -/
theorem scale_three (x : Element) :
    scale 3 x (by decide) (by decide) = ((x+x)+(x+x))+((x+x)+(x+x)) := by
  apply element_ext
  rw [scale_val, add_self_val, add_self_val, add_self_val,
    Nat.mod_mul_mod]
  rw [Nat.mul_assoc, Nat.mod_mul_mod, Nat.mul_assoc]
  rfl

/-- Adding the halved residue to itself recovers the original residue. -/
theorem halve_add_self (a : Element) : halve a + halve a = a := by
  apply element_ext
  rw [add_val]
  change ((halveRaw a.raw).val + (halveRaw a.raw).val) % Fp.modulus = a.raw.val
  have he : (halveRaw a.raw).val + (halveRaw a.raw).val =
      a.raw.val + (a.raw.val % 2) * Fp.modulus := by
    rw [halveRaw_val]
    simp only [Fp.modulus]
    omega
  rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.lt]

private theorem fusedFinish_eq_fallback (t : Words64)
    (hlo : 2^256-Fp.modulus ≤ value (bias t)) (hhi : value (bias t) < 2*Fp.modulus+2^256) :
    fusedFinish t hlo hhi = fusedFinishFallback t hlo hhi := by
  unfold fusedFinish
  split
  · next h => exact element_ext (congrArg Raw.val (fusedFinish_raw_eq_signedFast t hlo hhi h).symm)
  · rfl

private theorem fusedFinish_val (t : Words64)
    (hlo : 2^256-Fp.modulus ≤ value (bias t)) (hhi : value (bias t) < 2*Fp.modulus+2^256) :
    ((fusedFinish t hlo hhi).raw.val + 2^256) % Fp.modulus = (value (bias t)) % Fp.modulus := by
  rw [fusedFinish_eq_fallback]
  unfold fusedFinishFallback
  split
  · rename_i hh
    dsimp only
    rw [(fusedFinish_negative t hh hlo hhi).2, Nat.add_mod_right]
  · rename_i hh
    rw [finish_val, Nat.mod_add_mod, (fusedFinish_positive t hh hhi).2]

private theorem mod_add_cancel_right {x y z m : Nat}
    (h : (x+z)%m = (y+z)%m) : x%m = y%m := by
  have hi : ((x : Int)+z) % (m : Int) = ((y : Int)+z) % (m : Int) := congrArg Int.ofNat h
  exact Int.ofNat.inj ((Int.emod_add_cancel_right (z : Int)).mp hi)

private theorem fused_scaled_residue {r t R A B q p : Nat}
    (h : (r+R)%p = t%p) (he : R*t+B = A+q*p+R*R) : (R*r+B)%p = A%p := by
  have hi : (R*(r+R))%p = (R*t)%p := by
    rw [← Nat.mul_mod_mod R (r+R) p, h, Nat.mul_mod_mod]
  apply mod_add_cancel_right (z := R*R)
  calc
    _ = (R*(r+R) + B)%p := by rw [Nat.mul_add, Nat.add_right_comm]
    _ = (R*t+B)%p := by rw [← Nat.mod_add_mod (R*(r+R)) p, hi, Nat.mod_add_mod]
    _ = (A+R*R)%p := by rw [he, Nat.add_right_comm A (q*p), Nat.add_mul_mod_self_right]

private theorem fusedFinish_productVal (t : Words64) (a b : Nat)
    (cert : (2^256-Fp.modulus ≤ value (bias t) ∧ value (bias t) < 2*Fp.modulus+2^256) ∧
      ∃ q, 2^256*value (bias t) + b = a + q*Fp.modulus + (2^256)*(2^256)) :
    (2^256 * (fusedFinish t cert.1.1 cert.1.2).raw.val + b) % Fp.modulus =
      a % Fp.modulus := by
  obtain ⟨q, h⟩ := cert.2
  exact @fused_scaled_residue (fusedFinish t cert.1.1 cert.1.2).raw.val (value (bias t))
    (2^256) a b q Fp.modulus (fusedFinish_val t cert.1.1 cert.1.2) h

private theorem productDiff_val (a b c d : Element) :
    (2^256 * (productDiff a b c d).raw.val + c.raw.val*d.raw.val) % Fp.modulus =
      a.raw.val*b.raw.val % Fp.modulus :=
  fusedFinish_productVal (scanProductDiff a.raw b.raw c.raw d.raw)
    (a.raw.val*b.raw.val) (c.raw.val*d.raw.val) (scanProductDiff_spec a b c d)

private theorem sub_scaled_residue {s u v R A B p : Nat}
    (hs : (s+v)%p = u%p) (hu : (R*u)%p = A%p) (hv : (R*v)%p = B%p) :
    (R*s+B)%p = A%p := by
  calc
    _ = (R*s+R*v)%p := by rw [← Nat.add_mod_mod _ B p, ← hv, Nat.add_mod_mod]
    _ = (R*(s+v))%p := by rw [Nat.mul_add]
    _ = (R*u)%p := by rw [← Nat.mul_mod_mod R (s+v) p, hs, Nat.mul_mod_mod]
    _ = _ := hu

set_option maxRecDepth 4000 in
/-- The fused Montgomery calculation gives the difference of the two products. -/
theorem productDiff_eq (a b c d : Element) : productDiff a b c d = a*b - c*d := by
  let p := Fp.modulus
  let R : Nat := 2^256
  let u := a*b
  let v := c*d
  let s := u-v
  have hs : (s.raw.val+v.raw.val)%p = u.raw.val%p := by
    change (((a*b-c*d).raw.val) + v.raw.val)%p = _
    rw [sub_val, Nat.mod_add_mod]
    change ((u.raw.val + p - v.raw.val) + v.raw.val)%p = _
    rw [Nat.sub_add_cancel (Nat.le_trans (Nat.le_of_lt v.lt) (Nat.le_add_left _ _)),
      Nat.add_mod_right]
  have hv : (R*v.raw.val)%p = (c.raw.val*d.raw.val)%p := mul_val c d
  have hu : (R*u.raw.val)%p = (a.raw.val*b.raw.val)%p := mul_val a b
  apply element_ext
  apply eq_of_radix_mul_mod (productDiff a b c d).lt s.lt
  apply mod_add_cancel_right (z := c.raw.val*d.raw.val)
  exact (productDiff_val a b c d).trans (sub_scaled_residue hs hu hv).symm

private theorem productSubSquare_val (a b c : Element) :
    (2^256 * (productSubSquare a b c).raw.val + c.raw.val*c.raw.val) % Fp.modulus =
      a.raw.val*b.raw.val % Fp.modulus := by
  let t := fusedSquareAccum a.raw b.raw c.raw
  have h : (2^256-Fp.modulus ≤ value (bias t) ∧
      value (bias t) < 2*Fp.modulus+2^256) ∧
    ∃ q, 2^256*value (bias t) + c.raw.val*c.raw.val =
      a.raw.val*b.raw.val + q*Fp.modulus + (2^256)*(2^256) := by
    rw [show t = fusedAccum a.raw b.raw c.raw c.raw from fusedSquareAccum_eq a.raw b.raw c.raw]
    exact fusedAccum_spec a.raw b.raw c.raw c.raw a.lt c.lt
  exact fusedFinish_productVal t (a.raw.val*b.raw.val) (c.raw.val*c.raw.val) h

/-- The fused square variant gives the product minus the square. -/
theorem productSubSquare_eq (a b c : Element) : productSubSquare a b c = a*b - square c := by
  rw [square_eq_mul, ← productDiff_eq]
  apply element_ext
  apply eq_of_radix_mul_mod (productSubSquare a b c).lt (productDiff a b c c).lt
  apply mod_add_cancel_right (z := c.raw.val*c.raw.val)
  exact (productSubSquare_val a b c).trans (productDiff_val a b c c).symm

end EthLib.Cryptography.Secp256k1.Fp.RecoveryField


namespace EthLib.Cryptography.Secp256k1.FnRecoveryWords

open Fp.RecoveryField

private theorem complement_eq : lowValue complementWords = 2^256 - Fn.modulus := by decide

private theorem raw_lt (a : Raw) : a.val < 2^256 := lowValue_lt a.words

private theorem sumWords_val (a b : Words64) :
    value (sumWords a b) = lowValue a + lowValue b := by
  let s0 := plus a.w0 b.w0 0
  let s1 := plus a.w1 b.w1 s0.hi
  let s2 := plus a.w2 b.w2 s1.hi
  let s3 := plus a.w3 b.w3 s2.hi
  have h0 : s0.lo.toNat + wordRadix*s0.hi.toNat = a.w0.toNat+b.w0.toNat :=
    (plus_spec _ _ _ (by decide)).1
  have b0 : s0.hi.toNat ≤ 1 := (plus_spec _ _ _ (by decide)).2
  obtain ⟨h1,b1⟩ := plus_spec a.w1 b.w1 s0.hi b0
  obtain ⟨h2,b2⟩ := plus_spec a.w2 b.w2 s1.hi b1
  obtain ⟨h3,_⟩ := plus_spec a.w3 b.w3 s2.hi b2
  change s1.lo.toNat + wordRadix*s1.hi.toNat = a.w1.toNat+b.w1.toNat+s0.hi.toNat at h1
  change s2.lo.toNat + wordRadix*s2.hi.toNat = a.w2.toNat+b.w2.toNat+s1.hi.toNat at h2
  change s3.lo.toNat + wordRadix*s3.hi.toNat = a.w3.toNat+b.w3.toNat+s2.hi.toNat at h3
  change value ⟨s0.lo,s1.lo,s2.lo,s3.lo,s3.hi⟩ = _
  simp only [value, lowValue, wordRadix] at h0 h1 h2 h3 ⊢
  omega

/-- The scalar encoding preserves its canonical value. -/
theorem fromFin_val (a : Fn) : (fromFin a).val = a.val := by
  exact rawOfNat_val _ (Nat.lt_trans a.isLt (by decide))

/-- Decoding words below the order preserves their value. -/
theorem toFin_val_of_lt (a : Raw) (ha : a.val < Fn.modulus) : (toFin a).val = a.val := by
  change rawToNat a % Fn.modulus = _
  rw [rawToNat_eq, Nat.mod_eq_of_lt ha]

/-- Decoding the words of a scalar recovers that scalar. -/
theorem toFin_fromFin (a : Fn) : toFin (fromFin a) = a := by
  apply Fin.ext
  rw [toFin_val_of_lt _ (by rw [fromFin_val]; exact a.isLt), fromFin_val]

private theorem raw_val_injective {a b : Raw} (h : a.val = b.val) : a = b := by
  cases a with
  | mk a0 a1 a2 a3 =>
    cases b with
    | mk b0 b1 b2 b3 =>
      have ha0 := a0.toNat_lt
      have ha1 := a1.toNat_lt
      have ha2 := a2.toNat_lt
      have ha3 := a3.toNat_lt
      have hb0 := b0.toNat_lt
      have hb1 := b1.toNat_lt
      have hb2 := b2.toNat_lt
      have hb3 := b3.toNat_lt
      simp only [Raw.val, Raw.words, lowValue, wordRadix] at h
      simp only [Raw.mk.injEq, ← UInt64.toNat_inj]
      omega

/-- Encoding preserves the four words of a canonical residue. -/
theorem fromFin_toFin_of_lt (a : Raw) (ha : a.val < Fn.modulus) : fromFin (toFin a) = a := by
  apply raw_val_injective
  rw [fromFin_val, toFin_val_of_lt _ ha]

/-- Negation maps a nonzero canonical residue to its complement in `n`. -/
theorem negate_val (a : Raw) (ha : a.val < Fn.modulus) :
    (negate a).val = if a.val = 0 then 0 else Fn.modulus - a.val := by
  unfold negate
  have z : (a.w0 == 0 && a.w1 == 0 && a.w2 == 0 && a.w3 == 0) = true ↔ a.val = 0 := by
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
    exact words_zero_iff a
  by_cases h : (a.w0 == 0 && a.w1 == 0 && a.w2 == 0 && a.w3 == 0) = true
  · have hz := z.mp h
    rw [ite_eq_left h, ite_eq_left hz, hz]
  · rw [ite_eq_right h, ite_eq_right (mt z.mpr h)]
    let d0 := minus 0xbfd25e8cd0364141 a.w0 0
    let d1 := minus 0xbaaedce6af48a03b a.w1 d0.hi
    let d2 := minus 0xfffffffffffffffe a.w2 d1.hi
    let d3 := minus 0xffffffffffffffff a.w3 d2.hi
    obtain ⟨e0,b0⟩ := minus_spec 0xbfd25e8cd0364141 a.w0 0 (by decide)
    obtain ⟨e1,b1⟩ := minus_spec 0xbaaedce6af48a03b a.w1 d0.hi b0
    obtain ⟨e2,b2⟩ := minus_spec 0xfffffffffffffffe a.w2 d1.hi b1
    obtain ⟨e3,_⟩ := minus_spec 0xffffffffffffffff a.w3 d2.hi b2
    let d : Raw := ⟨d0.lo,d1.lo,d2.lo,d3.lo⟩
    change d.val = _
    have hd := raw_lt d
    change d0.lo.toNat + a.w0.toNat+0 = (0xbfd25e8cd0364141 : UInt64).toNat +
      wordRadix*d0.hi.toNat at e0
    change d1.lo.toNat + a.w1.toNat+d0.hi.toNat =
      (0xbaaedce6af48a03b : UInt64).toNat + wordRadix*d1.hi.toNat at e1
    change d2.lo.toNat + a.w2.toNat+d1.hi.toNat =
      (0xfffffffffffffffe : UInt64).toNat + wordRadix*d2.hi.toNat at e2
    change d3.lo.toNat + a.w3.toNat+d2.hi.toNat =
      (0xffffffffffffffff : UInt64).toNat + wordRadix*d3.hi.toNat at e3
    have e : d.val + a.val = Fn.modulus + 2^256*d3.hi.toNat := by
      simp only [d, Raw.val, Raw.words, lowValue, order_eq, wordRadix,
        UInt64.toNat_ofNat] at e0 e1 e2 e3 ⊢
      omega
    omega

private theorem fromWords_low (w : Words64) : (Raw.fromWords w).val = lowValue w := rfl

private theorem reduceOrder_yes (t : Words64) (h : Fn.modulus ≤ value t)
    (ht : value t < 2*Fn.modulus) :
    (Raw.fromWords (sumWords t complementWords)).val = value t % Fn.modulus := by
  rw [fromWords_low]
  rw [value_as_nat t] at h ht ⊢
  have he := (value_as_nat (sumWords t complementWords)).symm.trans
    (sumWords_val t complementWords)
  have hc : Fn.modulus + lowValue complementWords = 2^256 := by
    rw [complement_eq]
    exact Nat.add_sub_of_le (by decide)
  exact reduction_from_add hc (lowValue_lt _) he h ht

private theorem reduceOrder_no (t : Words64) (hlt : value t < Fn.modulus) :
    (Raw.fromWords t).val = value t % Fn.modulus := by
  have htop : t.top = 0 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_zero]
    change lowValue t + 2^256*t.top.toNat < Fn.modulus at hlt
    rw [order_eq] at hlt
    omega
  exact (Raw.fromWords_val t htop).trans (Nat.mod_eq_of_lt hlt).symm

private theorem reduceOrder_val (t : Words64) (ht : value t < 2*Fn.modulus) :
    (reduceOrder t).val = value t % Fn.modulus :=
  ite_predicate (fun w : Raw => w.val = value t % Fn.modulus)
    (geOrder t) (Raw.fromWords (sumWords t complementWords)) (Raw.fromWords t)
    (fun h => reduceOrder_yes t ((geOrder_iff t).mp h) ht)
    (fun h => reduceOrder_no t (Nat.lt_of_not_ge (mt (geOrder_iff t).mpr h)))

private theorem fold_complement_value :
    2^256 - Fn.modulus = 0x14551231950b75fc4402da1732fc9bebf := by decide

private theorem foldWords_val (lo hi : Words64) :
    lowValue (foldWords lo hi).1 + 2^256*lowValue (foldWords lo hi).2 =
      lowValue lo + (2^256-Fn.modulus)*lowValue hi := by
  let p := multiplyColumns hi complementWords
  let s := sumWords lo p.1
  let t := addLow (.fromWords p.2) s.top
  have ep : lowValue p.1 + 2^256*lowValue p.2 = lowValue hi * (2^256-Fn.modulus) := by
    rw [← complement_eq]
    exact multiplyColumns_spec hi complementWords
  have es : value s = lowValue lo + lowValue p.1 := sumWords_val lo p.1
  have et : value t = lowValue p.2 + s.top.toNat := addLow_val (.fromWords p.2) s.top
  have es' : value s = lowValue s + 2^256*s.top.toNat := rfl
  have et' : value t = lowValue t + 2^256*t.top.toNat := rfl
  have hlo : lowValue lo < 2^256 := lowValue_lt lo
  have hhi : lowValue hi < 2^256 := lowValue_lt hi
  change lowValue s + 2^256*lowValue t = _
  rw [fold_complement_value] at ep ⊢
  omega

private theorem fold_mod (l h : Nat) :
    (l + (2^256-Fn.modulus)*h) % Fn.modulus = (l + 2^256*h) % Fn.modulus := by
  have hc : Fn.modulus ≤ 2^256 := by decide
  have e : l + (2^256-Fn.modulus)*h + Fn.modulus*h = l+2^256*h := by
    rw [Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel hc]
  rw [← e, Nat.add_mul_mod_self_left]

private theorem lastFold_val (k : UInt64) (hk : k.toNat ≤ 2) :
    let w0 := wordProduct k 0x402da1732fc9bebf
    let w1 := mac k 0x4551231950b75fc4 0 w0.hi
    lowValue ⟨w0.lo,w1.lo,k+w1.hi,0,0⟩ = (2^256-Fn.modulus)*k.toNat := by
  let w0 := wordProduct k 0x402da1732fc9bebf
  let w1 := mac k 0x4551231950b75fc4 0 w0.hi
  have h0 := wordProduct_value k 0x402da1732fc9bebf
  have h1 := mac_spec k 0x4551231950b75fc4 0 w0.hi
  change w0.lo.toNat + wordRadix*w0.hi.toNat = k.toNat*(0x402da1732fc9bebf : UInt64).toNat at h0
  change w1.lo.toNat + 2^64*w1.hi.toNat = k.toNat*(0x4551231950b75fc4 : UInt64).toNat +
    0 + w0.hi.toNat at h1
  have hb := w0.hi.toNat_lt
  have hsum : (k+w1.hi).toNat = k.toNat+w1.hi.toNat := by
    apply add_exact
    simp only [UInt64.toNat_ofNat] at h1
    omega
  change w0.lo.toNat + 2^64*w1.lo.toNat + 2^128*(k+w1.hi).toNat + 2^192*0 = _
  rw [hsum, fold_complement_value]
  simp only [UInt64.toNat_ofNat, wordRadix] at h0 h1
  omega

/-- The word product gives the scalar field remainder for any four-word inputs. -/
theorem mul_val (a b : Raw) : (mul a b).val = (a.val*b.val) % Fn.modulus := by
  let p := multiplyColumns a.words b.words
  let v := foldWords p.1 p.2
  let t := foldWords v.1 v.2
  have ep : lowValue p.1 + 2^256*lowValue p.2 = a.val*b.val :=
    multiplyColumns_spec a.words b.words
  have ev : lowValue v.1 + 2^256*lowValue v.2 =
      lowValue p.1 + (2^256-Fn.modulus)*lowValue p.2 := foldWords_val p.1 p.2
  have hl : lowValue p.1 < 2^256 := lowValue_lt _
  have hh : lowValue p.2 < 2^256 := lowValue_lt _
  have hv : lowValue v.2 ≤ 2^256-Fn.modulus := by
    rw [fold_complement_value] at ev ⊢
    omega
  have et : lowValue t.1 + 2^256*lowValue t.2 =
      lowValue v.1 + (2^256-Fn.modulus)*lowValue v.2 := foldWords_val v.1 v.2
  have qt : lowValue t.2 ≤ 2 := by
    have hvl : lowValue v.1 < 2^256 := lowValue_lt _
    have hprod := Nat.mul_le_mul_left (2^256-Fn.modulus) hv
    rw [fold_complement_value] at et hprod
    omega
  let k := t.2.w0
  have ek : k.toNat = lowValue t.2 := by
    change k.toNat + wordRadix*t.2.w1.toNat + wordRadix^2*t.2.w2.toNat +
      wordRadix^3*t.2.w3.toNat ≤ 2 at qt
    change k.toNat = k.toNat + wordRadix*t.2.w1.toNat + wordRadix^2*t.2.w2.toNat +
      wordRadix^3*t.2.w3.toNat
    simp only [wordRadix] at qt ⊢
    omega
  let w0 := wordProduct k 0x402da1732fc9bebf
  let w1 := mac k 0x4551231950b75fc4 0 w0.hi
  let s := sumWords t.1 ⟨w0.lo,w1.lo,k+w1.hi,0,0⟩
  have es : value s = lowValue t.1 + (2^256-Fn.modulus)*lowValue t.2 := by
    change value (sumWords t.1 ⟨w0.lo,w1.lo,k+w1.hi,0,0⟩) = _
    rw [sumWords_val]
    have el : lowValue ⟨w0.lo,w1.lo,k+w1.hi,0,0⟩ = (2^256-Fn.modulus)*k.toNat :=
      lastFold_val k (ek ▸ qt)
    rw [el, ek]
  have hs : value s < 2*Fn.modulus := by
    have htl : lowValue t.1 < 2^256 := lowValue_lt _
    rw [fold_complement_value] at es
    rw [order_eq]
    omega
  change (reduceOrder s).val = _
  rw [reduceOrder_val _ hs, es, fold_mod, et, fold_mod, ev, fold_mod, ep]

end EthLib.Cryptography.Secp256k1.FnRecoveryWords

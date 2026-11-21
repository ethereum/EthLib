module

public import EthLib.Cryptography.Secp256k1.Montgomery
import all EthLib.Cryptography.Secp256k1.Montgomery
public import EthLib.Cryptography.Montgomery.Fin
import all EthLib.Cryptography.Montgomery.Fin
import all EthLib.Cryptography.Montgomery
public import EthLib.Cryptography.Proofs.Montgomery.Core
public import EthLib.Cryptography.Proofs.Montgomery.Fin

/-!
# Proofs: the Montgomery form of the secp256k1 base field

The four words hold the same residue as the shared Montgomery field on eight 32-bit limbs.

So reading back into `Fp` keeps zero, one, sums, differences and products, and it is injective.

Its specialized square, shifts and fused operations give the corresponding field operations.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

/-- The Montgomery constants of `p` on eight 32-bit limbs, with radix `R = 2^256`.

The four words are proved against the shared Montgomery field on these limbs. -/
def Fp.params : Cryptography.Montgomery.Modulus 8 where
  p := Fp.modulus
  pLimbs := ⟨0xfffffc2f, 0xfffffffe, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff⟩
  r1 := ⟨0x3d1, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0⟩
  r2 := ⟨0xe90a1, 0x7a2, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0⟩
  pm2 := ⟨0xfffffc2d, 0xfffffffe, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff⟩
  pinv := 0xd2253531
  pLimbs_spec := by decide
  pinv_spec := by decide
  r1_spec := by decide
  r2_spec := by decide
  pm2_spec := by decide

end EthLib.Cryptography.Secp256k1

namespace EthLib.Cryptography.Secp256k1.Montgomery

open EthLib.Cryptography.Montgomery (Limbs)

/-- One word from two 32-bit limbs, the low one first. -/
def join (lo hi : UInt32) : UInt64 :=
  lo.toUInt64 ||| (hi.toUInt64 <<< 32)

/-- Four words from eight 32-bit limbs, with a zero carry word. -/
def wide (a : Cryptography.Montgomery.Limbs8) : Words64 :=
  ⟨join a.l0 a.l1, join a.l2 a.l3, join a.l4 a.l5, join a.l6 a.l7, 0⟩

/-- Eight 32-bit limbs from the four low words. -/
def narrow (p : Words64) : Cryptography.Montgomery.Limbs8 :=
  ⟨p.w0.toUInt32, (p.w0 >>> 32).toUInt32,
    p.w1.toUInt32, (p.w1 >>> 32).toUInt32,
    p.w2.toUInt32, (p.w2 >>> 32).toUInt32,
    p.w3.toUInt32, (p.w3 >>> 32).toUInt32⟩


private theorem join_value (lo hi : UInt32) : (join lo hi).toNat = lo.toNat + 2^32*hi.toNat := by
  have hhi : hi.toNat * 2^32 < 2^64 := Nat.mul_lt_mul_of_pos_right hi.toNat_lt (by decide)
  unfold join
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  change lo.toNat ||| (hi.toNat <<< 32) % 2^64 = _
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hhi, Nat.mul_comm hi.toNat, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt lo.toNat_lt, Nat.add_comm]

private theorem split_value (w : UInt64) :
    w.toUInt32.toNat + 2^32*(w >>> 32).toUInt32.toNat = w.toNat := by
  rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]
  change w.toNat % 2^32 + 2^32*(w.toNat / 2^32 % 2^32) = w.toNat
  have h : w.toNat / 2^32 < 2^32 := Nat.div_lt_of_lt_mul w.toNat_lt
  rw [Nat.mod_eq_of_lt h, Nat.mod_add_div]

private theorem limbs8_value (a : Cryptography.Montgomery.Limbs8) :
    Limbs.val (n := 8) a = a.l0.toNat + 2^32*a.l1.toNat + 2^64*a.l2.toNat +
      2^96*a.l3.toNat + 2^128*a.l4.toNat + 2^160*a.l5.toNat +
      2^192*a.l6.toNat + 2^224*a.l7.toNat := by
  change a.l0.toNat + 2^32*(a.l1.toNat + 2^32*(a.l2.toNat + 2^32*(a.l3.toNat +
    2^32*(a.l4.toNat + 2^32*(a.l5.toNat + 2^32*(a.l6.toNat + 2^32*(a.l7.toNat + 2^32*0))))))) = _
  omega

private theorem value_wide (a : Cryptography.Montgomery.Limbs8) :
    value (wide a) = Limbs.val (n := 8) a := by
  simp only [value, lowValue, wide, join_value, limbs8_value, UInt64.toNat_zero,
    Nat.mul_zero, Nat.add_zero, wordRadix]
  omega

private theorem val_narrow (w : Words64) (h : w.top = 0) :
    Limbs.val (n := 8) (narrow w) = value w := by
  have h0 := split_value w.w0
  have h1 := split_value w.w1
  have h2 := split_value w.w2
  have h3 := split_value w.w3
  simp only [limbs8_value, narrow, value, lowValue, h, UInt64.toNat_zero,
    Nat.mul_zero, Nat.add_zero, wordRadix]
  omega





/-- The shared Montgomery field on eight 32-bit limbs, at the constants of `p`. -/
abbrev Shared := Cryptography.Montgomery Fp.params

/-- The same Montgomery residue on the eight limbs of the shared field. -/
def toMont (a : Montgomery) : Shared :=
  ⟨narrow a.raw.words, by rw [val_narrow _ rfl, ← a.raw.val_eq]; exact a.lt⟩

/-- The same Montgomery residue on four words. -/
def ofMont (a : Shared) : Montgomery :=
  ⟨Raw.fromWords (wide a.limbs), by
    rw [Raw.fromWords_val _ rfl, value_wide]
    exact a.lt⟩


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

private theorem Raw.words_fromWords (w : Words64) (h : w.top = 0) :
    (Raw.fromWords w).words = w := by
  cases w
  cases h
  rfl

/-- Four words represent a value smaller than `2^256`. -/
theorem rawToNat_lt (w : Raw) : rawToNat w < 2^256 := by
  rw [rawToNat_eq]
  exact lowValue_lt w.words

private theorem toMont_val (a : Montgomery) : Limbs.val (n := 8) (toMont a).limbs = a.raw.val := by
  exact (val_narrow _ rfl).trans a.raw.val_eq.symm

private theorem ofMont_val (a : Shared) : (ofMont a).raw.val = Limbs.val (n := 8) a.limbs :=
  (Raw.fromWords_val _ rfl).trans (value_wide _)

private theorem mont_ext {a b : Shared} (h : Limbs.val (n := 8) a.limbs =
    Limbs.val (n := 8) b.limbs) : a = b := by
  have h := Limbs.val_injective (n := 8) h
  cases a
  cases b
  cases h
  rfl

/-- A change of limb packing preserves the original Montgomery residue. -/
theorem toMont_ofMont (a : Shared) : toMont (ofMont a) = a :=
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
  have h := congrArg (fun z : Shared => wide z.limbs) h
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
theorem toMont_zero : toMont (0 : Montgomery) = 0 := mont_ext (by decide)

/-- One has the same residue in either representation. -/
theorem toMont_one : toMont (1 : Montgomery) = 1 := mont_ext (by decide)

private theorem finish_val (t : Words64) (ht : value t < 2*Fp.modulus) :
    (finish t ht).raw.val = value t % Fp.modulus := by
  have hu := reduceFast_spec t ht
  exact (Raw.fromWords_val (reduceFast t) hu.1).trans hu.2

private theorem scaled_residue (x y v : Nat)
    (h : (2^256 * v) % Fp.modulus = x*y % Fp.modulus) :
    (2^256 * (v % Fp.modulus)) % Fp.modulus = x*y % Fp.modulus :=
  (Nat.mul_mod_mod _ _ _).trans h

private theorem mul_val (a b : Montgomery) :
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
theorem square_eq_mul (a : Montgomery) : square a = a * a := by
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
theorem toMont_mul (a b : Montgomery) : toMont (a*b) = toMont a * toMont b := by
  let x := toMont a
  let y := toMont b
  have hspec := (Cryptography.Montgomery.mulLimbs_spec Fp.params x.limbs x.lt y.limbs).2
  have hEq : Limbs.val (n := 8) (x*y).limbs =
      Limbs.val (n := 8) (Cryptography.Montgomery.mulWords (Limbs.get Fp.params.pLimbs)
        Fp.params.pinv (Limbs.get x.limbs) (Limbs.get y.limbs) Limbs.pack) := by
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

private theorem toMont_readRaw (a : Fp) :
    (toMont (readRaw a)).limbs = Limbs.ofNat a.val := by
  apply Limbs.val_injective
  rw [toMont_val, Limbs.val_ofNat]
  change (rawOfNat a.val).val = a.val % 2^256
  have h : a.val < 2^256 := Nat.lt_trans a.isLt (by decide)
  rw [rawOfNat_val _ h, Nat.mod_eq_of_lt h]

/-- Both field implementations encode a canonical integer the same way. -/
theorem toMont_ofFin (a : Fp) : toMont (ofFin a) = Cryptography.Montgomery.ofFin a := by
  have h : toMont montgomerySquare = ⟨Fp.params.r2, Fp.params.r2_lt⟩ := by
    apply mont_ext
    decide
  simp only [ofFin, toMont_mul, h]
  change Cryptography.Montgomery.mulLimbs Fp.params Fp.params.r2 Fp.params.r2_lt
    (toMont (readRaw a)).limbs =
      Cryptography.Montgomery.mulLimbs Fp.params Fp.params.r2 Fp.params.r2_lt
        (Limbs.ofNat (a.val % Fp.modulus))
  rw [Nat.mod_eq_of_lt a.isLt, toMont_readRaw]

/-- Leaving either Montgomery representation gives the same field element. -/
theorem toFin_eq (a : Montgomery) : toFin a = Cryptography.Montgomery.toFin (toMont a) := by
  apply Fin.ext
  change rawToNat (a * rawOne).raw = (toMont a).toNat
  rw [rawToNat_eq, ← toMont_val, toMont_mul, Cryptography.Montgomery.toNat_eq_val]
  have h : (toMont rawOne).limbs = Limbs.ofNat (n := 8) 1 := by decide
  exact congrArg (fun limbs =>
    Limbs.val
      (Cryptography.Montgomery.mulLimbs Fp.params (toMont a).limbs (toMont a).lt limbs).limbs) h

private theorem add_val (a b : Montgomery) :
    (a+b).raw.val = (a.raw.val + b.raw.val) % Fp.modulus := by
  let u := add64 reduceFast a.raw.words b.raw.words
  have hu := add64_spec reduceFast reduceFast_spec a.raw.words b.raw.words rfl rfl
    (a.raw.val_eq ▸ a.lt) (b.raw.val_eq ▸ b.lt)
  change (Raw.fromWords u).val = _
  rw [Raw.fromWords_val u hu.1, hu.2, ← a.raw.val_eq, ← b.raw.val_eq]

private theorem sub_val (a b : Montgomery) : (a-b).raw.val =
    (a.raw.val + Fp.modulus - b.raw.val) % Fp.modulus := by
  let u := subMasked a.raw.words b.raw.words
  have hu := subMasked_spec a.raw.words b.raw.words rfl rfl
    (a.raw.val_eq ▸ a.lt) (b.raw.val_eq ▸ b.lt)
  change (Raw.fromWords u).val = _
  rw [Raw.fromWords_val u hu.1, hu.2, ← a.raw.val_eq, ← b.raw.val_eq]

/-- Addition gives the same Montgomery residue in either representation. -/
theorem toMont_add (a b : Montgomery) : toMont (a+b) = toMont a + toMont b := by
  apply mont_ext
  let x := toMont a
  let y := toMont b
  have h := Cryptography.Montgomery.addLimbs_spec Fp.params x.limbs y.limbs x.lt y.lt
  change Limbs.val (n := 8) (toMont (a+b)).limbs =
    Limbs.val (n := 8) (Cryptography.Montgomery.addCore (n := 8) x.limbs y.limbs Fp.params.pLimbs)
  rw [toMont_val, add_val]
  unfold Cryptography.Montgomery.addCore
  rw [h, toMont_val, toMont_val]
  rfl

/-- Subtraction gives the same Montgomery residue in either representation. -/
theorem toMont_sub (a b : Montgomery) : toMont (a-b) = toMont a - toMont b := by
  apply mont_ext
  let x := toMont a
  let y := toMont b
  change Limbs.val (n := 8) (toMont (a-b)).limbs =
    Limbs.val (n := 8) (Cryptography.Montgomery.subLimbs Fp.params x.limbs y.limbs)
  rw [Cryptography.Montgomery.subLimbs_spec Fp.params x.lt y.lt, toMont_val, sub_val]
  rw [toMont_val, toMont_val]
  rfl

private theorem element_ext {a b : Montgomery} (h : a.raw.val = b.raw.val) : a = b :=
  toMont_injective (mont_ext ((toMont_val a).trans (h.trans (toMont_val b).symm)))

private theorem add_self_val (x : Montgomery) : (x+x).raw.val = x.raw.val * 2 % Fp.modulus := by
  rw [add_val, Nat.mul_two]

/-- Adding the halved residue to itself recovers the original residue. -/
theorem halve_add_self (a : Montgomery) : halve a + halve a = a := by
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

private theorem productDiff_val (a b c d : Montgomery) :
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

/-- The fused Montgomery calculation gives the difference of the two products. -/
theorem productDiff_eq (a b c d : Montgomery) : productDiff a b c d = a*b - c*d := by
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

/-- The fused square variant gives the product minus the square. -/
theorem productSubSquare_eq (a b c : Montgomery) : productSubSquare a b c = a*b - square c := by
  rw [square_eq_mul, ← productDiff_eq]
  rfl

/-! ## The field read back

Reading an element back into `Fp` keeps zero, one, sums, differences and products.

Distinct elements read back to distinct elements.
-/

theorem toFin_zero : toFin (0 : Montgomery) = 0 := by
  rw [toFin_eq, toMont_zero, Cryptography.Montgomery.toFin_zero]
  rfl

theorem toFin_one : toFin (1 : Montgomery) = 1 := by
  rw [toFin_eq, toMont_one, Cryptography.Montgomery.toFin_one]
  rfl

theorem toFin_add (a b : Montgomery) : toFin (a + b) = toFin a + toFin b := by
  rw [toFin_eq, toFin_eq, toFin_eq, toMont_add, Cryptography.Montgomery.toFin_add]
  rfl

theorem toFin_sub (a b : Montgomery) : toFin (a - b) = toFin a - toFin b := by
  rw [toFin_eq, toFin_eq, toFin_eq, toMont_sub, Cryptography.Montgomery.toFin_sub]
  rfl

theorem toFin_mul (a b : Montgomery) : toFin (a * b) = toFin a * toFin b := by
  rw [toFin_eq, toFin_eq, toFin_eq, toMont_mul, Cryptography.Montgomery.toFin_mul]
  rfl

theorem toFin_square (a : Montgomery) : toFin (square a) = toFin a * toFin a := by
  rw [square_eq_mul, toFin_mul]

theorem toFin_injective : Function.Injective toFin := by
  intro a b h
  rw [toFin_eq, toFin_eq] at h
  exact toMont_injective (Cryptography.Montgomery.toFin_injective h)

/-- Entering the Montgomery form and reading back gives the element itself. -/
@[simp] theorem toFin_ofFin (a : Fp) : toFin (ofFin a) = a :=
  (toFin_eq _).trans ((congrArg Cryptography.Montgomery.toFin (toMont_ofFin a)).trans
    (Cryptography.Montgomery.toFin_ofFin (M := Fp.params) a))

/-- Reading back and entering the Montgomery form again gives the same element. -/
theorem ofFin_toFin (a : Montgomery) : ofFin (toFin a) = a :=
  toFin_injective (toFin_ofFin _)

end EthLib.Cryptography.Secp256k1.Montgomery

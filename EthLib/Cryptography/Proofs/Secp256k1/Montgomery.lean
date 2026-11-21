module

public import EthLib.Cryptography.Secp256k1.Montgomery
import all EthLib.Cryptography.Secp256k1.Montgomery
public import EthLib.Cryptography.Montgomery.Fin
import all EthLib.Cryptography.Montgomery.Fin
import all EthLib.Cryptography.Montgomery
public import EthLib.Cryptography.Proofs.Montgomery.Core
public import EthLib.Cryptography.Proofs.Montgomery.Fin
public import EthLib.Cryptography.Proofs.Word64

/-!
# Proofs: the Montgomery form of the secp256k1 base field

The four words hold the same residue as the shared Montgomery field on eight 32-bit limbs.

So reading back into `Fp` keeps zero, one, sums, differences and products, and it is injective.

Its specialized square, shifts and fused operations give the corresponding field operations.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

open EthLib.Cryptography.Word64

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

open EthLib.Cryptography.Word64

open EthLib.Cryptography.Montgomery (Limbs)

/-- Four words represent a value smaller than `2^256`. -/
theorem rawToNat_lt (w : Raw) : rawToNat w < 2^256 := by
  rw [rawToNat_eq]
  exact lowValue_lt w.words

private theorem finish_val (t : Words64) (ht : value t < 2*Fp.modulus) :
    (finish t ht).raw.val = value t % Fp.modulus := by
  have hu := reduceFast_spec t ht
  exact (Raw.fromWords_val (reduceFast t) hu.1).trans hu.2

private theorem scaled_residue (x y v : Nat)
    (h : (2^256 * v) % Fp.modulus = x*y % Fp.modulus) :
    (2^256 * (v % Fp.modulus)) % Fp.modulus = x*y % Fp.modulus :=
  (Nat.mul_mod_mod _ _ _).trans h

/-- The product on four words holds the product divided by `R = 2^256`, mod `p`. -/
theorem mul_val_words (a b : Montgomery) :
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

/-- The laws of the sum, the difference and the product, and the constants of `p` on eight limbs. -/
instance : Word64.Montgomery.Laws Fp.modulus where
  params := Fp.params
  params_p := rfl
  add_val a b := by
    let u := add64 reduceFast a.raw.words b.raw.words
    have hu := add64_spec reduceFast reduceFast_spec a.raw.words b.raw.words rfl rfl
      (a.raw.val_eq ▸ a.lt) (b.raw.val_eq ▸ b.lt)
    rw [show (a + b).raw = Raw.fromWords u by simp only [HAdd.hAdd, Add.add, add]; rfl]
    rw [Raw.fromWords_val u hu.1, hu.2, ← a.raw.val_eq, ← b.raw.val_eq]
  sub_val a b := by
    let u := subMasked a.raw.words b.raw.words
    have hu := subMasked_spec a.raw.words b.raw.words rfl rfl
      (a.raw.val_eq ▸ a.lt) (b.raw.val_eq ▸ b.lt)
    rw [show (a - b).raw = Raw.fromWords u by simp only [HSub.hSub, Sub.sub, sub]; rfl]
    rw [Raw.fromWords_val u hu.1, hu.2, ← a.raw.val_eq, ← b.raw.val_eq]
  mul_val := mul_val_words

/-- The shared Montgomery field on eight 32-bit limbs, at the constants of `p`. -/
abbrev Shared := Cryptography.Montgomery Fp.params

/-- The same Montgomery residue on the eight limbs of the shared field. -/
abbrev toMont (a : Montgomery) : Shared := Word64.Montgomery.toMont a

/-- The same Montgomery residue on four words. -/
def ofMont (a : Shared) : Montgomery :=
  ⟨Raw.fromWords (wide a.limbs), by
    rw [Raw.fromWords_val _ rfl, value_wide]
    exact a.lt⟩

/-- A change of limb packing preserves the original Montgomery residue. -/
theorem toMont_ofMont (a : Shared) : toMont (ofMont a) = a :=
  Word64.Montgomery.mont_ext ((Word64.Montgomery.toMont_val (ofMont a)).trans
    ((Raw.fromWords_val _ rfl).trans (value_wide _)))

/-- Canonical residues have an injective representation in the general field. -/
theorem toMont_injective : Function.Injective toMont := Word64.Montgomery.toMont_injective

/-- Zero has the same residue in either representation. -/
theorem toMont_zero : toMont (0 : Montgomery) = 0 := Word64.Montgomery.toMont_zero

/-- One has the same residue in either representation. -/
theorem toMont_one : toMont (1 : Montgomery) = 1 := Word64.Montgomery.toMont_one

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
  have he : (square a).raw.val = (a*a).raw.val := Word64.Montgomery.eq_of_radix_mul_mod
    (square a).lt (a*a).lt (hs.trans (mul_val_words a a).symm)
  exact Word64.Montgomery.element_ext he

/-- Multiplication gives the same Montgomery residue in either representation. -/
theorem toMont_mul (a b : Montgomery) : toMont (a*b) = toMont a * toMont b :=
  Word64.Montgomery.toMont_mul a b

/-- Both field implementations encode a canonical integer the same way. -/
theorem toMont_ofFin (a : Fp) : toMont (ofFin a) = Cryptography.Montgomery.ofFin a :=
  Word64.Montgomery.toMont_ofFin a

/-- Leaving either Montgomery representation gives the same field element. -/
theorem toFin_eq (a : Montgomery) : toFin a = Cryptography.Montgomery.toFin (toMont a) :=
  Fin.ext (Word64.Montgomery.toFin_val_eq a)

/-- Addition gives the same Montgomery residue in either representation. -/
theorem toMont_add (a b : Montgomery) : toMont (a+b) = toMont a + toMont b :=
  Word64.Montgomery.toMont_add a b

/-- Subtraction gives the same Montgomery residue in either representation. -/
theorem toMont_sub (a b : Montgomery) : toMont (a-b) = toMont a - toMont b :=
  Word64.Montgomery.toMont_sub a b

/-- Adding the halved residue to itself recovers the original residue. -/
theorem halve_add_self (a : Montgomery) : halve a + halve a = a := by
  apply Word64.Montgomery.element_ext
  rw [Word64.Montgomery.Laws.add_val]
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
  · next h =>
    exact Word64.Montgomery.element_ext
      (congrArg Raw.val (fusedFinish_raw_eq_signedFast t hlo hhi h).symm)
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
    rw [Word64.Montgomery.Laws.sub_val, Nat.mod_add_mod]
    change ((u.raw.val + p - v.raw.val) + v.raw.val)%p = _
    rw [Nat.sub_add_cancel (Nat.le_trans (Nat.le_of_lt v.lt) (Nat.le_add_left _ _)),
      Nat.add_mod_right]
  have hv : (R*v.raw.val)%p = (c.raw.val*d.raw.val)%p := mul_val_words c d
  have hu : (R*u.raw.val)%p = (a.raw.val*b.raw.val)%p := mul_val_words a b
  apply Word64.Montgomery.element_ext
  apply Word64.Montgomery.eq_of_radix_mul_mod (productDiff a b c d).lt s.lt
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

theorem toFin_zero : toFin (0 : Montgomery) = 0 := Word64.Montgomery.toFin_zero

theorem toFin_one : toFin (1 : Montgomery) = 1 := Word64.Montgomery.toFin_one

theorem toFin_add (a b : Montgomery) : toFin (a + b) = toFin a + toFin b :=
  Word64.Montgomery.toFin_add a b

theorem toFin_sub (a b : Montgomery) : toFin (a - b) = toFin a - toFin b :=
  Word64.Montgomery.toFin_sub a b

theorem toFin_mul (a b : Montgomery) : toFin (a * b) = toFin a * toFin b :=
  Word64.Montgomery.toFin_mul a b

theorem toFin_square (a : Montgomery) : toFin (square a) = toFin a * toFin a := by
  rw [square_eq_mul, toFin_mul]

theorem toFin_injective : Function.Injective toFin := Word64.Montgomery.toFin_injective

/-- Entering the Montgomery form and reading back gives the element itself. -/
@[simp] theorem toFin_ofFin (a : Fp) : toFin (ofFin a) = a := Word64.Montgomery.toFin_ofFin a

/-- Reading back and entering the Montgomery form again gives the same element. -/
theorem ofFin_toFin (a : Montgomery) : ofFin (toFin a) = a := Word64.Montgomery.ofFin_toFin a

end EthLib.Cryptography.Secp256k1.Montgomery

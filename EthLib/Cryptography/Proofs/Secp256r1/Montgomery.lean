module

public import EthLib.Cryptography.Secp256r1.Montgomery
public import EthLib.Cryptography.Montgomery.Fin
import all EthLib.Cryptography.Montgomery.Fin
import all EthLib.Cryptography.Montgomery
public import EthLib.Cryptography.Proofs.Montgomery.Core
public import EthLib.Cryptography.Proofs.Montgomery.Fin
public import EthLib.Cryptography.Proofs.Word64
public import EthLib.Cryptography.Proofs.Jacobian

/-!
# Proofs: the Montgomery form of the secp256r1 base field

The four words hold the same residue as the shared Montgomery field on eight 32-bit limbs.

So reading back into `Fp` keeps zero, one, sums, differences and products, and it is injective.

It undoes the encoding, and the inverse reads back as the inverse of `Fp`.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

/-- The Montgomery constants of `p` on eight 32-bit limbs, with radix `R = 2^256`.

The four words are proved against the shared Montgomery field on these limbs. -/
def Fp.params : Cryptography.Montgomery.Modulus 8 where
  p := Fp.modulus
  pLimbs := ⟨0xffffffff, 0xffffffff, 0xffffffff, 0x0, 0x0, 0x0, 0x1, 0xffffffff⟩
  r1 := ⟨0x1, 0x0, 0x0, 0xffffffff, 0xffffffff, 0xffffffff, 0xfffffffe, 0x0⟩
  r2 := ⟨0x3, 0x0, 0xffffffff, 0xfffffffb, 0xfffffffe, 0xffffffff, 0xfffffffd, 0x4⟩
  pm2 := ⟨0xfffffffd, 0xffffffff, 0xffffffff, 0x0, 0x0, 0x0, 0x1, 0xffffffff⟩
  pinv := 1
  pLimbs_spec := by decide
  pinv_spec := by decide
  r1_spec := by decide
  r2_spec := by decide
  pm2_spec := by decide

end EthLib.Cryptography.Secp256r1

namespace EthLib.Cryptography.Secp256r1.Montgomery

open EthLib.Cryptography.Word64

/-- The laws of the sum, the difference and the product, and the constants of `p` on eight limbs. -/
instance : Word64.Montgomery.Laws Fp.modulus where
  params := Fp.params
  params_p := rfl
  add_val a b := by
    rw [show (a + b).raw = addRaw a.raw b.raw by simp only [HAdd.hAdd, Add.add, add]]
    exact addRaw_val _ _ a.lt b.lt
  sub_val a b := by
    rw [show (a - b).raw = subRaw a.raw b.raw by simp only [HSub.hSub, Sub.sub, sub]]
    rw [subRaw_val _ _ a.lt b.lt, Nat.add_sub_assoc b.lt.le]
  mul_val a b := by
    have h := mulAcc_spec a.raw b.raw a.lt
    obtain ⟨m, hm⟩ := h.2
    rw [show (a * b).raw = reduceOnce (mulAcc a.raw b.raw) by
      simp only [HMul.hMul, Mul.mul, mul]]
    rw [reduceOnce_val _ h.1, Nat.mul_mod_mod, hm, Nat.add_mul_mod_self_right]

/-- The shared Montgomery field on eight 32-bit limbs, at the constants of `p`. -/
abbrev Shared := Cryptography.Montgomery Fp.params

/-- The same Montgomery residue on the eight limbs of the shared field. -/
abbrev toMont (a : Montgomery) : Shared := Word64.Montgomery.toMont a

/-- Distinct residues stay distinct on the shared limbs. -/
theorem toMont_injective : Function.Injective toMont := Word64.Montgomery.toMont_injective

/-- Zero has the same residue in either representation. -/
theorem toMont_zero : toMont (0 : Montgomery) = 0 := Word64.Montgomery.toMont_zero

/-- One has the same residue in either representation. -/
theorem toMont_one : toMont (1 : Montgomery) = 1 := Word64.Montgomery.toMont_one

/-- Addition gives the same Montgomery residue in either representation. -/
theorem toMont_add (a b : Montgomery) : toMont (a + b) = toMont a + toMont b :=
  Word64.Montgomery.toMont_add a b

/-- Subtraction gives the same Montgomery residue in either representation. -/
theorem toMont_sub (a b : Montgomery) : toMont (a - b) = toMont a - toMont b :=
  Word64.Montgomery.toMont_sub a b

/-- Multiplication gives the same Montgomery residue in either representation. -/
theorem toMont_mul (a b : Montgomery) : toMont (a * b) = toMont a * toMont b :=
  Word64.Montgomery.toMont_mul a b

/-- Both field implementations encode a canonical integer the same way. -/
theorem toMont_ofFin (a : Fp) : toMont (ofFin a) = Cryptography.Montgomery.ofFin a :=
  Word64.Montgomery.toMont_ofFin a

/-- Leaving either Montgomery representation gives the same field element. -/
theorem toFin_eq (a : Montgomery) : toFin a = Cryptography.Montgomery.toFin (toMont a) :=
  Fin.ext (Word64.Montgomery.toFin_val_eq a)

/-! ## The field read back

Reading an element back into `Fp` keeps zero, one, sums, differences and products.

Distinct elements read back to distinct elements.
-/

/-- Zero reads back as zero. -/
theorem toFin_zero : toFin (0 : Montgomery) = 0 := Word64.Montgomery.toFin_zero

/-- One reads back as one. -/
theorem toFin_one : toFin (1 : Montgomery) = 1 := Word64.Montgomery.toFin_one

/-- A sum reads back as the sum. -/
theorem toFin_add (a b : Montgomery) : toFin (a + b) = toFin a + toFin b :=
  Word64.Montgomery.toFin_add a b

/-- A difference reads back as the difference. -/
theorem toFin_sub (a b : Montgomery) : toFin (a - b) = toFin a - toFin b :=
  Word64.Montgomery.toFin_sub a b

/-- A product reads back as the product. -/
theorem toFin_mul (a b : Montgomery) : toFin (a * b) = toFin a * toFin b :=
  Word64.Montgomery.toFin_mul a b

/-- Distinct elements read back as distinct elements. -/
theorem toFin_injective : Function.Injective toFin := Word64.Montgomery.toFin_injective

/-- Entering the Montgomery form and reading back gives the element itself. -/
theorem toFin_ofFin (a : Fp) : toFin (ofFin a) = a := Word64.Montgomery.toFin_ofFin a

/-- The inverse reads back as the inverse of `Fp`. -/
theorem toFin_inv (a : Montgomery) : toFin (inv a) = Fin.inverse (toFin a) :=
  toFin_ofFin _

/-- Reading the Montgomery form back is a change of field representation. -/
theorem toFin_embedding : Jacobian.Coords.Embedding toFin :=
  ⟨toFin_zero, toFin_one, toFin_add, toFin_sub, toFin_mul, toFin_injective⟩

end EthLib.Cryptography.Secp256r1.Montgomery

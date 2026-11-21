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

open EthLib.Cryptography.Montgomery (Limbs)

/-- The shared Montgomery field on eight 32-bit limbs, at the constants of `p`. -/
abbrev Shared := Cryptography.Montgomery Fp.params

/-- The same Montgomery residue on the eight limbs of the shared field. -/
def toMont (a : Montgomery) : Shared :=
  ⟨narrow a.raw.words, by rw [val_narrow _ rfl, ← a.raw.val_eq]; exact a.lt⟩

private theorem toMont_val (a : Montgomery) :
    Limbs.val (n := 8) (toMont a).limbs = a.raw.val :=
  (val_narrow _ rfl).trans a.raw.val_eq.symm

private theorem mont_ext {a b : Shared} (h : Limbs.val (n := 8) a.limbs =
    Limbs.val (n := 8) b.limbs) : a = b := by
  have h := Limbs.val_injective (n := 8) h
  cases a
  cases b
  cases h
  rfl

private theorem element_ext {a b : Montgomery} (h : a.raw.val = b.raw.val) : a = b := by
  have hr := Raw.val_injective h
  cases a
  cases b
  cases hr
  rfl

/-- Distinct residues stay distinct on the shared limbs. -/
theorem toMont_injective : Function.Injective toMont := fun a b h =>
  element_ext ((toMont_val a).symm.trans ((congrArg (fun z : Shared =>
    Limbs.val (n := 8) z.limbs) h).trans (toMont_val b)))

/-- Zero has the same residue in either representation. -/
theorem toMont_zero : toMont (0 : Montgomery) = 0 := mont_ext (by decide)

/-- One has the same residue in either representation. -/
theorem toMont_one : toMont (1 : Montgomery) = 1 := mont_ext (by decide)

-- Each operation's words, read through its instance.

private theorem raw_add (a b : Montgomery) : (a + b).raw = addRaw a.raw b.raw := by
  simp only [HAdd.hAdd, Add.add, Montgomery.add]

private theorem raw_sub (a b : Montgomery) : (a - b).raw = subRaw a.raw b.raw := by
  simp only [HSub.hSub, Sub.sub, Montgomery.sub]

private theorem raw_mul (a b : Montgomery) : (a * b).raw = reduceOnce (mulAcc a.raw b.raw) := by
  simp only [HMul.hMul, Mul.mul, Montgomery.mul]

private theorem add_val (a b : Montgomery) :
    (a + b).raw.val = (a.raw.val + b.raw.val) % Fp.modulus := by
  rw [raw_add]
  exact addRaw_val _ _ a.lt b.lt

private theorem sub_val (a b : Montgomery) :
    (a - b).raw.val = (a.raw.val + Fp.modulus - b.raw.val) % Fp.modulus := by
  rw [raw_sub, subRaw_val _ _ a.lt b.lt, Nat.add_sub_assoc b.lt.le]

private theorem mul_val (a b : Montgomery) :
    (2^256 * (a * b).raw.val) % Fp.modulus = a.raw.val * b.raw.val % Fp.modulus := by
  have h := mulAcc_spec a.raw b.raw a.lt
  obtain ⟨m, hm⟩ := h.2
  rw [raw_mul, reduceOnce_val _ h.1, Nat.mul_mod_mod, hm, Nat.add_mul_mod_self_right]

private theorem eq_of_radix_mul_mod {x y : Nat} (hx : x < Fp.modulus) (hy : y < Fp.modulus)
    (he : 2^256 * x % Fp.modulus = 2^256 * y % Fp.modulus) : x = y := by
  let inverse := 0xfffffffe00000003fffffffd0000000200000001fffffffe0000000300000000
  have hi : (inverse * 2^256) % Fp.modulus = 1 := by decide
  have inv (v : Nat) : (inverse * (2^256 * v % Fp.modulus)) % Fp.modulus = v % Fp.modulus := by
    rw [Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, hi, Nat.one_mul]
  have h := congrArg (fun v => (inverse * v) % Fp.modulus) he
  rw [inv, inv, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
  exact h

/-- Addition gives the same Montgomery residue in either representation. -/
theorem toMont_add (a b : Montgomery) : toMont (a + b) = toMont a + toMont b := by
  apply mont_ext
  let x := toMont a
  let y := toMont b
  have h := Cryptography.Montgomery.addLimbs_spec Fp.params x.limbs y.limbs x.lt y.lt
  change Limbs.val (n := 8) (toMont (a + b)).limbs =
    Limbs.val (n := 8) (Cryptography.Montgomery.addCore (n := 8) x.limbs y.limbs Fp.params.pLimbs)
  rw [toMont_val, add_val]
  unfold Cryptography.Montgomery.addCore
  rw [h, toMont_val, toMont_val]
  rfl

/-- Subtraction gives the same Montgomery residue in either representation. -/
theorem toMont_sub (a b : Montgomery) : toMont (a - b) = toMont a - toMont b := by
  apply mont_ext
  let x := toMont a
  let y := toMont b
  change Limbs.val (n := 8) (toMont (a - b)).limbs =
    Limbs.val (n := 8) (Cryptography.Montgomery.subLimbs Fp.params x.limbs y.limbs)
  rw [Cryptography.Montgomery.subLimbs_spec Fp.params x.lt y.lt, toMont_val, sub_val]
  rw [toMont_val, toMont_val]
  rfl

/-- Multiplication gives the same Montgomery residue in either representation. -/
theorem toMont_mul (a b : Montgomery) : toMont (a * b) = toMont a * toMont b := by
  let x := toMont a
  let y := toMont b
  have hspec := (Cryptography.Montgomery.mulLimbs_spec Fp.params x.limbs x.lt y.limbs).2
  have hEq : Limbs.val (n := 8) (x * y).limbs =
      Limbs.val (n := 8) (Cryptography.Montgomery.mulWords (Limbs.get Fp.params.pLimbs)
        Fp.params.pinv (Limbs.get x.limbs) (Limbs.get y.limbs) Limbs.pack) := by
    change Limbs.val (n := 8) (Fp.params.mul x.limbs y.limbs) = _
    rw [Fp.params.mul_spec x.limbs y.limbs x.lt]
  change _ = x * y
  apply mont_ext
  have aeq := toMont_val a
  have beq := toMont_val b
  have hm := mul_val a b
  have hc := toMont_val (a * b)
  change (2^256 * _) % Fp.modulus =
    (Limbs.val (n := 8) x.limbs * Limbs.val (n := 8) y.limbs) % Fp.modulus at hspec
  rw [← hEq, aeq, beq] at hspec
  exact eq_of_radix_mul_mod (toMont (a * b)).lt (x * y).lt
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

/-! ## The field read back

Reading an element back into `Fp` keeps zero, one, sums, differences and products.

Distinct elements read back to distinct elements.
-/

/-- Zero reads back as zero. -/
theorem toFin_zero : toFin (0 : Montgomery) = 0 := by
  rw [toFin_eq, toMont_zero, Cryptography.Montgomery.toFin_zero]
  rfl

/-- One reads back as one. -/
theorem toFin_one : toFin (1 : Montgomery) = 1 := by
  rw [toFin_eq, toMont_one, Cryptography.Montgomery.toFin_one]
  rfl

/-- A sum reads back as the sum. -/
theorem toFin_add (a b : Montgomery) : toFin (a + b) = toFin a + toFin b := by
  rw [toFin_eq, toFin_eq, toFin_eq, toMont_add, Cryptography.Montgomery.toFin_add]
  rfl

/-- A difference reads back as the difference. -/
theorem toFin_sub (a b : Montgomery) : toFin (a - b) = toFin a - toFin b := by
  rw [toFin_eq, toFin_eq, toFin_eq, toMont_sub, Cryptography.Montgomery.toFin_sub]
  rfl

/-- A product reads back as the product. -/
theorem toFin_mul (a b : Montgomery) : toFin (a * b) = toFin a * toFin b := by
  rw [toFin_eq, toFin_eq, toFin_eq, toMont_mul, Cryptography.Montgomery.toFin_mul]
  rfl

/-- Distinct elements read back as distinct elements. -/
theorem toFin_injective : Function.Injective toFin := by
  intro a b h
  rw [toFin_eq, toFin_eq] at h
  exact toMont_injective (Cryptography.Montgomery.toFin_injective h)

/-- Entering the Montgomery form and reading back gives the element itself. -/
theorem toFin_ofFin (a : Fp) : toFin (ofFin a) = a :=
  (toFin_eq _).trans ((congrArg Cryptography.Montgomery.toFin (toMont_ofFin a)).trans
    (Cryptography.Montgomery.toFin_ofFin (M := Fp.params) a))

/-- The inverse reads back as the inverse of `Fp`. -/
theorem toFin_inv (a : Montgomery) : toFin (inv a) = Fin.inverse (toFin a) :=
  toFin_ofFin _

/-- Reading the Montgomery form back is a change of field representation. -/
theorem toFin_embedding : Jacobian.Coords.Embedding toFin :=
  ⟨toFin_zero, toFin_one, toFin_add, toFin_sub, toFin_mul, toFin_injective⟩

end EthLib.Cryptography.Secp256r1.Montgomery

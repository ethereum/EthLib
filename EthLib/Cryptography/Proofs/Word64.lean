module

public import EthLib.Cryptography.Word64
public import EthLib.Cryptography.Montgomery
import all EthLib.Cryptography.Montgomery
public import EthLib.Cryptography.Montgomery.Fin
import all EthLib.Cryptography.Montgomery.Fin
public import EthLib.Cryptography.Proofs.Montgomery.Core
public import EthLib.Cryptography.Proofs.Montgomery.Fin
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Proofs: integers of four 64-bit words

Four words determine their integer, and their integer determines them.

The bit that a shift and a mask read from the words is the bit of their integer.

Four words and the eight 32-bit limbs of the shared Montgomery field hold the same integer.

So a field on four words takes its laws from the shared field.

A field that gives the laws of its sum, difference and product gets the other laws from here.
-/

@[expose] public section

namespace EthLib.Cryptography.Word64

open EthLib.Cryptography.Montgomery (Limbs)

/-- The integer of four words, as nested products by `2^64`. -/
private theorem Raw.val_nested (k : Raw) :
    k.val = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * k.w3.toNat + k.w2.toNat) + k.w1.toNat) + k.w0.toNat := by
  simp only [Raw.val, Raw.words, lowValue, wordRadix]
  ring

/-- Distinct words have distinct values. -/
theorem Raw.val_injective : Function.Injective Raw.val := by
  intro x y h
  have hx0 := x.w0.toNat_lt
  have hx1 := x.w1.toNat_lt
  have hx2 := x.w2.toNat_lt
  have hx3 := x.w3.toNat_lt
  have hy0 := y.w0.toNat_lt
  have hy1 := y.w1.toNat_lt
  have hy2 := y.w2.toNat_lt
  have hy3 := y.w3.toNat_lt
  rw [Raw.val_nested, Raw.val_nested] at h
  have e0 : x.w0.toNat = y.w0.toNat := by omega
  have e1 : x.w1.toNat = y.w1.toNat := by omega
  have e2 : x.w2.toNat = y.w2.toNat := by omega
  have e3 : x.w3.toNat = y.w3.toNat := by omega
  cases x
  cases y
  simp only [Raw.mk.injEq]
  exact ⟨UInt64.toNat_inj.mp e0, UInt64.toNat_inj.mp e1, UInt64.toNat_inj.mp e2,
    UInt64.toNat_inj.mp e3⟩

/-- Bit `r` of a word, by a shift and a mask, is bit `r` of its value. -/
private theorem wordBit (w : UInt64) (r : Nat) (hr : r < 64) :
    ((w >>> r.toUInt64) &&& 1 != 0) = w.toNat.testBit r := by
  have hr' : r.toUInt64.toNat % 64 = r := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  have h : ((w >>> r.toUInt64) &&& 1).toNat = (w.toNat >>> r) % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_one, Nat.and_one_is_mod, hr']
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    bne_iff_ne, ne_eq, decide_eq_true_iff, ← UInt64.toNat_inj, h, UInt64.toNat_zero]
  omega

/-- The bit read from four words is the bit of their value. -/
theorem Raw.bit_iff (k : Raw) (s : Nat) : k.bit s = true ↔ (k.val >>> s) % 2 = 1 := by
  have h0 := k.w0.toNat_lt
  have h1 := k.w1.toNat_lt
  have h2 := k.w2.toNat_lt
  have hb : ((k.val >>> s) % 2 = 1) ↔ k.val.testBit s = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, decide_eq_true_iff]
  rw [hb, Raw.val_nested, Nat.testBit_two_pow_mul_add _ h0]
  simp only [Raw.bit]
  split_ifs with c0 c1 c2 c3
  · rw [wordBit _ _ (by omega), Nat.mod_eq_of_lt c0]
  · rw [Nat.testBit_two_pow_mul_add _ h1, ite_eq_left (by omega), show s % 64 = s - 64 by omega,
      wordBit _ _ (by omega)]
  · rw [Nat.testBit_two_pow_mul_add _ h1, ite_eq_right (by omega),
      Nat.testBit_two_pow_mul_add _ h2, ite_eq_left (by omega),
      show s % 64 = s - 64 - 64 by omega, wordBit _ _ (by omega)]
  · rw [Nat.testBit_two_pow_mul_add _ h1, ite_eq_right (by omega),
      Nat.testBit_two_pow_mul_add _ h2, ite_eq_right (by omega),
      show s % 64 = s - 64 - 64 - 64 by omega, wordBit _ _ (by omega)]
  · rw [Nat.testBit_two_pow_mul_add _ h1, ite_eq_right (by omega),
      Nat.testBit_two_pow_mul_add _ h2, ite_eq_right (by omega),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le k.w3.toNat_lt
        (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp only [UInt64.zero_shiftRight, UInt64.zero_and, bne_self_eq_false]

/-! ## Four words and eight limbs -/

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

/-- A joined word is worth its low limb plus `2^32` times its high limb. -/
private theorem join_value (lo hi : UInt32) : (join lo hi).toNat = lo.toNat + 2^32*hi.toNat := by
  have hhi : hi.toNat * 2^32 < 2^64 := Nat.mul_lt_mul_of_pos_right hi.toNat_lt (by decide)
  unfold join
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  change lo.toNat ||| (hi.toNat <<< 32) % 2^64 = _
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hhi, Nat.mul_comm hi.toNat, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt lo.toNat_lt, Nat.add_comm]

/-- The two 32-bit halves of a word give back its value. -/
private theorem split_value (w : UInt64) :
    w.toUInt32.toNat + 2^32*(w >>> 32).toUInt32.toNat = w.toNat := by
  rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]
  change w.toNat % 2^32 + 2^32*(w.toNat / 2^32 % 2^32) = w.toNat
  have h : w.toNat / 2^32 < 2^32 := Nat.div_lt_of_lt_mul w.toNat_lt
  rw [Nat.mod_eq_of_lt h, Nat.mod_add_div]

/-- The integer of eight 32-bit limbs, as a sum of powers of `2^32`. -/
private theorem limbs8_value (a : Cryptography.Montgomery.Limbs8) :
    Limbs.val (n := 8) a = a.l0.toNat + 2^32*a.l1.toNat + 2^64*a.l2.toNat +
      2^96*a.l3.toNat + 2^128*a.l4.toNat + 2^160*a.l5.toNat +
      2^192*a.l6.toNat + 2^224*a.l7.toNat := by
  change a.l0.toNat + 2^32*(a.l1.toNat + 2^32*(a.l2.toNat + 2^32*(a.l3.toNat +
    2^32*(a.l4.toNat + 2^32*(a.l5.toNat + 2^32*(a.l6.toNat + 2^32*(a.l7.toNat + 2^32*0))))))) = _
  omega

/-- Four words joined from eight limbs have the value of the limbs. -/
theorem value_wide (a : Cryptography.Montgomery.Limbs8) :
    value (wide a) = Limbs.val (n := 8) a := by
  simp only [value, lowValue, wide, join_value, limbs8_value, UInt64.toNat_zero,
    Nat.mul_zero, Nat.add_zero, wordRadix]
  omega

/-- Eight limbs split from four words, with no carry, have the value of the words. -/
theorem val_narrow (w : Words64) (h : w.top = 0) :
    Limbs.val (n := 8) (narrow w) = value w := by
  have h0 := split_value w.w0
  have h1 := split_value w.w1
  have h2 := split_value w.w2
  have h3 := split_value w.w3
  simp only [limbs8_value, narrow, value, lowValue, h, UInt64.toNat_zero,
    Nat.mul_zero, Nat.add_zero, wordRadix]
  omega

/-- Joining the two halves of a word gives the word. -/
private theorem join_split (w : UInt64) :
    join w.toUInt32 (w >>> 32).toUInt32 = w :=
  UInt64.toNat_inj.mp ((join_value _ _).trans (split_value w))

/-- Splitting four words into limbs and joining them back gives the words. -/
theorem wide_narrow (w : Words64) (h : w.top = 0) : wide (narrow w) = w := by
  cases w
  cases h
  simp only [wide, narrow, join_split]
  rfl

/-! ## Montgomery fields on four words

A field on four words proves the laws of its own sum, difference and product.

The other laws follow from them once, against the shared field on eight limbs.
-/

namespace Montgomery

open EthLib.Cryptography.Montgomery (Limbs)

/-- The laws of a Montgomery field on four words, mod `p`, and its constants on eight limbs.

Each field proves the laws of its own sum, difference and product. -/
class Laws (p : Nat) [Constants p] [Add (Montgomery p)] [Sub (Montgomery p)]
    [Mul (Montgomery p)] where
  /-- The constants of `p` for the shared Montgomery field on eight 32-bit limbs. -/
  params : Cryptography.Montgomery.Modulus 8
  /-- Those constants are for `p`. -/
  params_p : params.p = p
  /-- A sum holds the sum mod `p`. -/
  add_val : ∀ a b : Montgomery p, (a + b).raw.val = (a.raw.val + b.raw.val) % p
  /-- A difference holds the difference mod `p`. -/
  sub_val : ∀ a b : Montgomery p, (a - b).raw.val = (a.raw.val + p - b.raw.val) % p
  /-- A product holds the product divided by `R = 2^256`, mod `p`. -/
  mul_val : ∀ a b : Montgomery p, 2^256 * (a * b).raw.val % p = a.raw.val * b.raw.val % p

/-- Two residues with the same integer are equal. -/
theorem element_ext {p : Nat} {a b : Montgomery p} (h : a.raw.val = b.raw.val) : a = b := by
  have hr := Raw.val_injective h
  cases a
  cases b
  cases hr
  rfl

/-- Two elements of the shared field with the same limb value are equal. -/
theorem mont_ext {M : Cryptography.Montgomery.Modulus 8} {a b : Cryptography.Montgomery M}
    (h : Limbs.val (n := 8) a.limbs = Limbs.val (n := 8) b.limbs) : a = b := by
  have h := Limbs.val_injective (n := 8) h
  cases a
  cases b
  cases h
  rfl

variable {p : Nat} [Constants p] [Add (Montgomery p)] [Sub (Montgomery p)] [Mul (Montgomery p)]
  [Laws p]

/-- The shared Montgomery field on eight 32-bit limbs, at the constants of `p`. -/
abbrev Shared (p : Nat) [Constants p] [Add (Montgomery p)] [Sub (Montgomery p)]
    [Mul (Montgomery p)] [Laws p] := Cryptography.Montgomery (Laws.params (p := p))

/-- The modulus is odd, since it has an inverse mod `2^32`. -/
theorem modulus_odd : p % 2 = 1 := by
  have h := (Laws.params (p := p)).pinv_spec
  rw [Laws.params_p] at h
  have h2 : (p * (Laws.params (p := p)).pinv.toNat + 1) % 2 = 0 := by
    rw [← Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2^32), h]
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp
  · rw [Nat.add_mod, Nat.mul_mod, hp] at h2
    simp at h2
  · exact hp

/-- Two integers below `p` with the same product by `R = 2^256` mod `p` are equal. -/
theorem eq_of_radix_mul_mod {x y : Nat} (hx : x < p) (hy : y < p)
    (he : 2^256 * x % p = 2^256 * y % p) : x = y := by
  have hc : Nat.Coprime (2^256) p :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr modulus_odd))
  have h := Nat.ModEq.cancel_left_of_coprime (c := 2^256) (by
    rw [Nat.gcd_comm]
    exact hc) he
  rw [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
  exact h

/-- The same Montgomery residue on the eight limbs of the shared field. -/
def toMont (a : Montgomery p) : Shared p :=
  ⟨narrow a.raw.words, by rw [val_narrow _ rfl, ← a.raw.val_eq, Laws.params_p]; exact a.lt⟩

/-- The limbs of a residue hold its integer. -/
theorem toMont_val (a : Montgomery p) : Limbs.val (n := 8) (toMont a).limbs = a.raw.val :=
  (val_narrow _ rfl).trans a.raw.val_eq.symm

/-- Distinct residues stay distinct on the shared limbs. -/
theorem toMont_injective : Function.Injective (toMont (p := p)) := fun a b h =>
  element_ext ((toMont_val a).symm.trans ((congrArg (fun z : Shared p =>
    Limbs.val (n := 8) z.limbs) h).trans (toMont_val b)))

/-- Zero has the same residue in either representation. -/
theorem toMont_zero : toMont (0 : Montgomery p) = 0 := by
  apply mont_ext
  rw [toMont_val, show (0 : Shared p) = Cryptography.Montgomery.zero from rfl]
  unfold Cryptography.Montgomery.zero
  rw [Limbs.val_pack Cryptography.Montgomery.zero_spec.1, Cryptography.Montgomery.zero_spec.2]
  rfl

/-- One has the same residue in either representation. -/
theorem toMont_one : toMont (1 : Montgomery p) = 1 := by
  apply mont_ext
  rw [toMont_val]
  change (Constants.one (p := p)).val = Limbs.val (Laws.params (p := p)).r1
  rw [Constants.one_val, (Laws.params (p := p)).r1_spec, Laws.params_p]

/-- Addition gives the same Montgomery residue in either representation. -/
theorem toMont_add (a b : Montgomery p) : toMont (a + b) = toMont a + toMont b := by
  apply mont_ext
  let x := toMont a
  let y := toMont b
  have h := Cryptography.Montgomery.addLimbs_spec (Laws.params (p := p)) x.limbs y.limbs x.lt y.lt
  change Limbs.val (n := 8) (toMont (a + b)).limbs =
    Limbs.val (n := 8) (Cryptography.Montgomery.addCore (n := 8) x.limbs y.limbs
      (Laws.params (p := p)).pLimbs)
  rw [toMont_val, Laws.add_val]
  unfold Cryptography.Montgomery.addCore
  rw [h, toMont_val, toMont_val, Laws.params_p]

/-- Subtraction gives the same Montgomery residue in either representation. -/
theorem toMont_sub (a b : Montgomery p) : toMont (a - b) = toMont a - toMont b := by
  apply mont_ext
  let x := toMont a
  let y := toMont b
  change Limbs.val (n := 8) (toMont (a - b)).limbs =
    Limbs.val (n := 8) (Cryptography.Montgomery.subLimbs (Laws.params (p := p)) x.limbs y.limbs)
  rw [Cryptography.Montgomery.subLimbs_spec (Laws.params (p := p)) x.lt y.lt, toMont_val,
    Laws.sub_val, toMont_val, toMont_val, Laws.params_p]

/-- Multiplication gives the same Montgomery residue in either representation. -/
theorem toMont_mul (a b : Montgomery p) : toMont (a * b) = toMont a * toMont b := by
  let M := Laws.params (p := p)
  let x := toMont a
  let y := toMont b
  have hspec := (Cryptography.Montgomery.mulLimbs_spec M x.limbs x.lt y.limbs).2
  have hEq : Limbs.val (n := 8) (x * y).limbs =
      Limbs.val (n := 8) (Cryptography.Montgomery.mulWords (Limbs.get M.pLimbs)
        M.pinv (Limbs.get x.limbs) (Limbs.get y.limbs) Limbs.pack) := by
    change Limbs.val (n := 8) (M.mul x.limbs y.limbs) = _
    rw [M.mul_spec x.limbs y.limbs x.lt]
  change _ = x * y
  apply mont_ext
  have aeq := toMont_val a
  have beq := toMont_val b
  have hm := Laws.mul_val a b
  have hc := toMont_val (a * b)
  have hp : M.p = p := Laws.params_p
  change (2^256 * _) % M.p = (Limbs.val (n := 8) x.limbs * Limbs.val (n := 8) y.limbs) % M.p
    at hspec
  rw [← hEq, aeq, beq, hp] at hspec
  have hxy := (x * y).lt
  rw [hp] at hxy
  have hab := (toMont (a * b)).lt
  rw [hp] at hab
  exact eq_of_radix_mul_mod hab hxy
    ((congrArg (fun v => (2^256 * v) % p) hc).trans (hm.trans hspec.symm))

/-- The integer of an element of `Fin p` has the same limbs in either representation. -/
theorem toMont_readRaw (a : Fin p) :
    (toMont (readRaw a)).limbs = Limbs.ofNat a.val := by
  apply Limbs.val_injective
  rw [toMont_val, Limbs.val_ofNat]
  change (rawOfNat a.val).val = a.val % 2^256
  have h : a.val < 2^256 := Nat.lt_trans a.isLt (Constants.bounds (p := p)).2
  rw [rawOfNat_val _ h, Nat.mod_eq_of_lt h]

/-- Both field implementations encode a canonical integer the same way. -/
theorem toMont_ofFin (a : Fin p) :
    toMont (ofFin a) = Cryptography.Montgomery.ofFin (a.cast Laws.params_p.symm) := by
  let M := Laws.params (p := p)
  have h : toMont (montgomerySquare : Montgomery p) = ⟨M.r2, M.r2_lt⟩ := by
    apply mont_ext
    rw [toMont_val]
    change (Constants.square (p := p)).val = Limbs.val M.r2
    rw [Constants.square_val, M.r2_spec, Laws.params_p]
  simp only [ofFin, toMont_mul, h]
  change Cryptography.Montgomery.mulLimbs M M.r2 M.r2_lt (toMont (readRaw a)).limbs =
      Cryptography.Montgomery.mulLimbs M M.r2 M.r2_lt (Limbs.ofNat (a.val % M.p))
  rw [Laws.params_p, Nat.mod_eq_of_lt a.isLt, toMont_readRaw]

/-- Leaving either Montgomery representation gives the same integer. -/
theorem toFin_val_eq (a : Montgomery p) :
    (toFin a).val = (Cryptography.Montgomery.toFin (toMont a)).val := by
  unfold toFin Cryptography.Montgomery.toFin
  dsimp only
  rw [rawToNat_eq, ← toMont_val, toMont_mul, Cryptography.Montgomery.toNat_eq_val]
  have h : (toMont (rawOne : Montgomery p)).limbs = Limbs.ofNat (n := 8) 1 := by
    apply Limbs.val_injective
    rw [toMont_val, Limbs.val_ofNat]
    rfl
  exact congrArg (fun limbs => Limbs.val (Cryptography.Montgomery.mulLimbs (Laws.params (p := p))
    (toMont a).limbs (toMont a).lt limbs).limbs) h

/-! ### The field read back -/

/-- Zero reads back as zero. -/
theorem toFin_zero : toFin (0 : Montgomery p) = 0 := by
  apply Fin.ext
  rw [toFin_val_eq, toMont_zero, Cryptography.Montgomery.toFin_zero]
  rfl

/-- One reads back as one. -/
theorem toFin_one : toFin (1 : Montgomery p) = 1 := by
  apply Fin.ext
  rw [toFin_val_eq, toMont_one, Cryptography.Montgomery.toFin_one, Fin.val_one', Fin.val_one',
    Laws.params_p]

/-- A sum reads back as the sum. -/
theorem toFin_add (a b : Montgomery p) : toFin (a + b) = toFin a + toFin b := by
  apply Fin.ext
  rw [Fin.val_add, toFin_val_eq, toFin_val_eq, toFin_val_eq, toMont_add,
    Cryptography.Montgomery.toFin_add, Fin.val_add]
  exact congrArg _ Laws.params_p

/-- A difference reads back as the difference. -/
theorem toFin_sub (a b : Montgomery p) : toFin (a - b) = toFin a - toFin b := by
  apply Fin.ext
  rw [Fin.sub_def, toFin_val_eq, toFin_val_eq, toFin_val_eq, toMont_sub,
    Cryptography.Montgomery.toFin_sub, Fin.sub_def]
  simp only [Laws.params_p]

/-- A product reads back as the product. -/
theorem toFin_mul (a b : Montgomery p) : toFin (a * b) = toFin a * toFin b := by
  apply Fin.ext
  rw [Fin.val_mul, toFin_val_eq, toFin_val_eq, toFin_val_eq, toMont_mul,
    Cryptography.Montgomery.toFin_mul, Fin.val_mul]
  exact congrArg _ Laws.params_p

/-- Distinct elements read back as distinct elements. -/
theorem toFin_injective : Function.Injective (toFin (p := p)) := by
  intro a b h
  have h := congrArg Fin.val h
  rw [toFin_val_eq, toFin_val_eq] at h
  exact toMont_injective (Cryptography.Montgomery.toFin_injective (Fin.ext h))

/-- Entering the Montgomery form and reading back gives the element itself. -/
theorem toFin_ofFin (a : Fin p) : toFin (ofFin a) = a := by
  apply Fin.ext
  rw [toFin_val_eq, toMont_ofFin, Cryptography.Montgomery.toFin_ofFin]
  rfl

/-- Reading back and entering the Montgomery form again gives the same element. -/
theorem ofFin_toFin (a : Montgomery p) : ofFin (toFin a) = a :=
  toFin_injective (toFin_ofFin _)

end Montgomery

end EthLib.Cryptography.Word64

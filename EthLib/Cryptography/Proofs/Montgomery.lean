module

public import EthLib.Cryptography.Montgomery
public import EthLib.Base.Proofs.BigEndian
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Proofs: Montgomery arithmetic

An element holds `a R mod p`, with `R = 2 ^ 256`, for the integer `a` that it stands for.

The map below sends it to `a` in `ZMod p`, as its limbs times the inverse of `R`.

`R` is invertible mod `p` because `p` is odd.

Each operation maps to the same operation of `ZMod p`, and the map is a bijection.

So the limb arithmetic is the arithmetic of the integers mod `p`.

The inverse agrees with the inverse of `ZMod p` when `p` is prime.
-/

@[expose] public section

namespace EthLib.Cryptography.Montgomery

variable {M : Modulus}

/-- The modulus is below `2 ^ 256`, the radix. -/
theorem Modulus.lt_radix (M : Modulus) : M.p < 2 ^ 256 :=
  M.pLimbs_spec ▸ M.pLimbs.val_lt

/-- The modulus is odd, since its product with `-p⁻¹` is `-1` mod `2 ^ 32`. -/
theorem Modulus.odd (M : Modulus) : M.p % 2 = 1 := by
  have h := M.pinv_spec
  have hv : M.p % 2 = M.pLimbs.l0.toNat % 2 := by
    rw [← M.pLimbs_spec]
    simp only [Limbs.val]
    omega
  rw [hv]
  rcases Nat.mod_two_eq_zero_or_one M.pLimbs.l0.toNat with h0 | h0
  · exfalso
    have : (M.pLimbs.l0.toNat * M.pinv.toNat + 1) % 2 = 1 := by
      rw [Nat.add_mod, Nat.mul_mod, h0]
      simp
    omega
  · exact h0

/-- The radix `R = 2 ^ 256`, mod `p`. -/
def radix (M : Modulus) : ZMod M.p := ((2 ^ 256 : ℕ) : ZMod M.p)

/-- `R` is a unit mod `p`. -/
theorem radix_mul_inv (M : Modulus) : radix M * (radix M)⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one _
    (Nat.Coprime.pow_left 256 ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr M.odd)))

/-- `R⁻¹ R = 1` mod `p`. -/
theorem radix_inv_mul (M : Modulus) : (radix M)⁻¹ * radix M = 1 := by
  rw [mul_comm, radix_mul_inv]

/-- Two values equal after a product by `R` are equal. -/
theorem radix_cancel {x y : ZMod M.p} (h : x * radix M = y * radix M) : x = y := by
  have := congrArg (· * (radix M)⁻¹) h
  simpa only [mul_assoc, radix_mul_inv, mul_one] using this

/-- The integer mod `p` that an element stands for: its limbs times `R⁻¹`. -/
def toZMod (a : Montgomery M) : ZMod M.p :=
  (a.limbs.val : ZMod M.p) * (radix M)⁻¹

/-- The limbs of an element write `a R` mod `p`. -/
theorem limbs_cast (a : Montgomery M) : (a.limbs.val : ZMod M.p) = toZMod a * radix M := by
  rw [toZMod, mul_assoc, radix_inv_mul, mul_one]

/-- The Montgomery product divides the product of the limbs by `R`, mod `p`. -/
theorem mulLimbs_cast (a : Limbs) (ha : a.val < M.p) (b : Limbs) :
    ((mulLimbs M a ha b).limbs.val : ZMod M.p) * radix M = a.val * b.val := by
  obtain ⟨k, hk, hs, hv⟩ := mulWords_spec M.pinv_spec (M.lt_pLimbs ha) b
  rw [M.pLimbs_spec] at hk
  have hc := congrArg (Nat.cast : ℕ → ZMod M.p) hk
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    add_zero] at hc
  change ((reduce M.pLimbs (mulWords M.pLimbs M.pinv a b)).val : ZMod M.p) * _ = _
  rw [reduce_spec hs hv, M.pLimbs_spec, ZMod.natCast_mod, mul_comm, radix, hc]

/-- The product is the product mod `p`. -/
theorem toZMod_mul (a b : Montgomery M) : toZMod (a * b) = toZMod a * toZMod b := by
  apply radix_cancel
  apply radix_cancel
  have h := mulLimbs_cast a.limbs a.lt b.limbs
  rw [limbs_cast, limbs_cast a, limbs_cast b] at h
  change toZMod (mulLimbs M a.limbs a.lt b.limbs) * _ * _ = _
  rw [h]
  ring

/-- The sum is the sum mod `p`. -/
theorem toZMod_add (a b : Montgomery M) : toZMod (a + b) = toZMod a + toZMod b := by
  apply radix_cancel
  obtain ⟨hs, hv⟩ := addWords_spec a.limbs b.limbs
  have := a.lt
  have := b.lt
  have h : ((a + b).limbs.val : ZMod M.p) = a.limbs.val + b.limbs.val := by
    change ((reduce M.pLimbs (addWords a.limbs b.limbs)).val : ZMod M.p) = _
    rw [reduce_spec hs (by rw [M.pLimbs_spec]; omega), M.pLimbs_spec, ZMod.natCast_mod, hv,
      Nat.cast_add]
  rw [limbs_cast, limbs_cast a, limbs_cast b] at h
  rw [h]
  ring

/-- The difference is the difference mod `p`. -/
theorem toZMod_sub' (a b : Montgomery M) : toZMod (sub a b) = toZMod a - toZMod b := by
  apply radix_cancel
  have h : ((sub a b).limbs.val : ZMod M.p) = a.limbs.val - b.limbs.val := by
    change ((subLimbs M.pLimbs a.limbs b.limbs).val : ZMod M.p) = _
    have := b.lt
    rw [subLimbs_spec (M.lt_pLimbs a.lt) (M.lt_pLimbs b.lt), M.pLimbs_spec, ZMod.natCast_mod,
      Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]
  rw [limbs_cast, limbs_cast a, limbs_cast b] at h
  rw [h]
  ring

/-- The difference is the difference mod `p`. -/
theorem toZMod_sub (a b : Montgomery M) : toZMod (a - b) = toZMod a - toZMod b :=
  toZMod_sub' a b

/-- Zero stands for `0`. -/
theorem toZMod_zero : toZMod (0 : Montgomery M) = 0 := by
  have h : (zero : Montgomery M).limbs.val = 0 := rfl
  exact (congrArg (fun n : ℕ => (n : ZMod M.p) * (radix M)⁻¹) h).trans (by simp)

/-- The negation is the negation mod `p`. -/
theorem toZMod_neg (a : Montgomery M) : toZMod (-a) = -toZMod a :=
  (toZMod_sub' zero a).trans (by rw [show toZMod (zero : Montgomery M) = 0 from toZMod_zero,
    zero_sub])

/-- One stands for `1`. -/
theorem toZMod_one : toZMod (1 : Montgomery M) = 1 := by
  change (M.r1.val : ZMod M.p) * _ = 1
  rw [M.r1_spec, ZMod.natCast_mod]
  exact radix_mul_inv M

/-- The element of `n` stands for `n mod p`. -/
theorem toZMod_ofNat (n : ℕ) : toZMod (ofNat n : Montgomery M) = n := by
  apply radix_cancel
  rw [← limbs_cast]
  unfold ofNat
  apply radix_cancel
  rw [mulLimbs_cast, M.r2_spec, Limbs.val_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ M.pos) M.lt_radix), ZMod.natCast_mod,
    ZMod.natCast_mod, Nat.cast_mul, radix]
  ring

/-- The cast of `n` stands for `n mod p`. -/
theorem toZMod_natCast (n : ℕ) : toZMod (n : Montgomery M) = n :=
  toZMod_ofNat n

/-- The power is the power mod `p`. -/
theorem toZMod_pow (a : Montgomery M) (n : ℕ) : toZMod (a ^ n) = toZMod a ^ n := by
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    change toZMod (pow a n) = _
    rw [pow]
    split
    · rename_i h
      subst h
      exact (toZMod_one).trans (pow_zero _).symm
    · rename_i h
      have hrec := ih (n / 2) (by omega) (a * a)
      change toZMod (pow (a * a) (n / 2)) = _ at hrec
      rw [toZMod_mul] at hrec
      dsimp only
      split
      · change toZMod (a * pow (a * a) (n / 2)) = _
        rw [toZMod_mul, hrec, ← pow_two, ← pow_mul, ← pow_succ']
        congr 1
        omega
      · change toZMod (pow (a * a) (n / 2)) = _
        rw [hrec, ← pow_two, ← pow_mul]
        congr 1
        omega

/-- Limbs with the same integer are equal. -/
theorem Limbs.val_injective : Function.Injective Limbs.val := by
  rintro ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ h
  have := a0.toNat_lt; have := a1.toNat_lt; have := a2.toNat_lt; have := a3.toNat_lt
  have := a4.toNat_lt; have := a5.toNat_lt; have := a6.toNat_lt; have := a7.toNat_lt
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
  simp only [Limbs.val] at h
  simp only [Limbs.mk.injEq, ← UInt32.toNat_inj]
  omega

/-- Two elements that stand for the same integer mod `p` are equal. -/
theorem toZMod_injective : Function.Injective (toZMod : Montgomery M → ZMod M.p) := by
  intro a b h
  have hc : (a.limbs.val : ZMod M.p) = b.limbs.val := by rw [limbs_cast, limbs_cast b, h]
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_cast_of_lt a.lt, ZMod.val_cast_of_lt b.lt] at hv
  cases a
  cases b
  congr
  exact Limbs.val_injective hv

/-- Every integer mod `p` has an element. -/
theorem toZMod_surjective : Function.Surjective (toZMod : Montgomery M → ZMod M.p) := by
  intro z
  have : NeZero M.p := ⟨Nat.pos_iff_ne_zero.mp M.pos⟩
  exact ⟨ofNat z.val, by rw [toZMod_ofNat, ZMod.natCast_zmod_val]⟩

/-- The integer that `toNat` returns is the value of the element in `ZMod p`. -/
theorem toNat_eq (a : Montgomery M) : a.toNat = (toZMod a).val := by
  have h := mulLimbs_cast (M := M) a.limbs a.lt Limbs.one
  have hone : Limbs.one.val = 1 := rfl
  rw [hone, Nat.cast_one, mul_one, limbs_cast a] at h
  have hv := congrArg ZMod.val (radix_cancel h)
  rw [ZMod.val_cast_of_lt (mulLimbs M a.limbs a.lt Limbs.one).lt] at hv
  exact hv

/-- The integer of an element is below `p`. -/
theorem toNat_lt (a : Montgomery M) : a.toNat < M.p := (mulLimbs M a.limbs a.lt _).lt

/-- The element of the integer of `a` is `a`. -/
theorem ofNat_toNat (a : Montgomery M) : ofNat a.toNat = a := by
  have : NeZero M.p := ⟨Nat.pos_iff_ne_zero.mp M.pos⟩
  apply toZMod_injective
  rw [toZMod_ofNat, toNat_eq, ZMod.natCast_zmod_val]

/-- The table holds the powers of `a`, from the first powers. -/
theorem powTableAux_spec (a : Montgomery M) (k : ℕ) (t : Array (Montgomery M)) (ht : 0 < t.size)
    (h : ∀ i < t.size, toZMod t[i]! = toZMod a ^ i) :
    (powTableAux a k t).size = t.size + k ∧
      ∀ i < t.size + k, toZMod (powTableAux a k t)[i]! = toZMod a ^ i := by
  induction k generalizing t with
  | zero => exact ⟨rfl, h⟩
  | succ k ih =>
    have hb : toZMod t.back! = toZMod a ^ (t.size - 1) := h _ (by omega)
    obtain ⟨hs, hv⟩ := ih (t.push (mul t.back! a)) (by simp) (by
      intro i hi
      rw [Array.size_push] at hi
      rcases Nat.lt_or_ge i t.size with hlt | hge
      · rw [getElem!_pos (t.push _) i (by simp; omega), Array.getElem_push_lt hlt,
          ← getElem!_pos t i hlt]
        exact h i hlt
      · obtain rfl : i = t.size := by omega
        rw [getElem!_pos (t.push _) t.size (by simp), Array.getElem_push_eq]
        change toZMod (t.back! * a) = _
        rw [toZMod_mul, hb, ← pow_succ]
        congr 1
        omega)
    rw [powTableAux]
    refine ⟨by rw [hs, Array.size_push]; omega, fun i hi => hv i (by simp; omega)⟩

/-- The table holds `a ^ 0` to `a ^ 15`. -/
theorem powTable_spec (a : Montgomery M) {i : ℕ} (hi : i < 16) :
    toZMod (powTable a)[i]! = toZMod a ^ i :=
  (powTableAux_spec a 15 #[one] (by simp) (by
    intro i hi
    obtain rfl : i = 0 := by simpa using hi
    exact toZMod_one.trans (pow_zero _).symm)).2 i (by simpa using hi)

/-- A window raises the accumulator to the 16th power and multiplies by `a ^ d`. -/
theorem toZMod_window (a acc : Montgomery M) {d : UInt32} (hd : d.toNat < 16) :
    toZMod (window (powTable a) acc d) = toZMod acc ^ 16 * toZMod a ^ d.toNat := by
  change toZMod (acc * acc * (acc * acc) * (acc * acc * (acc * acc)) *
    (acc * acc * (acc * acc) * (acc * acc * (acc * acc))) * (powTable a)[d.toNat]!) = _
  simp only [toZMod_mul, powTable_spec a hd]
  ring

/-- The windows of a word `w` raise the accumulator to the power `2 ^ 32`, times `a ^ w`. -/
theorem toZMod_powWord (a acc : Montgomery M) (w : UInt32) :
    toZMod (powWord (powTable a) acc w) = toZMod acc ^ 2 ^ 32 * toZMod a ^ w.toNat := by
  have hw := w.toNat_lt
  have e7 : (w >>> 28).toNat = w.toNat / 2 ^ 28 := by
    simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have e (k : UInt32) (hk : k.toNat < 32) :
      (w >>> k &&& 15).toNat = w.toNat / 2 ^ k.toNat % 16 := by
    rw [UInt32.toNat_and, UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hk,
      Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 4
  have e0 : (w &&& 15).toNat = w.toNat % 16 := by
    rw [UInt32.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 4
  unfold powWord
  simp only
  rw [toZMod_window _ _ (by rw [e0]; omega), toZMod_window _ _ (by rw [e 4 (by decide)]; omega),
    toZMod_window _ _ (by rw [e 8 (by decide)]; omega),
    toZMod_window _ _ (by rw [e 12 (by decide)]; omega),
    toZMod_window _ _ (by rw [e 16 (by decide)]; omega),
    toZMod_window _ _ (by rw [e 20 (by decide)]; omega),
    toZMod_window _ _ (by rw [e 24 (by decide)]; omega),
    toZMod_window _ _ (by rw [e7]; omega), e0, e 4 (by decide), e 8 (by decide),
    e 12 (by decide), e 16 (by decide), e 20 (by decide), e 24 (by decide), e7]
  simp only [UInt32.reduceToNat]
  have hsum : w.toNat = w.toNat % 16 + 16 * (w.toNat / 2 ^ 4 % 16 + 16 * (w.toNat / 2 ^ 8 % 16 +
      16 * (w.toNat / 2 ^ 12 % 16 + 16 * (w.toNat / 2 ^ 16 % 16 + 16 * (w.toNat / 2 ^ 20 % 16 +
      16 * (w.toNat / 2 ^ 24 % 16 + 16 * (w.toNat / 2 ^ 28))))))) := by omega
  conv_rhs => rw [hsum]
  ring

/-- The power by limbs is the power by their integer. -/
theorem toZMod_powLimbs (a : Montgomery M) (e : Limbs) :
    toZMod (powLimbs a e) = toZMod a ^ e.val := by
  unfold powLimbs
  simp only [List.foldl, toZMod_powWord, show toZMod (one : Montgomery M) = 1 from toZMod_one,
    one_pow, one_mul, Limbs.val]
  ring

/-- For a prime modulus, the inverse is the inverse of `ZMod p`. -/
theorem toZMod_inv [Fact M.p.Prime] (a : Montgomery M) : toZMod a⁻¹ = (toZMod a)⁻¹ := by
  change toZMod (powLimbs a M.pm2) = _
  rw [toZMod_powLimbs, M.pm2_spec]
  have h3 : 2 < M.p := by
    have := M.odd
    have := (Fact.out : M.p.Prime).two_le
    omega
  by_cases ha : toZMod a = 0
  · rw [ha, inv_zero, zero_pow (by omega)]
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show M.p - 2 + 1 = M.p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one ha

/-! ## Bytes -/

open EthLib.Base

/-- The four bytes of a limb, the most significant first. -/
def limbBytes (x : UInt32) : List UInt8 :=
  [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- The four bytes of a limb read back as the limb. -/
theorem bytesToNat_limbBytes (x : UInt32) : bytesToNat (limbBytes x) = x.toNat := by
  have := x.toNat_lt
  simp only [limbBytes, bytesToNat, List.foldl, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    UInt32.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega

/-- A limb has four bytes. -/
theorem limbBytes_length (x : UInt32) : (limbBytes x).length = 4 := rfl

/-- The 32 bytes are the bytes of each limb, the highest limb first. -/
theorem Limbs.toBytesBE_toList (a : Limbs) :
    a.toBytesBE.data.toList = limbBytes a.l7 ++ limbBytes a.l6 ++ limbBytes a.l5 ++
      limbBytes a.l4 ++ limbBytes a.l3 ++ limbBytes a.l2 ++ limbBytes a.l1 ++ limbBytes a.l0 :=
  rfl

/-- The 32 bytes of the limbs read back as their integer. -/
theorem Limbs.bytesToNat_toBytesBE (a : Limbs) : bytesToNat a.toBytesBE.data.toList = a.val := by
  rw [Limbs.toBytesBE_toList]
  simp only [bytesToNat_append, bytesToNat_limbBytes, limbBytes_length, Limbs.val]
  omega

/-- The limbs make 32 bytes. -/
theorem Limbs.toBytesBE_size (a : Limbs) : a.toBytesBE.data.toList.length = 32 := rfl

/-- The limbs as 32 bytes are the big-endian bytes of their integer. -/
theorem Limbs.toBytesBE_eq (a : Limbs) : a.toBytesBE.data.toList = natToBytes 32 a.val := by
  conv_lhs => rw [← natToBytes_bytesToNat a.toBytesBE.data.toList]
  rw [a.toBytesBE_size, a.bytesToNat_toBytesBE]

/-- A word read from four bytes is their big-endian integer. -/
theorem Limbs.word_toNat (b : ByteArray) (i : Nat) :
    (Limbs.word b i).toNat = b[i]!.toNat * 2 ^ 24 + b[i + 1]!.toNat * 2 ^ 16 +
      b[i + 2]!.toNat * 2 ^ 8 + b[i + 3]!.toNat := by
  have := b[i]!.toNat_lt
  have := b[i + 1]!.toNat_lt
  have := b[i + 2]!.toNat_lt
  have := b[i + 3]!.toNat_lt
  simp only [Limbs.word, UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32]
  simp only [UInt32.reduceToNat]
  omega

/-- The limbs read from `off` hold the integer of the 32 bytes from `off`, big-endian. -/
theorem Limbs.ofBytesBE_val (b : ByteArray) (off : Nat) :
    (Limbs.ofBytesBE b off).val = bytesToNat (List.ofFn (n := 32) fun k => b[off + k.val]!) := by
  simp only [Limbs.ofBytesBE, Limbs.val, Limbs.word_toNat, List.ofFn_succ, List.ofFn_zero,
    bytesToNat, List.foldl, Fin.val_zero, Fin.val_succ, Nat.add_assoc]
  simp only [Nat.reduceAdd, Nat.add_zero]
  omega

/-- Reading 32 bytes gives the element of their integer, or `none` from `p` on. -/
theorem ofBytesBE_eq (b : ByteArray) (off : Nat) :
    (ofBytesBE b off : Option (Montgomery M)) =
      if bytesToNat (List.ofFn (n := 32) fun k => b[off + k.val]!) < M.p then
        some (ofNat (bytesToNat (List.ofFn (n := 32) fun k => b[off + k.val]!)))
      else none := by
  rw [← Limbs.ofBytesBE_val]
  unfold ofBytesBE
  dsimp only
  have hl : (Limbs.ofBytesBE b off).lt M.pLimbs = true ↔ (Limbs.ofBytesBE b off).val < M.p := by
    rw [Limbs.lt_iff, M.pLimbs_spec]
  by_cases h : (Limbs.ofBytesBE b off).val < M.p
  · simp only [hl.mpr h, h, ite_true]
    have he : Limbs.ofNat ((Limbs.ofBytesBE b off).val % M.p) = Limbs.ofBytesBE b off := by
      apply Limbs.val_injective
      rw [Limbs.val_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (Limbs.val_lt _)]
    unfold ofNat
    rw [he]
  · have h' : (Limbs.ofBytesBE b off).lt M.pLimbs = false := by
      cases hc : (Limbs.ofBytesBE b off).lt M.pLimbs
      · rfl
      · exact absurd (hl.mp hc) h
    simp only [h', h, Bool.false_eq_true, ite_false]

/-- An element as 32 bytes is its integer, big-endian. -/
theorem toBytesBE_eq (a : Montgomery M) : (toBytesBE a).data.toList = natToBytes 32 a.toNat := by
  unfold toBytesBE
  rw [Limbs.toBytesBE_eq]
  rfl

/-- Reading the 32 bytes of an element gives it back. -/
theorem ofBytesBE_toBytesBE (a : Montgomery M) : ofBytesBE (toBytesBE a) 0 = some a := by
  have hl : (List.ofFn (n := 32) fun k => (toBytesBE a)[0 + k.val]!) =
      (toBytesBE a).data.toList := by
    have hs : (toBytesBE a).size = 32 := rfl
    apply List.ext_getElem (by rw [List.length_ofFn, Array.length_toList]; exact hs.symm)
    intro i h1 _
    simp only [List.getElem_ofFn, Nat.zero_add, Array.getElem_toList]
    rw [getElem!_pos (toBytesBE a) i (by simp at h1; omega)]
    rfl
  have hv : bytesToNat (toBytesBE a).data.toList = a.toNat := by
    rw [toBytesBE_eq, bytesToNat_natToBytes, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
      (Nat.lt_trans (toNat_lt a) M.lt_radix) (by norm_num))]
  rw [ofBytesBE_eq, hl, hv]
  simp only [toNat_lt a, ↓reduceIte, ofNat_toNat]

end EthLib.Cryptography.Montgomery

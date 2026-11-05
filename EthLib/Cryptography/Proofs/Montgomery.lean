module

public import EthLib.Cryptography.Montgomery
public import EthLib.Base.Proofs.BigEndian
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Proofs: Montgomery arithmetic

An element holds `a R mod p`, with `R = 2 ^ (32 n)`, for the integer `a` that it stands for.

The map below sends it to `a` in `ZMod p`, as its limbs times the inverse of `R`.

`R` is invertible mod `p` because `p` is odd.

Each operation maps to the same operation of `ZMod p`, and the map is a bijection.

So the limb arithmetic is the arithmetic of the integers mod `p`.

The inverse agrees with the inverse of `ZMod p` when `p` is prime.
-/

@[expose] public section

namespace EthLib.Cryptography.Montgomery

variable {n : Nat} [Words n] [Limbs n] {M : Modulus n}

/-- The modulus is below the radix `2 ^ (32 n)`. -/
theorem Modulus.lt_radix (M : Modulus n) : M.p < 2 ^ (32 * n) :=
  M.num_eq ▸ num_lt M.fits

/-- The modulus is odd, since its product with `-p⁻¹` is `-1` mod `2 ^ 32`. -/
theorem Modulus.odd (M : Modulus n) : M.p % 2 = 1 := by
  have h := M.pinv_spec
  have h2 : (M.p * M.pinv.toNat + 1) % 2 = 0 := by
    rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 32 by decide), h]
  rcases Nat.mod_two_eq_zero_or_one M.p with h0 | h0
  · exfalso
    rw [Nat.add_mod, Nat.mul_mod, h0] at h2
    simp at h2
  · exact h0

/-- The radix `R = 2 ^ (32 n)`, mod `p`. -/
def radix (M : Modulus n) : ZMod M.p := ((2 ^ (32 * n) : ℕ) : ZMod M.p)

/-- `R` is a unit mod `p`. -/
theorem radix_mul_inv (M : Modulus n) : radix M * (radix M)⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one _
    (Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr M.odd)))

/-- `R⁻¹ R = 1` mod `p`. -/
theorem radix_inv_mul (M : Modulus n) : (radix M)⁻¹ * radix M = 1 := by
  rw [mul_comm, radix_mul_inv]

/-- Two values equal after a product by `R` are equal. -/
theorem radix_cancel {x y : ZMod M.p} (h : x * radix M = y * radix M) : x = y := by
  have := congrArg (· * (radix M)⁻¹) h
  simpa only [mul_assoc, radix_mul_inv, mul_one] using this

/-- The integer mod `p` that an element stands for: its limbs times `R⁻¹`. -/
def toZMod (a : Montgomery M) : ZMod M.p :=
  (Limbs.val a.limbs : ZMod M.p) * (radix M)⁻¹

/-- The limbs of an element write `a R` mod `p`. -/
theorem limbs_cast (a : Montgomery M) :
    (Limbs.val a.limbs : ZMod M.p) = toZMod a * radix M := by
  rw [toZMod, mul_assoc, radix_inv_mul, mul_one]

/-- The Montgomery product divides the product of the limbs by `R`, mod `p`. -/
theorem mulLimbs_cast (a : Limbs.T n) (ha : Limbs.val a < M.p) (b : Limbs.T n) :
    (Limbs.val (mulLimbs M a ha b).limbs : ZMod M.p) * radix M =
      Limbs.val a * Limbs.val b := by
  have hc := congrArg (Nat.cast : ℕ → ZMod M.p) (mulLimbs_spec M a ha b).2
  rw [ZMod.natCast_mod, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_mul] at hc
  rw [mul_comm, radix]
  change ((2 ^ (32 * n) : ℕ) : ZMod M.p) * (Limbs.val (mulCore a b M.pLimbs M.pinv) : ZMod M.p) = _
  rw [mulCore]
  exact hc

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
  have h : (Limbs.val (a + b).limbs : ZMod M.p) = Limbs.val a.limbs + Limbs.val b.limbs := by
    have e : Limbs.val (a + b).limbs = (Limbs.val a.limbs + Limbs.val b.limbs) % M.p := by
      change Limbs.val (addCore a.limbs b.limbs M.pLimbs) = _
      rw [addCore]
      exact addLimbs_spec M a.limbs b.limbs a.lt b.lt
    rw [e, ZMod.natCast_mod, Nat.cast_add]
  rw [limbs_cast, limbs_cast a, limbs_cast b] at h
  rw [h]
  ring

/-- The difference is the difference mod `p`. -/
theorem toZMod_sub' (a b : Montgomery M) : toZMod (sub a b) = toZMod a - toZMod b := by
  apply radix_cancel
  have h : (Limbs.val (sub a b).limbs : ZMod M.p) = Limbs.val a.limbs - Limbs.val b.limbs := by
    change (Limbs.val (subLimbs M a.limbs b.limbs) : ZMod M.p) = _
    have := b.lt
    rw [subLimbs_spec M a.lt b.lt, ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add,
      ZMod.natCast_self, add_zero]
  rw [limbs_cast, limbs_cast a, limbs_cast b] at h
  rw [h]
  ring

/-- The difference is the difference mod `p`. -/
theorem toZMod_sub (a b : Montgomery M) : toZMod (a - b) = toZMod a - toZMod b :=
  toZMod_sub' a b

/-- Zero stands for `0`. -/
theorem toZMod_zero : toZMod (0 : Montgomery M) = 0 := by
  have h : Limbs.val (zero : Montgomery M).limbs = 0 := by
    change Limbs.val (Limbs.pack (n := n) Words.zero) = 0
    rw [Limbs.val_pack zero_spec.1, zero_spec.2]
  exact (congrArg (fun k : ℕ => (k : ZMod M.p) * (radix M)⁻¹) h).trans (by simp)

/-- The negation is the negation mod `p`. -/
theorem toZMod_neg (a : Montgomery M) : toZMod (-a) = -toZMod a :=
  (toZMod_sub' zero a).trans (by rw [show toZMod (zero : Montgomery M) = 0 from toZMod_zero,
    zero_sub])

/-- One stands for `1`. -/
theorem toZMod_one : toZMod (1 : Montgomery M) = 1 := by
  change (Limbs.val M.r1 : ZMod M.p) * _ = 1
  rw [M.r1_spec, ZMod.natCast_mod]
  exact radix_mul_inv M

/-- The element of `x` stands for `x mod p`. -/
theorem toZMod_ofNat (x : ℕ) : toZMod (ofNat x : Montgomery M) = x := by
  apply radix_cancel
  rw [← limbs_cast]
  unfold ofNat
  apply radix_cancel
  rw [mulLimbs_cast, M.r2_spec, Limbs.val_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ M.pos) M.lt_radix), ZMod.natCast_mod,
    ZMod.natCast_mod, Nat.cast_mul, radix]
  ring

/-- The cast of `x` stands for `x mod p`. -/
theorem toZMod_natCast (x : ℕ) : toZMod (x : Montgomery M) = x :=
  toZMod_ofNat x

/-- The power is the power mod `p`. -/
theorem toZMod_pow (a : Montgomery M) (k : ℕ) : toZMod (a ^ k) = toZMod a ^ k := by
  induction k using Nat.strong_induction_on generalizing a with
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

/-- Two elements that stand for the same integer mod `p` are equal. -/
theorem toZMod_injective : Function.Injective (toZMod : Montgomery M → ZMod M.p) := by
  intro a b h
  have hc : (Limbs.val a.limbs : ZMod M.p) = Limbs.val b.limbs := by
    rw [limbs_cast, limbs_cast b, h]
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
  rw [toNat_eq_val]
  have h := mulLimbs_cast (M := M) a.limbs a.lt (Limbs.ofNat 1)
  have hone : Limbs.val (Limbs.ofNat (n := n) 1) = 1 := by
    rw [Limbs.val_ofNat]
    have := M.lt_radix
    have := M.pos
    exact Nat.mod_eq_of_lt (by omega)
  rw [hone, Nat.cast_one, mul_one, limbs_cast a] at h
  have hv := congrArg ZMod.val (radix_cancel h)
  rw [ZMod.val_cast_of_lt (mulLimbs M a.limbs a.lt (Limbs.ofNat 1)).lt] at hv
  exact hv

/-- The integer of an element is below `p`. -/
theorem toNat_lt (a : Montgomery M) : a.toNat < M.p :=
  (toNat_eq_val a).symm ▸ (mulLimbs M a.limbs a.lt _).lt

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

/-- The windows of the low `k` limbs raise the accumulator to `2 ^ (32 k)`, times `a ^ e`.

Here `e` is the integer of those limbs. -/
theorem toZMod_powDigits (a : Montgomery M) (l : Limbs.T n) (k : ℕ) (acc : Montgomery M) :
    toZMod (powDigits (powTable a) l k acc) =
      toZMod acc ^ 2 ^ (32 * k) * toZMod a ^ num k (Limbs.get l) 0 := by
  induction k generalizing acc with
  | zero => simp [powDigits, num]
  | succ k ih =>
    rw [powDigits, ih, toZMod_powWord, num_snoc, Nat.zero_add]
    have hw : (Limbs.get l k).toUInt32.toNat = (Limbs.get l k).toNat := by
      rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (Limbs.get_lt l k)]
    rw [hw, radix_succ, mul_pow, ← pow_mul, ← pow_mul, pow_add]
    ring

/-- The power by limbs is the power by their integer. -/
theorem toZMod_powLimbs (a : Montgomery M) (e : Limbs.T n) :
    toZMod (powLimbs a e) = toZMod a ^ Limbs.val e := by
  unfold powLimbs
  rw [toZMod_powDigits, show toZMod (one : Montgomery M) = 1 from toZMod_one, one_pow, one_mul]
  rfl

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

/-- The four bytes of a limb read back as the limb. -/
theorem bytesToNat_limbBytes (x : UInt32) : bytesToNat (limbBytes x) = x.toNat := by
  have := x.toNat_lt
  simp only [limbBytes, bytesToNat, List.foldl, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    UInt32.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega

/-- A limb has four bytes. -/
theorem limbBytes_length (x : UInt32) : (limbBytes x).length = 4 := rfl

/-- The bytes of `k` limbs number `4 k`. -/
theorem bytesBE_length (k : ℕ) (f : ℕ → UInt64) : (bytesBE k f).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [bytesBE, List.length_append, limbBytes_length, ih]
    omega

/-- The bytes of fitting limbs read back as their integer. -/
theorem bytesToNat_bytesBE {k : ℕ} {f : ℕ → UInt64} (h : Fits k f 0) :
    bytesToNat (bytesBE k f) = num k f 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := lt_of_fits h k (by omega)
    rw [Nat.zero_add] at hk
    rw [bytesBE, bytesToNat_append, bytesToNat_limbBytes, bytesBE_length, ih (fits_snoc.mp h).1,
      num_snoc, Nat.zero_add, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hk,
      show (256 : ℕ) ^ (4 * k) = 2 ^ (32 * k) by rw [Nat.pow_mul, Nat.pow_mul]]
    ring

/-- Pushing the limbs appends their bytes. -/
theorem pushLimbs_toList (f : ℕ → UInt64) (k : ℕ) (acc : ByteArray) :
    (pushLimbs f k acc).data.toList = acc.data.toList ++ bytesBE k f := by
  induction k generalizing acc with
  | zero => simp [pushLimbs, bytesBE]
  | succ k ih =>
    rw [pushLimbs, ih, bytesBE]
    simp [pushLimb, limbBytes, ByteArray.push]

/-- An element as `4 n` bytes is its integer, big-endian. -/
theorem toBytesBE_eq (a : Montgomery M) :
    (toBytesBE a).data.toList = natToBytes (4 * n) a.toNat := by
  unfold toBytesBE
  rw [pushLimbs_toList]
  have he : (ByteArray.emptyWithCapacity (4 * n)).data.toList = [] := by
    rfl
  rw [he, List.nil_append]
  conv_lhs => rw [← natToBytes_bytesToNat (bytesBE _ _)]
  rw [bytesBE_length, bytesToNat_bytesBE (Limbs.fits _ 0), toNat_eq_val]
  rfl

/-- A word read from four bytes is their big-endian integer. -/
theorem wordBE_toNat (b : ByteArray) (i : ℕ) :
    (wordBE b i).toNat = b[i]!.toNat * 2 ^ 24 + b[i + 1]!.toNat * 2 ^ 16 +
      b[i + 2]!.toNat * 2 ^ 8 + b[i + 3]!.toNat := by
  have := b[i]!.toNat_lt
  have := b[i + 1]!.toNat_lt
  have := b[i + 2]!.toNat_lt
  have := b[i + 3]!.toNat_lt
  simp only [wordBE, UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32]
  simp only [UInt32.reduceToNat]
  omega

/-- The `4 (m + 1)` bytes from `off` are four bytes, then the `4 m` bytes after them. -/
private theorem ofFn_succ_bytes (b : ByteArray) (m off : ℕ) :
    (List.ofFn (n := 4 * (m + 1)) fun k => b[off + k.val]!) =
      [b[off]!, b[off + 1]!, b[off + 2]!, b[off + 3]!] ++
        List.ofFn (n := 4 * m) fun k => b[off + 4 + k.val]! := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn]
  rw [List.getElem_append]
  split
  · rename_i h
    simp only [List.length_cons, List.length_nil] at h
    match i, h with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
  · rename_i h
    simp only [List.length_cons, List.length_nil, not_lt] at h
    simp only [List.getElem_ofFn, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceAdd] at h ⊢
    rw [show off + 4 + (i - 4) = off + i by omega]

/-- The limbs read from `off` hold the integer of the `4 m` bytes from `off`, big-endian. -/
theorem num_limbBE (b : ByteArray) (m off : ℕ) :
    num m (limbBE m b off) 0 = bytesToNat (List.ofFn (n := 4 * m) fun k => b[off + k.val]!) := by
  induction m generalizing off with
  | zero => rfl
  | succ m ih =>
    rw [num_snoc, ofFn_succ_bytes, bytesToNat_append, List.length_ofFn, ← ih (off + 4)]
    have hc : num m (limbBE (m + 1) b off) 0 = num m (limbBE m b (off + 4)) 0 :=
      num_congr fun i hi => by
        simp only [limbBE]
        congr 2
        omega
    have ht : limbBE (m + 1) b off (0 + m) = (wordBE b off).toUInt64 := by
      simp only [limbBE]
      congr 2
      omega
    rw [hc, ht, UInt32.toNat_toUInt64, wordBE_toNat,
      show (256 : ℕ) ^ (4 * m) = 2 ^ (32 * m) by rw [Nat.pow_mul, Nat.pow_mul]]
    simp only [bytesToNat, List.foldl]
    ring

/-- Reading `4 n` bytes gives the element of their integer, or `none` from `p` on. -/
theorem ofBytesBE_eq (b : ByteArray) (off : ℕ) :
    (ofBytesBE b off : Option (Montgomery M)) =
      if bytesToNat (List.ofFn (n := 4 * n) fun k => b[off + k.val]!) < M.p then
        some (ofNat (bytesToNat (List.ofFn (n := 4 * n) fun k => b[off + k.val]!)))
      else none := by
  rw [← num_limbBE]
  unfold ofBytesBE
  dsimp only
  have hf : Fits n (limbBE n b off) 0 := fits_of_lt fun i _ => by
    simp only [limbBE, UInt32.toNat_toUInt64]
    exact UInt32.toNat_lt _
  obtain ⟨fl, el⟩ := load_spec (n := n) (limbBE n b off) 0
  have hl : ltWords (Words.load (n := n) (limbBE n b off) 0) (Limbs.get M.pLimbs) = true ↔
      num n (limbBE n b off) 0 < M.p := by
    rw [ltWords_iff (fl.mpr hf) M.fits, el, M.num_eq]
  by_cases h : num n (limbBE n b off) 0 < M.p
  · simp only [hl.mpr h, h, ite_true]
    have he : Limbs.ofNat (n := n) (num n (limbBE n b off) 0 % M.p) =
        Limbs.pack (Words.load (n := n) (limbBE n b off) 0) := by
      apply Limbs.val_injective
      rw [Limbs.val_ofNat, Limbs.val_pack (fl.mpr hf), el, Nat.mod_eq_of_lt h,
        Nat.mod_eq_of_lt (num_lt hf)]
    unfold ofNat
    rw [he]
  · have h' : ltWords (Words.load (n := n) (limbBE n b off) 0) (Limbs.get M.pLimbs) = false := by
      cases hc : ltWords (Words.load (n := n) (limbBE n b off) 0) (Limbs.get M.pLimbs)
      · rfl
      · exact absurd (hl.mp hc) h
    simp only [h', h, Bool.false_eq_true, ite_false]

/-- Reading the `4 n` bytes of an element gives it back. -/
theorem ofBytesBE_toBytesBE (a : Montgomery M) : ofBytesBE (toBytesBE a) 0 = some a := by
  have hl : (List.ofFn (n := 4 * n) fun k => (toBytesBE a)[0 + k.val]!) =
      (toBytesBE a).data.toList := by
    have hs := toBytesBE_size a
    apply List.ext_getElem (by rw [List.length_ofFn, Array.length_toList]; exact hs.symm)
    intro i h1 _
    simp only [List.getElem_ofFn, Nat.zero_add, Array.getElem_toList]
    rw [getElem!_pos (toBytesBE a) i (by simp at h1; omega)]
    rfl
  have hv : bytesToNat (toBytesBE a).data.toList = a.toNat := by
    rw [toBytesBE_eq, bytesToNat_natToBytes, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
      (Nat.lt_trans (toNat_lt a) M.lt_radix) (Nat.le_of_eq (by rw [Nat.pow_mul, Nat.pow_mul])))]
  rw [ofBytesBE_eq, hl, hv]
  simp only [toNat_lt a, ↓reduceIte, ofNat_toNat]

end EthLib.Cryptography.Montgomery

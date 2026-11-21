module

/-!
# 64-bit word arithmetic

Products, sums and differences of 64-bit words, with their carries.

Lean has no 128-bit product, so the high word of a product comes from four 32-bit products.

Each operation states its result as an equation of natural numbers.

The Montgomery forms of the base fields of secp256k1 and secp256r1 run on these words.
-/

@[expose] public section

namespace EthLib.Cryptography.Word64

/-- The radix of one word, `2^64`. -/
abbrev wordRadix : Nat := 2^64

/-- The high word of the product of two words, from four 32-bit products. -/
@[inline] def mulHigh (a b : UInt64) : UInt64 :=
  let alo := a &&& 0xffffffff
  let ahi := a >>> 32
  let blo := b &&& 0xffffffff
  let bhi := b >>> 32
  let w0 := alo * blo
  let t := ahi * blo + (w0 >>> 32)
  let w1 := alo * bhi + (t &&& 0xffffffff)
  ahi * bhi + (t >>> 32) + (w1 >>> 32)

/-- The radix of half a word, `2^32`. -/
private abbrev halfRadix : Nat := 2^32

/-- The low half of a word is its value mod `2^32`. -/
private theorem low_eq (x : UInt64) : (x &&& 0xffffffff).toNat = x.toNat % halfRadix := by
  rw [UInt64.toNat_and]
  change x.toNat &&& (2^32 - 1) = x.toNat % 2^32
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- The high half of a word is its value divided by `2^32`. -/
private theorem high_eq (x : UInt64) : (x >>> 32).toNat = x.toNat / halfRadix := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

/-- A product of two half words fits the square of the largest half word. -/
private theorem prod_le {a b : Nat} (ha : a < halfRadix) (hb : b < halfRadix) :
    a * b ≤ (halfRadix - 1) * (halfRadix - 1) := Nat.mul_le_mul (by omega) (by omega)

/-- A half word is at most the largest half word. -/
private theorem half_le {a : Nat} (ha : a < halfRadix) : a ≤ halfRadix - 1 := by omega

/-- A product at most the square of the largest half word does not wrap. -/
private theorem mul_exact {a b : UInt64} (h : a.toNat*b.toNat ≤ (halfRadix - 1)*(halfRadix - 1)) :
    (a*b).toNat = a.toNat*b.toNat := by
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h (by decide))]

/-- A word sum below `2^64` does not wrap. -/
theorem add_exact {a b : UInt64} (h : a.toNat + b.toNat < 2^64) :
    (a+b).toNat = a.toNat+b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

/-- The high half of a product, from the four products of its halves. -/
private theorem model_mulHigh (a b c d : Nat) :
    let w0 := a * c
    let t := b * c + w0 / halfRadix
    let w1 := a * d + t % halfRadix
    ((a + halfRadix*b) * (c + halfRadix*d)) / (halfRadix*halfRadix) =
      b*d + t/halfRadix + w1/halfRadix := by
  dsimp only
  let w0 := a * c
  let t := b * c + w0 / halfRadix
  let w1 := a * d + t % halfRadix
  let lo := w0 % halfRadix + halfRadix * (w1 % halfRadix)
  let hi := b*d + t/halfRadix + w1/halfRadix
  have hlo : lo < halfRadix*halfRadix := by
    have h0 := half_le (Nat.mod_lt w0 (show 0 < halfRadix by decide))
    have h1 := half_le (Nat.mod_lt w1 (show 0 < halfRadix by decide))
    exact Nat.lt_of_le_of_lt (Nat.add_le_add h0 (Nat.mul_le_mul_left halfRadix h1)) (by decide)
  have h : (a + halfRadix*b) * (c + halfRadix*d) = lo + halfRadix*halfRadix*hi := by
    calc
      _ = w0 + halfRadix*(a*d + b*c) + halfRadix*halfRadix*(b*d) := by dsimp only [w0]; grind
      _ = w0 % halfRadix + halfRadix*(a*d + t) + halfRadix*halfRadix*(b*d) := by
        conv => lhs; rw [← Nat.mod_add_div w0 halfRadix]
        dsimp only [t]
        grind
      _ = w0 % halfRadix + halfRadix*(w1 + halfRadix*(t/halfRadix)) +
          halfRadix*halfRadix*(b*d) := by
        conv => lhs; rw [← Nat.mod_add_div t halfRadix]
        dsimp only [w1]
        grind
      _ = lo + halfRadix*halfRadix*hi := by
        conv => lhs; rw [← Nat.mod_add_div w1 halfRadix]
        dsimp only [lo, hi]
        grind
  change ((a + halfRadix*b) * (c + halfRadix*d)) / (halfRadix*halfRadix) = hi
  rw [h, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo, Nat.zero_add]

/-- The high word is the product divided by `2^64`. -/
theorem mulHigh_spec (a b : UInt64) : (mulHigh a b).toNat = a.toNat*b.toNat / 2^64 := by
  let a0 := a &&& 0xffffffff
  let a1 := a >>> 32
  let b0 := b &&& 0xffffffff
  let b1 := b >>> 32
  let w0 := a0*b0
  let t := a1*b0 + (w0 >>> 32)
  let w1 := a0*b1 + (t &&& 0xffffffff)
  have ha0 : a0.toNat < halfRadix := by rw [low_eq]; exact Nat.mod_lt _ (by decide)
  have hb0 : b0.toNat < halfRadix := by rw [low_eq]; exact Nat.mod_lt _ (by decide)
  have ha1 : a1.toNat < halfRadix := by
    rw [high_eq]
    exact Nat.div_lt_of_lt_mul a.toNat_lt
  have hb1 : b1.toNat < halfRadix := by
    rw [high_eq]
    exact Nat.div_lt_of_lt_mul b.toNat_lt
  have h00 := prod_le ha0 hb0
  have h01 := prod_le ha0 hb1
  have h10 := prod_le ha1 hb0
  have h11 := prod_le ha1 hb1
  have h0 : w0.toNat = a0.toNat*b0.toNat := mul_exact h00
  have ht : t.toNat = a1.toNat*b0.toNat + (w0.toNat/halfRadix) := by
    have hw0 : w0.toNat/halfRadix < halfRadix := Nat.div_lt_of_lt_mul w0.toNat_lt
    change (a1*b0 + (w0 >>> 32)).toNat = _
    rw [add_exact (by
      rw [mul_exact h10, high_eq w0]
      exact Nat.lt_of_le_of_lt (Nat.add_le_add h10 (half_le hw0)) (by decide)),
      mul_exact h10, high_eq w0]
  have hw : w1.toNat = a0.toNat*b1.toNat + t.toNat % halfRadix := by
    have htm := Nat.mod_lt t.toNat (show 0 < halfRadix by decide)
    change (a0*b1 + (t &&& 0xffffffff)).toNat = _
    rw [add_exact (by
      rw [mul_exact h01, low_eq t]
      exact Nat.lt_of_le_of_lt (Nat.add_le_add h01 (half_le htm)) (by decide)),
      mul_exact h01, low_eq t]
  have htd : t.toNat/halfRadix < halfRadix := Nat.div_lt_of_lt_mul t.toNat_lt
  have hwd : w1.toNat/halfRadix < halfRadix := Nat.div_lt_of_lt_mul w1.toNat_lt
  have he : (mulHigh a b).toNat = a1.toNat*b1.toNat + t.toNat/halfRadix + w1.toNat/halfRadix := by
    change (a1*b1 + (t >>> 32) + (w1 >>> 32)).toNat = _
    have h1 := Nat.add_le_add h11 (half_le htd)
    have e := add_exact (a := a1*b1) (b := t >>> 32) (by
      rw [mul_exact h11, high_eq t]
      exact Nat.lt_of_le_of_lt h1 (by decide))
    rw [add_exact (by
      rw [e, mul_exact h11, high_eq t, high_eq w1]
      exact Nat.lt_of_le_of_lt (Nat.add_le_add h1 (half_le hwd)) (by decide)),
      e, mul_exact h11, high_eq t, high_eq w1]
  rw [he, hw, ht, h0]
  have ea : a.toNat = a0.toNat + halfRadix*a1.toNat := by
    dsimp only [a0, a1]
    rw [low_eq a, high_eq a, Nat.mod_add_div]
  have eb : b.toNat = b0.toNat + halfRadix*b1.toNat := by
    dsimp only [b0, b1]
    rw [low_eq b, high_eq b, Nat.mod_add_div]
  conv => rhs; rw [ea, eb]
  exact (model_mulHigh a0.toNat a1.toNat b0.toNat b1.toNat).symm

/-- One for `true` and zero for `false`. -/
@[inline] def yes (b : Bool) : UInt64 := b.toUInt64

/-- The addition and its overflow bit represent the full 65-bit sum. -/
theorem add_with_carry (a b : UInt64) :
    (a + b).toNat + 2^64 * (yes (a + b < a)).toNat = a.toNat + b.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  by_cases h : a + b < a
  · have hl : (a.toNat + b.toNat) % 2^64 < a.toNat := by
      simpa only [UInt64.toNat_add] using (show (a + b).toNat < a.toNat from h)
    simp only [yes, Bool.toUInt64, h, decide_true, ite_true, UInt64.toNat_add,
      UInt64.toNat_one, Nat.mul_one]
    omega
  · have hl : ¬ (a.toNat + b.toNat) % 2^64 < a.toNat := by
      simpa only [UInt64.toNat_add] using (show ¬ (a + b).toNat < a.toNat from h)
    simp only [yes, Bool.toUInt64, h, decide_false, Bool.false_eq_true, ite_false, UInt64.toNat_add,
      UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
    omega

/-- Two words, least significant first. -/
structure Pair where
  /-- The low word. -/
  lo : UInt64
  /-- The high word, or the carry. -/
  hi : UInt64

/-- `a b + w + cin`, the step of a column, as two words. -/
@[inline] def mac (a b w cin : UInt64) : Pair :=
  let lo := a*b
  let hi := mulHigh a b
  let s := lo+w
  let t := s+cin
  ⟨t, hi + yes (s < lo) + yes (t < s)⟩

/-- The wide MAC represents the integer product and both added words. -/
theorem mac_spec (a b w cin : UInt64) :
    (mac a b w cin).lo.toNat + 2^64 * (mac a b w cin).hi.toNat =
      a.toNat*b.toNat + w.toNat + cin.toNat := by
  let lo := a*b
  let hi := mulHigh a b
  let s := lo + w
  let t := s + cin
  let c1 := yes (s < lo)
  let c2 := yes (t < s)
  have hmul : lo.toNat + 2^64 * hi.toNat = a.toNat*b.toNat := by
    dsimp only [lo, hi]
    rw [UInt64.toNat_mul, mulHigh_spec, Nat.mod_add_div]
  have hadd1 : s.toNat + 2^64 * c1.toNat = lo.toNat + w.toNat := add_with_carry lo w
  have hadd2 : t.toNat + 2^64 * c2.toNat = s.toNat + cin.toNat := add_with_carry s cin
  have hproduct : a.toNat*b.toNat ≤ (2^64 - 1)*(2^64 - 1) := Nat.mul_le_mul
    (by have := a.toNat_lt; omega) (by have := b.toNat_lt; omega)
  have hw := w.toNat_lt
  have hc := cin.toNat_lt
  have eh : t.toNat + 2^64 * (hi.toNat + c1.toNat + c2.toNat) =
      a.toNat*b.toNat + w.toNat + cin.toNat := by omega
  have hh : hi.toNat + c1.toNat + c2.toNat < 2^64 := by omega
  change t.toNat + 2^64 * (hi + c1 + c2).toNat = _
  rw [add_exact (a := hi + c1) (b := c2) (by rw [add_exact (by omega)]; exact hh),
    add_exact (a := hi) (b := c1) (by omega)]
  exact eh

/-- A word difference and the subtrahend give the minuend, plus `2^64` on a borrow. -/
theorem sub_split (a b : UInt64) :
    (a-b).toNat + b.toNat = a.toNat + wordRadix * (yes (a < b)).toNat := by
  have ha : a.toNat < wordRadix := a.toNat_lt
  have hb : b.toNat < wordRadix := b.toNat_lt
  simp only [wordRadix] at *
  by_cases h : a < b
  · have hn : a.toNat < b.toNat := h
    simp [yes, Bool.toUInt64, h, UInt64.toNat_sub]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have hn : ¬ a.toNat < b.toNat := h
    have hab : b ≤ a := by change b.toNat ≤ a.toNat; omega
    simp [yes, Bool.toUInt64, h, UInt64.toNat_sub_of_le _ _ hab]
    omega

/-- `a + b + carry`, and the carry out. -/
@[inline] def plus (a b carry : UInt64) : Pair :=
  let s := a+b
  let t := s+carry
  ⟨t, yes (s < a) + yes (t < s)⟩

/-- `a - b - borrow`, and the borrow out. -/
@[inline] def minus (a b borrow : UInt64) : Pair :=
  let s := a-b
  ⟨s-borrow, yes (a < b) + yes (s < borrow)⟩

/-- A flag is at most one. -/
theorem yes_le_one (b : Bool) : (yes b).toNat ≤ 1 := by
  cases b <;> decide

/-- Two flags add without wrapping. -/
private theorem yes_sum (a b : Bool) : (yes a + yes b).toNat = (yes a).toNat + (yes b).toNat := by
  cases a <;> cases b <;> decide

/-- An addition word and its carry give the integer sum. -/
theorem plus_spec (a b carry : UInt64) (hc : carry.toNat ≤ 1) :
    (plus a b carry).lo.toNat + wordRadix * (plus a b carry).hi.toNat =
      a.toNat + b.toNat + carry.toNat ∧ (plus a b carry).hi.toNat ≤ 1 := by
  have h0 := add_with_carry a b
  have h1 := add_with_carry (a + b) carry
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [plus, yes_sum, wordRadix] at h0 h1 ⊢
  omega

/-- A subtraction word plus the subtrahends equals the minuend and the borrow. -/
theorem minus_spec (a b borrow : UInt64) (hc : borrow.toNat ≤ 1) :
    (minus a b borrow).lo.toNat + b.toNat + borrow.toNat =
      a.toNat + wordRadix * (minus a b borrow).hi.toNat ∧ (minus a b borrow).hi.toNat ≤ 1 := by
  have h0 := sub_split a b
  have h1 := sub_split (a - b) borrow
  have hb := b.toNat_lt
  have hl := (a - b - borrow).toNat_lt
  simp only [minus, yes_sum, wordRadix] at h0 h1 ⊢
  omega

/-! ## Integers of four and five words -/

/-- Four words and a carry word above them, least significant first. -/
structure Words64 where
  /-- Bits 0 through 63. -/
  w0 : UInt64
  /-- Bits 64 through 127. -/
  w1 : UInt64
  /-- Bits 128 through 191. -/
  w2 : UInt64
  /-- Bits 192 through 255. -/
  w3 : UInt64
  /-- The carry above bit 255. -/
  top : UInt64

/-- The integer of the four low words. -/
def lowValue (w : Words64) : Nat :=
  w.w0.toNat + wordRadix*w.w1.toNat + wordRadix^2*w.w2.toNat + wordRadix^3*w.w3.toNat

/-- The integer of all five words. -/
def value (w : Words64) : Nat := lowValue w + wordRadix^4*w.top.toNat

/-- Four words are below `2^256`. -/
theorem lowValue_lt (w : Words64) : lowValue w < wordRadix^4 := by
  have h0 := w.w0.toNat_lt
  have h1 := w.w1.toNat_lt
  have h2 := w.w2.toNat_lt
  have h3 := w.w3.toNat_lt
  simp only [lowValue, wordRadix]
  omega

/-- With a zero carry, the five words are worth their four low words. -/
theorem value_low_of_top_zero (w : Words64) (h : w.top = 0) :
    value w = lowValue w := by
  simp only [value, h, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]

/-- A 256-bit integer in four words, with the least significant word first. -/
structure Raw where
  /-- Bits 0 through 63. -/
  w0 : UInt64
  /-- Bits 64 through 127. -/
  w1 : UInt64
  /-- Bits 128 through 191. -/
  w2 : UInt64
  /-- Bits 192 through 255. -/
  w3 : UInt64
deriving DecidableEq

/-- The four low words, without the carry word. -/
@[inline] def Raw.fromWords (r : Words64) : Raw := ⟨r.w0, r.w1, r.w2, r.w3⟩

/-- Extend the four words with a zero carry word. -/
@[inline] def Raw.words (t : Raw) : Words64 := ⟨t.w0, t.w1, t.w2, t.w3, 0⟩

/-- The natural number represented by the four words. -/
def Raw.val (t : Raw) : Nat := lowValue t.words

/-- Four words are worth their five-word form with a zero carry. -/
theorem Raw.val_eq (t : Raw) : t.val = value t.words := by
  rw [value_low_of_top_zero _ rfl]
  rfl

/-- Dropping a zero carry word keeps the integer. -/
theorem Raw.fromWords_val (w : Words64) (h : w.top = 0) :
    (Raw.fromWords w).val = value w := by
  rw [value_low_of_top_zero w h]
  rfl

/-- The integer of all five words. -/
abbrev Words64.val (x : Words64) : Nat := value x

/-- Read the low 256 bits in four words. -/
@[inline] def rawOfNat (n : Nat) : Raw :=
  ⟨n.toUInt64, (n >>> 64).toUInt64, (n >>> 128).toUInt64, (n >>> 192).toUInt64⟩

/-- The four words of an integer below `2^256` hold that integer. -/
theorem rawOfNat_val (n : Nat) (hn : n < 2^256) : (rawOfNat n).val = n := by
  simp only [rawOfNat, Raw.val, Raw.words, lowValue, wordRadix,
    Nat.shiftRight_eq_div_pow]
  change n % 2^64 + 2^64 * ((n / 2^64) % 2^64) + 2^128 * ((n / 2^128) % 2^64) +
    2^192 * ((n / 2^192) % 2^64) = n
  omega

/-- Join the four words with shifts by 64 bits. -/
@[inline] def rawToNat (a : Raw) : Nat :=
  let high := (a.w3.toNat <<< 64) + a.w2.toNat
  let middle := (high <<< 64) + a.w1.toNat
  (middle <<< 64) + a.w0.toNat

/-- Joining the words gives their integer. -/
theorem rawToNat_eq (a : Raw) : rawToNat a = a.val := by
  simp only [rawToNat, Nat.shiftLeft_eq, Raw.val, Raw.words, lowValue, wordRadix]
  omega

/-- Bit `i` of four words, and `false` from bit 256 on. -/
@[inline] def Raw.bit (k : Raw) (i : Nat) : Bool :=
  let w := if i < 64 then k.w0 else if i < 128 then k.w1 else if i < 192 then k.w2
    else if i < 256 then k.w3 else 0
  (w >>> (i % 64).toUInt64) &&& 1 != 0

/-- Dropping the carry word keeps the four low words. -/
theorem Raw.fromWords_val_low (w : Words64) : (Raw.fromWords w).val = lowValue w := rfl

/-! ## Sum with carry and difference with borrow -/

/-- The words of `a + b`, for the four low words of each.

The carry is the fifth word. -/
@[inline] def add4 (a b : Words64) : Words64 :=
  let s0 := plus a.w0 b.w0 0
  let s1 := plus a.w1 b.w1 s0.hi
  let s2 := plus a.w2 b.w2 s1.hi
  let s3 := plus a.w3 b.w3 s2.hi
  ⟨s0.lo, s1.lo, s2.lo, s3.lo, s3.hi⟩

/-- The sum and its carry give the integer sum, and the carry is at most one. -/
theorem add4_spec (a b : Words64) :
    value (add4 a b) = lowValue a + lowValue b ∧ (add4 a b).top.toNat ≤ 1 := by
  have e0 := plus_spec a.w0 b.w0 0 (by decide)
  have e1 := plus_spec a.w1 b.w1 (plus a.w0 b.w0 0).hi e0.2
  have e2 := plus_spec a.w2 b.w2 (plus a.w1 b.w1 (plus a.w0 b.w0 0).hi).hi e1.2
  have e3 := plus_spec a.w3 b.w3 (plus a.w2 b.w2 (plus a.w1 b.w1 (plus a.w0 b.w0 0).hi).hi).hi
    e2.2
  simp only [add4]
  generalize plus a.w0 b.w0 0 = s0 at *
  generalize plus a.w1 b.w1 s0.hi = s1 at *
  generalize plus a.w2 b.w2 s1.hi = s2 at *
  generalize plus a.w3 b.w3 s2.hi = s3 at *
  refine ⟨?_, e3.2⟩
  simp only [value, lowValue, wordRadix, UInt64.toNat_zero] at *
  omega

/-- The words of `a - b mod 2^256`, for the four low words of each.

The borrow is the fifth word. -/
@[inline] def sub4 (a b : Words64) : Words64 :=
  let d0 := minus a.w0 b.w0 0
  let d1 := minus a.w1 b.w1 d0.hi
  let d2 := minus a.w2 b.w2 d1.hi
  let d3 := minus a.w3 b.w3 d2.hi
  ⟨d0.lo, d1.lo, d2.lo, d3.lo, d3.hi⟩

/-- The difference plus `b` gives `a`, plus `2^256` on a borrow, which is at most one. -/
theorem sub4_spec (a b : Words64) :
    lowValue (sub4 a b) + lowValue b = lowValue a + 2^256 * (sub4 a b).top.toNat ∧
      (sub4 a b).top.toNat ≤ 1 := by
  have e0 := minus_spec a.w0 b.w0 0 (by decide)
  have e1 := minus_spec a.w1 b.w1 (minus a.w0 b.w0 0).hi e0.2
  have e2 := minus_spec a.w2 b.w2 (minus a.w1 b.w1 (minus a.w0 b.w0 0).hi).hi e1.2
  have e3 := minus_spec a.w3 b.w3 (minus a.w2 b.w2 (minus a.w1 b.w1 (minus a.w0 b.w0 0).hi).hi).hi
    e2.2
  simp only [sub4]
  generalize minus a.w0 b.w0 0 = d0 at *
  generalize minus a.w1 b.w1 d0.hi = d1 at *
  generalize minus a.w2 b.w2 d1.hi = d2 at *
  generalize minus a.w3 b.w3 d2.hi = d3 at *
  refine ⟨?_, e3.2⟩
  simp only [lowValue, wordRadix, UInt64.toNat_zero] at *
  omega

end EthLib.Cryptography.Word64

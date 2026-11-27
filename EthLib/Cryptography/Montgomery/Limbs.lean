module

public import EthLib.Cryptography.Montgomery.Words
public import EthLib.Cryptography.Word64.Four
public import EthLib.Cryptography.Word64.Six

/-!
# Montgomery arithmetic: stored limbs

An element stores its limbs of 32 bits in one structure, with one field for each limb.

Eight limbs hold 256 bits, and twelve hold 384 bits.
-/

@[expose] public section

namespace EthLib.Cryptography.Montgomery

open Internal

section Generic

variable {n : Nat} [Words n]

/-! ## Stored limbs -/

/-- `n` limbs of 32 bits, as an element stores them.

A structure of `n` fields of 32 bits takes one allocation and no work to free. -/
class Limbs (n : Nat) [Words n] where
  /-- The stored limbs. -/
  T : Type
  /-- The limb at an index, and `0` past the last. -/
  get : T → Nat → UInt64
  /-- The low 32 bits of each word. -/
  pack : Words.W n → T
  /-- Equality of stored limbs. -/
  decEq : DecidableEq T
  /-- Each limb is below `2 ^ 32`. -/
  get_lt : ∀ a k, (get a k).toNat < 2 ^ 32
  /-- The stored limbs are the low 32 bits of the words. -/
  get_pack : ∀ t k, k < n → (get (pack t) k).toNat = (Words.word t k).toNat % 2 ^ 32
  /-- Stored limbs with the same limbs are equal. -/
  ext : ∀ a b, (∀ k < n, get a k = get b k) → a = b

/-- Stored limbs compare field by field. -/
instance [Limbs n] : DecidableEq (Limbs.T n) := Limbs.decEq

namespace Limbs

variable [Limbs n]

/-- The integer that the limbs write. -/
def val (a : T n) : Nat := num n (get a) 0

/-- Stored limbs fit. -/
theorem fits (a : T n) (k : Nat) : Fits n (get a) k := fits_of_lt fun _ _ => get_lt a _

/-- Limbs with the same integer are equal. -/
theorem val_injective : Function.Injective (val : T n → Nat) := by
  intro a b h
  apply ext
  intro k hk
  simpa using eq_of_num_eq (fits a 0) (fits b 0) h k hk

/-- The limbs of fitting words write their integer. -/
theorem val_pack {t : Words.W n} (h : Fits n (Words.word t) 0) :
    val (pack (n := n) t) = num n (Words.word t) 0 := by
  have hl := lt_of_fits h
  refine num_congr fun i hi => UInt64.toNat_inj.mp ?_
  rw [get_pack _ _ (by omega), Nat.mod_eq_of_lt (hl i hi)]

/-- The digits of `x` in base `2 ^ 32`. -/
@[inline] def digit (x : Nat) (i : Nat) : UInt64 := (x / 2 ^ (32 * i) % 2 ^ 32).toUInt64

/-- The limbs of `x mod 2 ^ (32 n)`. -/
@[inline] def ofNat (x : Nat) : T n :=
  pack (Words.load (n := n) (digit x) 0)

end Limbs

end Generic

/-! ## Eight limbs

Eight limbs of 32 bits are held two to a word, in four words of 64 bits.

A product can then read each word whole. -/

/-- Eight limbs, stored as four words of 64 bits, the low limb of each pair in the low half. -/
instance : Limbs 8 where
  T := Word64.Raw
  get := Word64.Raw.limb
  pack t := ⟨Word64.pairLimbs t.1 t.2.1, Word64.pairLimbs t.2.2.1 t.2.2.2.1,
    Word64.pairLimbs t.2.2.2.2.1 t.2.2.2.2.2.1,
    Word64.pairLimbs t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2.1⟩
  decEq := inferInstanceAs (DecidableEq Word64.Raw)
  get_lt a k := Word64.Raw.limb_lt a k
  get_pack t k hk := by
    match k, hk with
    | 0, _ => exact Word64.pairLimbs_low _ _
    | 1, _ => exact Word64.pairLimbs_high _ _
    | 2, _ => exact Word64.pairLimbs_low _ _
    | 3, _ => exact Word64.pairLimbs_high _ _
    | 4, _ => exact Word64.pairLimbs_low _ _
    | 5, _ => exact Word64.pairLimbs_high _ _
    | 6, _ => exact Word64.pairLimbs_low _ _
    | 7, _ => exact Word64.pairLimbs_high _ _
  ext a b h := by
    have g (k : Nat) (hk : k < 8) := h k hk
    cases a
    cases b
    simp only [Word64.Raw.mk.injEq]
    exact ⟨Word64.eq_of_halves (g 0 (by decide)) (g 1 (by decide)),
      Word64.eq_of_halves (g 2 (by decide)) (g 3 (by decide)),
      Word64.eq_of_halves (g 4 (by decide)) (g 5 (by decide)),
      Word64.eq_of_halves (g 6 (by decide)) (g 7 (by decide))⟩

/-- Eight limbs write the integer of their four words. -/
theorem Limbs.val_raw (a : Limbs.T 8) : Limbs.val (n := 8) a = Word64.Raw.val a := by
  -- Each word is its low half plus `2^32` times its high half.
  simp only [Limbs.val, num, Limbs.get, Word64.Raw.limb, Word64.low_toNat, Word64.high_toNat,
    Word64.Raw.val_eq_sum]
  omega

/-! ## Twelve limbs

Twelve limbs of 32 bits are held two to a word, in six words of 64 bits.

A product can then read each word whole. -/

/-- Twelve limbs, stored as six words of 64 bits, the low limb of each pair in the low half. -/
instance : Limbs 12 where
  T := Word64.Words6
  get := Word64.Words6.limb
  pack t := ⟨Word64.pairLimbs t.1 t.2.1, Word64.pairLimbs t.2.2.1 t.2.2.2.1,
    Word64.pairLimbs t.2.2.2.2.1 t.2.2.2.2.2.1,
    Word64.pairLimbs t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2.1,
    Word64.pairLimbs t.2.2.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2.2.2.1,
    Word64.pairLimbs t.2.2.2.2.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2.2.2.2.2.1⟩
  decEq := inferInstanceAs (DecidableEq Word64.Words6)
  get_lt a k := Word64.Words6.limb_lt a k
  get_pack t k hk := by
    match k, hk with
    | 0, _ => exact Word64.pairLimbs_low _ _
    | 1, _ => exact Word64.pairLimbs_high _ _
    | 2, _ => exact Word64.pairLimbs_low _ _
    | 3, _ => exact Word64.pairLimbs_high _ _
    | 4, _ => exact Word64.pairLimbs_low _ _
    | 5, _ => exact Word64.pairLimbs_high _ _
    | 6, _ => exact Word64.pairLimbs_low _ _
    | 7, _ => exact Word64.pairLimbs_high _ _
    | 8, _ => exact Word64.pairLimbs_low _ _
    | 9, _ => exact Word64.pairLimbs_high _ _
    | 10, _ => exact Word64.pairLimbs_low _ _
    | 11, _ => exact Word64.pairLimbs_high _ _
  ext a b h := by
    have g (k : Nat) (hk : k < 12) := h k hk
    cases a
    cases b
    simp only [Word64.Words6.mk.injEq]
    exact ⟨Word64.eq_of_halves (g 0 (by decide)) (g 1 (by decide)),
      Word64.eq_of_halves (g 2 (by decide)) (g 3 (by decide)),
      Word64.eq_of_halves (g 4 (by decide)) (g 5 (by decide)),
      Word64.eq_of_halves (g 6 (by decide)) (g 7 (by decide)),
      Word64.eq_of_halves (g 8 (by decide)) (g 9 (by decide)),
      Word64.eq_of_halves (g 10 (by decide)) (g 11 (by decide))⟩

/-- Twelve limbs write the integer of their six words. -/
theorem Limbs.val_words6 (a : Limbs.T 12) : Limbs.val (n := 12) a = Word64.Words6.val a := by
  -- Each word is its low half plus `2^32` times its high half.
  simp only [Limbs.val, num, Limbs.get, Word64.Words6.limb, Word64.low_toNat, Word64.high_toNat,
    Word64.Words6.val]
  omega

end EthLib.Cryptography.Montgomery

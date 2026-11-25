module

public import EthLib.Cryptography.Montgomery.Words

/-!
# Montgomery arithmetic: stored limbs

An element stores its limbs of 32 bits in one structure, with one field for each limb.

Eight limbs hold 256 bits, and twelve hold 384 bits.
-/

@[expose] public section

namespace EthLib.Cryptography.Montgomery

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

/-! ## Eight limbs -/

/-- An integer below `2 ^ 256`, as 8 limbs of 32 bits, the lowest first. -/
structure Limbs8 where
  l0 : UInt32
  l1 : UInt32
  l2 : UInt32
  l3 : UInt32
  l4 : UInt32
  l5 : UInt32
  l6 : UInt32
  l7 : UInt32
deriving DecidableEq, Inhabited

/-- The limb at an index, and `0` past the last. -/
@[inline] def Limbs8.get (a : Limbs8) : Nat → UInt64
  | 0 => a.l0.toUInt64
  | 1 => a.l1.toUInt64
  | 2 => a.l2.toUInt64
  | 3 => a.l3.toUInt64
  | 4 => a.l4.toUInt64
  | 5 => a.l5.toUInt64
  | 6 => a.l6.toUInt64
  | 7 => a.l7.toUInt64
  | _ => 0

/-- Eight limbs, stored in a structure of eight fields. -/
instance : Limbs 8 where
  T := Limbs8
  get := Limbs8.get
  pack t := ⟨t.1.toUInt32, t.2.1.toUInt32, t.2.2.1.toUInt32, t.2.2.2.1.toUInt32,
    t.2.2.2.2.1.toUInt32, t.2.2.2.2.2.1.toUInt32, t.2.2.2.2.2.2.1.toUInt32,
    t.2.2.2.2.2.2.2.1.toUInt32⟩
  decEq := inferInstanceAs (DecidableEq Limbs8)
  get_lt a k := by
    unfold Limbs8.get
    split <;> first | exact UInt32.toNat_lt _ | decide
  get_pack t k hk := by
    have e (x : UInt64) : x.toUInt32.toUInt64.toNat = x.toNat % 2 ^ 32 := by
      rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    match k, hk with
    | 0, _ => exact e _
    | 1, _ => exact e _
    | 2, _ => exact e _
    | 3, _ => exact e _
    | 4, _ => exact e _
    | 5, _ => exact e _
    | 6, _ => exact e _
    | 7, _ => exact e _
  ext a b h := by
    have g (k : Nat) (hk : k < 8) := h k hk
    cases a
    cases b
    simp only [Limbs8.mk.injEq]
    exact ⟨UInt32.toUInt64_inj.mp (g 0 (by decide)), UInt32.toUInt64_inj.mp (g 1 (by decide)),
      UInt32.toUInt64_inj.mp (g 2 (by decide)), UInt32.toUInt64_inj.mp (g 3 (by decide)),
      UInt32.toUInt64_inj.mp (g 4 (by decide)), UInt32.toUInt64_inj.mp (g 5 (by decide)),
      UInt32.toUInt64_inj.mp (g 6 (by decide)), UInt32.toUInt64_inj.mp (g 7 (by decide))⟩

/-! ## Twelve limbs -/

/-- An integer below `2 ^ 384`, as 12 limbs of 32 bits, the lowest first. -/
structure Limbs12 where
  l0 : UInt32
  l1 : UInt32
  l2 : UInt32
  l3 : UInt32
  l4 : UInt32
  l5 : UInt32
  l6 : UInt32
  l7 : UInt32
  l8 : UInt32
  l9 : UInt32
  l10 : UInt32
  l11 : UInt32
deriving DecidableEq, Inhabited

/-- The limb at an index, and `0` past the last. -/
@[inline] def Limbs12.get (a : Limbs12) : Nat → UInt64
  | 0 => a.l0.toUInt64
  | 1 => a.l1.toUInt64
  | 2 => a.l2.toUInt64
  | 3 => a.l3.toUInt64
  | 4 => a.l4.toUInt64
  | 5 => a.l5.toUInt64
  | 6 => a.l6.toUInt64
  | 7 => a.l7.toUInt64
  | 8 => a.l8.toUInt64
  | 9 => a.l9.toUInt64
  | 10 => a.l10.toUInt64
  | 11 => a.l11.toUInt64
  | _ => 0

/-- Twelve limbs, stored in a structure of twelve fields. -/
instance : Limbs 12 where
  T := Limbs12
  get := Limbs12.get
  pack t := ⟨t.1.toUInt32, t.2.1.toUInt32, t.2.2.1.toUInt32, t.2.2.2.1.toUInt32,
    t.2.2.2.2.1.toUInt32, t.2.2.2.2.2.1.toUInt32, t.2.2.2.2.2.2.1.toUInt32,
    t.2.2.2.2.2.2.2.1.toUInt32, t.2.2.2.2.2.2.2.2.1.toUInt32,
    t.2.2.2.2.2.2.2.2.2.1.toUInt32, t.2.2.2.2.2.2.2.2.2.2.1.toUInt32,
    t.2.2.2.2.2.2.2.2.2.2.2.1.toUInt32⟩
  decEq := inferInstanceAs (DecidableEq Limbs12)
  get_lt a k := by
    unfold Limbs12.get
    split <;> first | exact UInt32.toNat_lt _ | decide
  get_pack t k hk := by
    have e (x : UInt64) : x.toUInt32.toUInt64.toNat = x.toNat % 2 ^ 32 := by
      rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    match k, hk with
    | 0, _ => exact e _
    | 1, _ => exact e _
    | 2, _ => exact e _
    | 3, _ => exact e _
    | 4, _ => exact e _
    | 5, _ => exact e _
    | 6, _ => exact e _
    | 7, _ => exact e _
    | 8, _ => exact e _
    | 9, _ => exact e _
    | 10, _ => exact e _
    | 11, _ => exact e _
  ext a b h := by
    have g (k : Nat) (hk : k < 12) := h k hk
    cases a
    cases b
    simp only [Limbs12.mk.injEq]
    exact ⟨UInt32.toUInt64_inj.mp (g 0 (by decide)), UInt32.toUInt64_inj.mp (g 1 (by decide)),
      UInt32.toUInt64_inj.mp (g 2 (by decide)), UInt32.toUInt64_inj.mp (g 3 (by decide)),
      UInt32.toUInt64_inj.mp (g 4 (by decide)), UInt32.toUInt64_inj.mp (g 5 (by decide)),
      UInt32.toUInt64_inj.mp (g 6 (by decide)), UInt32.toUInt64_inj.mp (g 7 (by decide)),
      UInt32.toUInt64_inj.mp (g 8 (by decide)), UInt32.toUInt64_inj.mp (g 9 (by decide)),
      UInt32.toUInt64_inj.mp (g 10 (by decide)), UInt32.toUInt64_inj.mp (g 11 (by decide))⟩

end EthLib.Cryptography.Montgomery

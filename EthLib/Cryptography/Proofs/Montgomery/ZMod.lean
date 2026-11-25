module

-- The modulus is not zero there, so `ZMod p` is finite.
public import EthLib.Cryptography.Montgomery.Fin
public import EthLib.Cryptography.Proofs.Montgomery
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.EquivFin

/-!
# Proofs: Montgomery elements as `ZMod p`

The map to `ZMod p` is a ring isomorphism, so the elements form a commutative ring.

For a prime `p` they form a field, with the division that each field specifies.
-/

@[expose] public section

namespace EthLib.Cryptography.Montgomery

variable {n : Nat} [Words n] [Limbs n] {M : Modulus n}

/-- The element that an integer mod `p` stands for. -/
def ofZMod (z : ZMod M.p) : Montgomery M := ofNat z.val

/-- An integer mod `p` maps back to itself. -/
theorem toZMod_ofZMod (z : ZMod M.p) : toZMod (ofZMod z : Montgomery M) = z :=
  (toZMod_ofNat z.val).trans (ZMod.natCast_zmod_val z)

/-- An element maps back to itself. -/
theorem ofZMod_toZMod (a : Montgomery M) : ofZMod (toZMod a) = a :=
  toZMod_injective (toZMod_ofZMod _)

/-- The elements and `ZMod p` are isomorphic rings.

An element maps to the integer mod `p` that it stands for. -/
def toZModEquiv : Montgomery M ≃+* ZMod M.p where
  toFun := toZMod
  invFun := ofZMod
  left_inv := ofZMod_toZMod
  right_inv := toZMod_ofZMod
  map_mul' := toZMod_mul
  map_add' := toZMod_add

/-- The isomorphism is the map to `ZMod p`. -/
@[simp] theorem toZModEquiv_apply (a : Montgomery M) : toZModEquiv a = toZMod a := rfl

/-- The inverse of the isomorphism reads the element of an integer mod `p`. -/
@[simp] theorem toZModEquiv_symm_apply (z : ZMod M.p) :
    toZModEquiv.symm z = (ofZMod z : Montgomery M) := rfl

-- The scalar actions and the cast from the integers go through `ZMod p`.
--
-- Proofs alone use them, as the operations of the elements need none of them.

instance : SMul ℕ (Montgomery M) := ⟨fun k a => ofZMod (k • toZMod a)⟩

instance : SMul ℤ (Montgomery M) := ⟨fun k a => ofZMod (k • toZMod a)⟩

instance : IntCast (Montgomery M) := ⟨fun k => ofZMod k⟩

/-- The commutative ring of `ZMod p`, carried to the elements by the isomorphism. -/
instance instCommRing : CommRing (Montgomery M) :=
  Function.Injective.commRing toZMod toZMod_injective toZMod_zero toZMod_one toZMod_add
    toZMod_mul toZMod_neg toZMod_sub (fun _ _ => toZMod_ofZMod _) (fun _ _ => toZMod_ofZMod _)
    toZMod_pow toZMod_natCast (fun _ => toZMod_ofZMod _)

/-- The elements are finite, through the isomorphism. -/
instance : Fintype (Montgomery M) := Fintype.ofEquiv _ toZModEquiv.symm.toEquiv

/-- There are `p` elements. -/
theorem card_eq : Fintype.card (Montgomery M) = M.p :=
  (Fintype.card_congr toZModEquiv.toEquiv).trans (ZMod.card M.p)

/-- The field of `ZMod p`, for a prime `p`, carried to the elements by the isomorphism.

Its inverse is the one of the elements, and its division is the one in context.

A field keeps the division its specification states, so this is a definition, not an instance. -/
abbrev field [Fact M.p.Prime] [Div (Montgomery M)]
    (div : ∀ a b : Montgomery M, toZMod (a / b) = toZMod a / toZMod b) : Field (Montgomery M) :=
  letI : SMul ℚ≥0 (Montgomery M) := ⟨fun q a => ofZMod (q • toZMod a)⟩
  letI : SMul ℚ (Montgomery M) := ⟨fun q a => ofZMod (q • toZMod a)⟩
  letI : Pow (Montgomery M) ℤ := ⟨fun a k => ofZMod (toZMod a ^ k)⟩
  letI : NNRatCast (Montgomery M) := ⟨fun q => ofZMod q⟩
  letI : RatCast (Montgomery M) := ⟨fun q => ofZMod q⟩
  Function.Injective.field toZMod toZMod_injective toZMod_zero toZMod_one toZMod_add
    toZMod_mul toZMod_neg toZMod_sub toZMod_inv div (fun _ _ => toZMod_ofZMod _)
    (fun _ _ => toZMod_ofZMod _) (fun _ _ => toZMod_ofZMod _) (fun _ _ => toZMod_ofZMod _)
    toZMod_pow (fun _ _ => toZMod_ofZMod _) toZMod_natCast (fun _ => toZMod_ofZMod _)
    (fun _ => toZMod_ofZMod _) (fun _ => toZMod_ofZMod _)

end EthLib.Cryptography.Montgomery

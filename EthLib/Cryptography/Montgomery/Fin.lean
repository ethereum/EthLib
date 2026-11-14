module

public import EthLib.Cryptography.Montgomery

/-!
# Montgomery forms of `Fin p`

An element of `Fin p` enters Montgomery form once, before a chain of products.

It leaves that form once, at the end of the chain.

Both conversions are one Montgomery product: with `R^2 mod p` going in, with `1` going out.
-/

@[expose] public section

namespace EthLib.Cryptography.Montgomery

variable {n : Nat} [Words n] [Limbs n] {M : Modulus n}

/-- The modulus is not zero, so `Fin p` has its literals. -/
instance Modulus.neZero (M : Modulus n) : NeZero M.p := ⟨Nat.pos_iff_ne_zero.mp M.pos⟩

/-- The Montgomery form of an element of `Fin p`. -/
@[no_expose, inline] def ofFin (a : Fin M.p) : Montgomery M := ofNat a.val

/-- The element of `Fin p` that a Montgomery form stands for.

Other modules see only the conversion laws, not its body. -/
@[no_expose, inline] def toFin (a : Montgomery M) : Fin M.p :=
  ⟨a.toNat, by
    rw [toNat_eq_val]
    exact (mulLimbs M a.limbs a.lt _).lt⟩

end EthLib.Cryptography.Montgomery

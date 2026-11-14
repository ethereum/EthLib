module

public import EthLib.Cryptography.Secp256k1.Field

-- The conversion laws need the bodies of `Fn.toMontgomery` and `Fn.ofMontgomery`.
import all EthLib.Cryptography.Secp256k1.Field
public import EthLib.Cryptography.Proofs.Montgomery
public import EthLib.Cryptography.Proofs.Inverse

/-!
# Montgomery inverses of secp256k1 scalars

The inverse through Montgomery form agrees with the Euclidean inverse for every scalar.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Fn

private instance : NeZero params.p := ⟨by decide⟩

private def residue (a : Fn) : ZMod params.p := (a.val : ZMod params.p)

private theorem residue_injective : Function.Injective residue := by
  intro a b h
  apply Fin.ext
  have ha : a.val < params.p := a.isLt
  have hb : b.val < params.p := b.isLt
  have h := congrArg ZMod.val h
  simpa only [residue, ZMod.val_natCast, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb] using h

private theorem residue_ofMontgomery (a : Montgomery) :
    residue (ofMontgomery a) = EthLib.Cryptography.Montgomery.toZMod a := by
  unfold ofMontgomery
  change (a.toNat : ZMod params.p) = _
  rw [EthLib.Cryptography.Montgomery.toNat_eq, ZMod.natCast_zmod_val]

private theorem toZMod_toMontgomery (a : Fn) :
    EthLib.Cryptography.Montgomery.toZMod (toMontgomery a) = residue a := by
  unfold toMontgomery
  exact EthLib.Cryptography.Montgomery.toZMod_ofNat a.val

/-- The scalar conversion preserves its value. -/
theorem ofMontgomery_toMontgomery (a : Fn) : ofMontgomery (toMontgomery a) = a := by
  apply residue_injective
  rw [residue_ofMontgomery, toZMod_toMontgomery]

/-- For the prime scalar modulus, Fermat and Euclid give the same inverse, including at zero. -/
theorem inv_eq_inverse (hprime : Nat.Prime modulus) (a : Fn) : inv a = Fin.inverse a := by
  let : Fact (Nat.Prime params.p) := ⟨hprime⟩
  apply residue_injective
  change residue (ofMontgomery (EthLib.Cryptography.Montgomery.inv (toMontgomery a))) = _
  rw [residue_ofMontgomery]
  change EthLib.Cryptography.Montgomery.toZMod (toMontgomery a)⁻¹ = _
  rw [EthLib.Cryptography.Montgomery.toZMod_inv, toZMod_toMontgomery]
  exact (Fin.inverse_val (m := params.p) a).symm

end EthLib.Cryptography.Secp256k1.Fn

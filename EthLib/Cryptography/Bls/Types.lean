module

/-!
# `Bls.Types`

The 48-byte BLS public key as a structure, with the equality and the order of its bytes.

The module imports no curve arithmetic, so a type that names a key does not import the pairing.

The ciphersuite of Ethereum, of §4.2.3 of the BLS signature draft, version 4, puts keys in `G1`.

<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-4.2.3>
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- A public key: the 48 bytes of a compressed `G1` point.

The type names the role of the bytes, not their validity as a key. -/
structure BLSPubkey where
  /-- The 48 bytes of the compressed point. -/
  bytes : Vector UInt8 48
deriving Repr, Inhabited

/-- Public keys are equal exactly when their bytes are equal. -/
instance : DecidableEq BLSPubkey := fun a b =>
  -- The bytes decide, and the structure has no other field.
  decidable_of_iff ((a.bytes == b.bytes) = true) (beq_iff_eq.trans
    ⟨fun same => by cases a; cases b; cases same; rfl, congrArg BLSPubkey.bytes⟩)

/-- Public keys compare as their bytes, so a search tree can hold them. -/
instance : Ord BLSPubkey where
  compare a b := compare a.bytes b.bytes

/-- Public keys compare as their bytes, so the order is oriented and transitive. -/
instance : Std.TransOrd BLSPubkey where
  -- Both laws are those of the order on byte vectors.
  eq_swap := Std.OrientedCmp.eq_swap (cmp := fun a b : Vector UInt8 48 => compare a b)
  isLE_trans := Std.TransCmp.isLE_trans (cmp := fun a b : Vector UInt8 48 => compare a b)

/-- Public keys compare as equal exactly when they are equal. -/
instance : Std.LawfulEqOrd BLSPubkey where
  -- Equal bytes make equal keys.
  eq_of_compare h :=
    congrArg BLSPubkey.mk
      (Std.LawfulEqCmp.eq_of_compare (cmp := fun a b : Vector UInt8 48 => compare a b) h)

end EthLib.Cryptography.Bls

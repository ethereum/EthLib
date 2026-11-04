module

public import EthLib.Cryptography.Hash.Keccak

/-!
# Proofs: Keccak-256

Every Keccak-256 digest is 32 bytes.

Other proof files write bytes as hex strings, which the reader below turns into bytes.

The Keccak-256 test vectors are in the Python suite, through the bindings.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

/-! ## Hex strings -/

/-- The value of one hex digit, upper or lower case. -/
def hexDigit (c : Char) : Nat :=
  -- '0' is 48, 'A' is 65 and 'a' is 97 in ASCII.
  if c.toNat < 58 then c.toNat - 48 else if c.toNat < 71 then c.toNat - 55 else c.toNat - 87

/-- The bytes a hex string spells, two digits per byte, the high digit first. -/
def hexBytes (s : String) : ByteArray :=
  ⟨(go s.toList).toArray⟩
where
  /-- Read the digits two at a time. -/
  go : List Char → List UInt8
    | hi :: lo :: rest => UInt8.ofNat (16 * hexDigit hi + hexDigit lo) :: go rest
    | _ => []

/-! ## The digest length -/

/-- Every digest is 32 bytes, whatever the message. -/
theorem size_keccak256 (msg : ByteArray) : (keccak256 msg).toArray.size = DIGEST_LEN :=
  (keccak256 msg).size_toArray

end EthLib.Cryptography.Hash.Keccak

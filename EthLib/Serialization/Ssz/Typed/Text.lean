module

public import EthLib.Serialization.Ssz.Typed.Class

/-!
# Typed SSZ values: text

A text held in a byte list as its UTF-8 bytes, as a URL is.

A Lean string is valid UTF-8, so every text has its bytes.

Bytes that are not UTF-8 hold no text, and are refused.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- `ByteList[limit]` that holds the UTF-8 bytes of a text. -/
structure SszString (limit : Nat) where
  /-- The text. -/
  text : String
  /-- Its UTF-8 bytes stay within the limit. -/
  bound : text.utf8ByteSize ≤ limit
  deriving DecidableEq

instance {limit : Nat} : SszType (SszString limit) where
  desc := .byteList limit
  toValue s := .bytes s.text.toByteArray.data
  ofValue
    | .bytes data =>
      if within : data.size ≤ limit then
        if valid : ByteArray.IsValidUTF8 ⟨data⟩ then .ok ⟨String.fromUTF8 ⟨data⟩ valid, within⟩
        else .error .notUtf8
      else .error (.overLimit limit data.size)
    | _ => .error .typeMismatch

end EthLib.Serialization.Ssz

module

public import EthLib.Serialization.Ssz.Typed.Text
public import EthLib.Serialization.Proofs.Ssz.Codec.Fits

/-!
# Proofs: a text reads back from its bytes

The UTF-8 bytes of a text fit its byte list, and decode back to that text.

Bytes that decode to a text are its UTF-8 bytes.

The type is not lawful: bytes that are not UTF-8 fit the byte list, and hold no text.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open SszType

variable {limit : Nat}

/-- The UTF-8 bytes of a text fit its byte list. -/
theorem SszString.fits (s : SszString limit) : Fits (desc (SszString limit)) (toValue s) :=
  .byteList (by simpa [ByteArray.size_data, String.size_toByteArray] using s.bound)

/-- Decoding the UTF-8 bytes of a text gives back the text. -/
theorem SszString.ofValue_toValue (s : SszString limit) : ofValue (toValue s) = .ok s := by
  have valid : ByteArray.IsValidUTF8 ⟨s.text.toByteArray.data⟩ := s.text.isValidUTF8
  have within : s.text.toByteArray.data.size ≤ limit := by
    simpa [ByteArray.size_data, String.size_toByteArray] using s.bound
  simp only [toValue, ofValue, within, valid, dite_true]
  simp [String.fromUTF8]

/-- A value that decodes to a text holds the UTF-8 bytes of that text. -/
theorem SszString.toValue_of_ofValue {value : Value} {s : SszString limit}
    (made : ofValue value = .ok s) : toValue s = value := by
  cases value <;> simp only [ofValue, reduceCtorEq] at made
  rename_i data
  by_cases within : data.size ≤ limit
  · by_cases valid : ByteArray.IsValidUTF8 ⟨data⟩
    · simp only [within, valid, dite_true, Except.ok.injEq] at made
      subst made
      simp [toValue, String.fromUTF8]
    · simp [within, valid] at made
  · simp [within] at made

/-- Bytes within the limit that are not UTF-8 are refused. -/
theorem SszString.ofValue_bytes_notUtf8 {data : Bytes} (within : data.size ≤ limit)
    (invalid : ¬ ByteArray.IsValidUTF8 ⟨data⟩) :
    ofValue (α := SszString limit) (.bytes data) = .error .notUtf8 := by
  simp [ofValue, within, invalid]

end EthLib.Serialization.Ssz

import EthLib.Serialization.Proofs.Ssz.Merkle.Widths

/-! Count and layout words preserve their information within their stated widths. -/

namespace EthLib.Serialization.Ssz

/-- Equal fixed-width integer encodings contain the same integer when both values fit. -/
theorem uintBytes_injective {width left right : Nat}
    (leftFits : left < 2 ^ (8 * width)) (rightFits : right < 2 ^ (8 * width))
    (same : uintBytes width left = uintBytes width right) : left = right := by
  -- Reading the common byte string recovers each bounded integer exactly.
  have read := congrArg (fun bytes => readUint bytes 0 width) same
  simpa only [readUint_uintBytes width left leftFits, readUint_uintBytes width right rightFits] using read

/-- A 256-bit length word distinguishes every count that fits the SSZ mixing field. -/
theorem lengthWord_injective {left right : Nat}
    (leftFits : left < 2 ^ 256) (rightFits : right < 2 ^ 256)
    (same : lengthWord left = lengthWord right) : left = right := by
  -- A length word is a 32-byte unsigned encoding, so every count below 2^256 is recovered exactly.
  exact uintBytes_injective leftFits rightFits same

/-- Equal layout words preserve every active position within the declared common width. -/
theorem activeFieldsWord_injective {left right : List Bool}
    (sameLength : left.length = right.length) (bounded : left.length ≤ bitsPerChunk)
    (same : activeFieldsWord left = activeFieldsWord right) : left = right := by
  -- Equal words give equal bits, including clear positions between occupied fields.
  apply List.ext_getElem sameLength
  intro position insideLeft insideRight
  -- Select the containing byte, shift the requested bit to the low position, and mask away the other bits.
  have bit := congrArg
    (fun bytes : Bytes => (bytes[position / 8]! >>> UInt8.ofNat (position % 8)) &&& 1 == 1) same
  -- The packed bit at that position is exactly the corresponding active-field flag.
  rw [activeFieldsWord_bit left position (by omega), activeFieldsWord_bit right position (by omega)] at bit
  simpa [insideLeft, insideRight] using bit

/-- Equal layout words carry the same flag at every position of the word, set or clear. -/
theorem activeFieldsWord_flags {left right : List Bool}
    (same : activeFieldsWord left = activeFieldsWord right) {position : Nat}
    (inside : position < bitsPerChunk) :
    left[position]?.getD false = right[position]?.getD false := by
  -- A position past the end of a layout reads as clear, like a gap inside it.
  have bit := congrArg
    (fun bytes : Bytes => (bytes[position / 8]! >>> UInt8.ofNat (position % 8)) &&& 1 == 1) same
  simpa only [activeFieldsWord_bit _ position inside] using bit

/--
Equal layout words come from the same legal layout, whatever the two lengths.
A legal layout ends on a set position, which marks where it stops.
Without that rule, a layout and its copy with clear positions appended would share a word.
-/
theorem activeFieldsWord_injective_of_legal {left right : List Bool}
    (leftEnds : left.getLast? = some true) (rightEnds : right.getLast? = some true)
    (leftBounded : left.length ≤ bitsPerChunk) (rightBounded : right.length ≤ bitsPerChunk)
    (same : activeFieldsWord left = activeFieldsWord right) : left = right := by
  rw [List.getLast?_eq_getElem?] at leftEnds rightEnds
  have ⟨leftInside, _⟩ := List.getElem?_eq_some_iff.mp leftEnds
  have ⟨rightInside, _⟩ := List.getElem?_eq_some_iff.mp rightEnds
  -- Each last position is set in its own layout, so it must be set in the other too.
  have atLeft := activeFieldsWord_flags same (position := left.length - 1) (by omega)
  have atRight := activeFieldsWord_flags same (position := right.length - 1) (by omega)
  rw [leftEnds] at atLeft
  rw [rightEnds] at atRight
  apply activeFieldsWord_injective _ leftBounded same
  -- The shorter layout reads clear at the longer one's last position, which is set.
  rcases Nat.lt_trichotomy left.length right.length with shorter | equal | longer
  · rw [List.getElem?_eq_none (by omega)] at atRight; simp at atRight
  · exact equal
  · rw [List.getElem?_eq_none (by omega)] at atLeft; simp at atLeft

end EthLib.Serialization.Ssz

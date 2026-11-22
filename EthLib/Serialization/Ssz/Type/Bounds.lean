module

public import EthLib.Serialization.Ssz.Type.Desc

/-!
# `Serialization.Ssz.Type.Bounds`

The fewest and the most bytes that an encoding of a type can have.

The request and response protocols of the consensus layer ask a payload to lie within them.

A static type has one size, so its two bounds are equal.

A dynamic type takes its largest size from its limits.

Each variable-size element or field adds an offset of 4 bytes.

No primary source writes these bounds as functions, so EthLib states them, one rule per comment.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The bytes of the offset of one element or field: four when its size can vary, else none. -/
def offsetWidth (shape : Desc) : Nat :=
  if shape.isFixed then 0 else bytesPerOffset

mutual

/-- The fewest bytes that an encoding of the type has. -/
def Desc.minSize : Desc → Nat
  -- A fixed-size type has one size: 1 for a boolean, `N / 8` for uintN, `N` for ByteVector[N].
  | .bool => 1
  | .uint width => width
  | .byteVector length => length
  -- ByteList[N]: the empty list, of no byte.
  | .byteList _ => 0
  -- Bitvector[N]: `ceil(N / 8)` bytes.
  | .bitVector length => (length + 7) / 8
  -- Bitlist[N] and ProgressiveBitlist: the empty list, whose delimiter bit takes one byte.
  | .bitList _ => 1
  | .progressiveBitList _ => 1
  -- Vector[type, N]: `N` elements, each of its fewest bytes, plus 4 if variable-size.
  | .vector element length => length * (element.minSize + offsetWidth element)
  -- List[type, N] and ProgressiveList[type]: the empty list, of no byte.
  | .list _ _ => 0
  | .progressiveList _ _ => 0
  -- A container: each field of its fewest bytes, plus 4 if variable-size.
  | .container _ fields => Desc.fieldsMinSize fields
  | .progressiveContainer _ _ fields => Desc.fieldsMinSize fields
  -- A union: its selector byte, then the smallest of its options.
  | .compatibleUnion _ options => 1 + Desc.optionsMinSize options

/-- The fewest bytes of the fields of a struct, with an offset for each variable field. -/
def Desc.fieldsMinSize : List Desc → Nat
  | [] => 0
  | field :: rest => field.minSize + offsetWidth field + Desc.fieldsMinSize rest

/-- The fewest bytes of the options of a union, 0 for no option. -/
def Desc.optionsMinSize : List Desc → Nat
  | [] => 0
  | [option] => option.minSize
  | option :: rest => min option.minSize (Desc.optionsMinSize rest)

end

mutual

/-- The most bytes that an encoding of the type has, if the type bounds them. -/
def Desc.maxSize : Desc → Option Nat
  -- A fixed-size type has one size: 1 for a boolean, `N / 8` for uintN, `N` for ByteVector[N].
  | .bool => some 1
  | .uint width => some width
  | .byteVector length => some length
  -- ByteList[N]: `N` bytes.
  | .byteList limit => some limit
  -- Bitvector[N]: `ceil(N / 8)` bytes.
  | .bitVector length => some ((length + 7) / 8)
  -- Bitlist[N]: `floor(N / 8) + 1` bytes, since the delimiter bit follows the last data bit.
  | .bitList limit => some ((limit + 8) / 8)
  -- A ProgressiveBitlist: as a Bitlist[N] where a bound `N` is declared, and unbounded otherwise.
  | .progressiveBitList limit => limit.map fun bound => (bound + 8) / 8
  -- Vector[type, N]: `N` elements, each of its most bytes, plus 4 if variable-size.
  | .vector element length => element.maxSize.map fun size => length * (size + offsetWidth element)
  -- List[type, N]: `N` elements, each of its most bytes, plus 4 if variable-size.
  | .list element limit => element.maxSize.map fun size => limit * (size + offsetWidth element)
  -- A ProgressiveList[type]: as a List[type, N] where a bound `N` is declared.
  --
  -- A progressive list without a bound has no largest size.
  | .progressiveList element limit => do
    let bound ← limit
    let size ← element.maxSize
    return bound * (size + offsetWidth element)
  -- A container: each field of its most bytes, plus 4 if variable-size.
  | .container _ fields => Desc.fieldsMaxSize fields
  | .progressiveContainer _ _ fields => Desc.fieldsMaxSize fields
  -- A union: its selector byte, then the largest of its options.
  | .compatibleUnion _ options => (Desc.optionsMaxSize options).map (1 + ·)

/-- The most bytes of the fields of a struct, if every field bounds them. -/
def Desc.fieldsMaxSize : List Desc → Option Nat
  | [] => some 0
  | field :: rest => do
    let size ← field.maxSize
    let remaining ← Desc.fieldsMaxSize rest
    return size + offsetWidth field + remaining

/-- The most bytes of the options of a union, if every option bounds them. -/
def Desc.optionsMaxSize : List Desc → Option Nat
  | [] => some 0
  | option :: rest => do
    let size ← option.maxSize
    let remaining ← Desc.optionsMaxSize rest
    return max size remaining

end

end EthLib.Serialization.Ssz

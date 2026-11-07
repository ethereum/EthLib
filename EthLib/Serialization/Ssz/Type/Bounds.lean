module

public import EthLib.Serialization.Ssz.Type.Desc

/-!
# `Serialization.Ssz.Type.Bounds`

The fewest and the most bytes that an encoding of a type can have.

The request and response protocols of the consensus layer ask a payload to lie within them.

The rule is that of "What are SSZ type size bounds?" in `specs/phase0/p2p-interface.md`.

That file is in `ethereum/consensus-specs`, at `aa16bb4c`:
<https://github.com/ethereum/consensus-specs/blob/aa16bb4c156184e9548a997d53efaf2a228a6304/specs/phase0/p2p-interface.md>

A static type has one size, so its two bounds are equal.

A dynamic type takes its largest size from its limits.

Each variable-size element or field adds an offset of 4 bytes.

No primary source writes these bounds as functions, so the rules below state them.

- A bit list holds a delimiter bit, so it has at least one byte.
- A list, a byte list and a bit list have no elements at least, and at most their limit.
- A progressive list without a limit has no largest size.
- A union is its selector byte, then the smallest or the largest of its options.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The bytes of one element or field: its own, and an offset when its size can vary. -/
def offsetWidth (shape : Desc) : Nat :=
  if shape.isFixed then 0 else bytesPerOffset

mutual

/-- The fewest bytes that an encoding of the type has. -/
def Desc.minSize : Desc → Nat
  | .bool => 1
  | .uint width => width
  | .byteVector length => length
  | .byteList _ => 0
  | .bitVector length => (length + 7) / 8
  -- The delimiter bit takes one byte when the list is empty.
  | .bitList _ => 1
  | .progressiveBitList _ => 1
  | .vector element length => length * (element.minSize + offsetWidth element)
  | .list _ _ => 0
  | .progressiveList _ _ => 0
  | .container _ fields => Desc.fieldsMinSize fields
  | .progressiveContainer _ _ fields => Desc.fieldsMinSize fields
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
  | .bool => some 1
  | .uint width => some width
  | .byteVector length => some length
  | .byteList limit => some limit
  | .bitVector length => some ((length + 7) / 8)
  -- The delimiter bit follows the last data bit.
  | .bitList limit => some ((limit + 8) / 8)
  | .progressiveBitList limit => limit.map fun bound => (bound + 8) / 8
  | .vector element length => element.maxSize.map fun size => length * (size + offsetWidth element)
  | .list element limit => element.maxSize.map fun size => limit * (size + offsetWidth element)
  | .progressiveList element limit => do
    let bound ← limit
    let size ← element.maxSize
    return bound * (size + offsetWidth element)
  | .container _ fields => Desc.fieldsMaxSize fields
  | .progressiveContainer _ _ fields => Desc.fieldsMaxSize fields
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

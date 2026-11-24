module

public import EthLib.Serialization.Ssz.Type.Desc
public import EthLib.Serialization.Ssz.Error

/-!
Declaration validity and compatibility of Merkle layouts.

The core illegal types are stated in EthLib's own terms, one rule per comment.

[EIP-7495][eip7495] and [EIP-8016][eip8016] add the illegal types of their own types.

[EIP-8016][compat] defines when two types have compatible Merkleization.

[eip7495]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7495.md#progressivecontaineractive_fields
[eip8016]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-8016.md#compatibleunionselector-type
[compat]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-8016.md#compatible-merkleization
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The most entries of a layout, so that it fits one 256-bit hash operand.

Source: [EIP-7495, the limit of the active fields][limit].

[limit]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7495.md#why-is-active_fields-limited-to-256-bits
-/
abbrev maxActiveFields : Nat := 256

/-- The byte-array shape a type spells, either spelling, or none for any other shape. -/
inductive ByteShape where
  /-- A fixed count of bytes, however it was written. -/
  | asVector (length : Nat)
  /-- A bounded count of bytes, however it was written. -/
  | asList (limit : Nat)
  deriving BEq, ReflBEq, LawfulBEq

/-- How a type spells a byte array, if it spells one at all. -/
def Desc.byteSequence : Desc → Option ByteShape
  -- ByteVector[N] is Vector[byte, N], and EIP-8016 makes byte compatible with uint8.
  | .byteVector length => some (.asVector length)
  -- A sequence of single bytes is the same shape as a byte array of that width.
  | .vector (.uint 1) length => some (.asVector length)
  -- ByteList[N] is List[byte, N], so the same holds.
  | .byteList limit => some (.asList limit)
  | .list (.uint 1) limit => some (.asList limit)
  -- A progressive list of bytes hangs its bytes on a spine, which no byte array's tree is.
  | _ => none

/-- Layout position of each field of a progressive container, paired with its name. -/
def placedFields (active : List Bool) (names : List String) : List (Nat × String) :=
  (active.zipIdx.filterMap fun (present, position) => if present then some position else none).zip names

/--
The ordinal each field of a layout takes among the fields, paired with its position.

Both are needed: the position addresses the tree, and the ordinal indexes the field list.
-/
def placedOrdinals (active : List Bool) (names : List String) : List (Nat × String × Nat) :=
  (placedFields active names).zipIdx.map fun ((position, name), ordinal) =>
    (position, name, ordinal)

mutual

/--
Whether two types use compatible Merkle layouts.

Reflexive and symmetric, but not transitive.

Two layouts may each agree with a third on shared positions and still clash.

The budget is the nesting of the two types, which is more than the walk can spend.
-/
def compatibleAt : Nat → Desc → Desc → Bool
  | 0, _, _ => false
  | budget + 1, left, right =>
    -- EIP-8016: types are compatible with themselves.
    if left == right then true
    else match left.byteSequence, right.byteSequence with
    -- A byte array and a sequence of single bytes are one shape, outranking what follows.
    | none, none =>
      match left, right with
      -- A basic type is compatible with itself only.
      | .bool, .bool => true
      | .uint a, .uint b => a == b
      -- EIP-8016: Bitvector[N] are compatible if they share the same capacity `N`.
      --
      -- No two of the three bitfield shapes agree, whatever capacity each declares.
      | .bitVector a, .bitVector b => a == b
      -- EIP-8016: Bitlist[N] are compatible if they share the same capacity `N`.
      | .bitList a, .bitList b => a == b
      -- EIP-8016: a ProgressiveBitlist is compatible with itself, by its first rule.
      --
      -- A bound never reaches the tree, so any two progressive bitfields agree on one.
      | .progressiveBitList _, .progressiveBitList _ => true
      -- EIP-8016: Vector[type, N] are compatible if type is compatible and `N` is shared.
      | .vector leftElement a, .vector rightElement b =>
        a == b && compatibleAt budget leftElement rightElement
      -- EIP-8016: List[type, N] are compatible if type is compatible and `N` is shared.
      | .list leftElement a, .list rightElement b =>
        a == b && compatibleAt budget leftElement rightElement
      -- EIP-8016: ProgressiveList[type] are compatible if type is compatible.
      --
      -- A bound never reaches the tree, so the two bounds may differ.
      | .progressiveList leftElement _, .progressiveList rightElement _ =>
        compatibleAt budget leftElement rightElement
      -- EIP-8016: Container are compatible if they share the same field names in the same order.
      --
      -- All their field types are compatible as well.
      | .container leftNames leftFields, .container rightNames rightFields =>
        leftNames == rightNames && fieldsCompatible budget leftFields rightFields
      -- EIP-8016: ProgressiveContainer are compatible by the layout rule below.
      --
      -- A progressive container answers for the positions its layout sets, not its width.
      | .progressiveContainer leftActive leftNames leftFields,
        .progressiveContainer rightActive rightNames rightFields =>
        layoutsAgree budget leftActive leftNames leftFields rightActive rightNames rightFields
      -- EIP-8016: CompatibleUnion are compatible if all options across both are compatible.
      | .compatibleUnion _ leftOptions, .compatibleUnion _ rightOptions =>
        unionOptionsAgree budget leftOptions rightOptions
      -- EIP-8016: all other types are incompatible.
      | _, _ => false
    -- EIP-8016: byte is compatible with uint8, so a byte array and a sequence of uint8 agree.
    --
    -- They agree when both are fixed of one length, or both bounded by one limit.
    | leftBytes, rightBytes => leftBytes == rightBytes
termination_by budget => (budget, 0, 0)

/-- Whether two field lists pair one to one, each pair compatible. -/
def fieldsCompatible : Nat → List Desc → List Desc → Bool
  | _, [], [] => true
  | budget, left :: leftRest, right :: rightRest =>
    compatibleAt budget left right && fieldsCompatible budget leftRest rightRest
  | _, _, _ => false
termination_by budget left right => (budget, 2, sizeOf left + sizeOf right)

/-- Whether every option of one union fits every option of the other. -/
def unionOptionsAgree : Nat → List Desc → List Desc → Bool
  | _, [], _ => true
  | budget, option :: rest, options =>
    -- Compatibility is not transitive, so one pair says nothing about the rest.
    optionAgainstAll budget option options && unionOptionsAgree budget rest options
termination_by budget left right => (budget, 2, sizeOf left + sizeOf right)

/-- Whether one option fits every option of another union. -/
def optionAgainstAll : Nat → Desc → List Desc → Bool
  | _, _, [] => true
  | budget, option, other :: rest =>
    compatibleAt budget option other && optionAgainstAll budget option rest
termination_by budget _ options => (budget, 1, sizeOf options)

/--
Whether two field layouts place the fields they share alike.

A position set in both layouts must hold one field name, of compatible types.

A name set in both must sit at one position.

That does not follow from the first rule, since one name can sit at two positions.

A position set in only one layout is free, the other leaving a zero leaf there.

These are the rules of EIP-8016 for two progressive containers.

Its rule on set entries is read as binding only the positions set in both layouts.
-/
def layoutsAgree (budget : Nat) (leftActive : List Bool) (leftNames : List String)
    (leftFields : List Desc) (rightActive : List Bool) (rightNames : List String)
    (rightFields : List Desc) : Bool :=
  (placedOrdinals leftActive leftNames).all fun left =>
    (placedOrdinals rightActive rightNames).all fun right =>
      layoutPairAgree budget leftFields rightFields left right
termination_by (budget, 3, 0)

/--
Shared positions require the same name and compatible types.

Distinct positions require distinct names.
-/
def layoutPairAgree (budget : Nat) (leftFields rightFields : List Desc)
    (left right : Nat × String × Nat) : Bool :=
  -- A position set in both layouts holds one field name, of compatible types.
  if left.1 == right.1 then
    left.2.1 == right.2.1 &&
      match leftFields[left.2.2]?, rightFields[right.2.2]? with
      | some leftField, some rightField => compatibleAt budget leftField rightField
      | _, _ => false
  else
    -- EIP-8016: no other field name is shared across both types.
    --
    -- Moving a field name changes its generalized index even when its type stays the same.
    left.2.1 != right.2.1
termination_by (budget, 1, 0)


end

/-- Whether two types use compatible Merkle layouts. -/
def isCompatible (left right : Desc) : Bool :=
  -- The walk descends one level of each type at a time, so their nesting bounds it.
  compatibleAt (left.nesting + right.nesting) left right

/-- The first entry that also appears later in a declaration. -/
def firstDuplicate {α : Type} [BEq α] : List α → Option α
  | [] => none
  | item :: rest =>
    -- A repeated key would give one name or selector two meanings.
    if rest.contains item then some item else firstDuplicate rest

mutual

/--
Whether a declaration names a real type, and what it broke if it does not.

Most rules here are the illegal types of SSZ, and of the EIPs for progressive containers and unions.

A few more are EthLib's own, and keep one field name or selector from meaning two things.

The proofs of the codec and the trees assume these rules.
-/
def Desc.wellFormed : Desc → Except Err Unit
  -- SSZ defines uintN for N in 8, 16, 32, 64, 128 and 256, so six byte widths and no others.
  | .uint width =>
    if [1, 2, 4, 8, 16, 32].contains width then .ok () else .error (.uintWidth width)
  -- Illegal: a Vector[type, N] with `N = 0`, since an empty vector names no tree.
  --
  -- A vector is legal only when its element type is.
  | .vector element length => do
    if length == 0 then throw .vectorEmpty
    element.wellFormed
  -- Illegal: Bitvector[0], and ByteVector[0], which is Vector[byte, 0].
  --
  -- A fixed count of nothing encodes to nothing, which no count of them could recover.
  | .bitVector length => if length == 0 then .error .vectorEmpty else .ok ()
  | .byteVector length => if length == 0 then .error .vectorEmpty else .ok ()
  -- A list and a progressive list are legal only when their element type is.
  | .list element _ => element.wellFormed
  | .progressiveList element _ => element.wellFormed
  | .container names fields => do
    -- Illegal: a Container with no fields.
    --
    -- A struct of no fields encodes to nothing, whatever value it holds.
    --
    -- A shape encoding to nothing at every value would let two values share one encoding.
    if fields.isEmpty then throw .containerEmpty
    -- EthLib's own: names are data here, so every field needs exactly one name.
    if names.length != fields.length then throw (.layoutFieldCount names.length fields.length)
    -- EthLib's own: unique names make field lookup unambiguous.
    if (firstDuplicate names).isSome then throw .badDeclaration
    -- A container is legal only when all its field types are.
    Desc.allWellFormed fields
  | .progressiveContainer active names fields => do
    -- EthLib's own: an empty layout is refused first, under an error of its own.
    --
    -- EIP-7495 makes it illegal too, with no fields or with fewer entries `1` than fields.
    if active.isEmpty then throw .layoutWidth
    -- EIP-7495: a layout ending in `0` is illegal.
    if active.getLast? == some false then throw .layoutTrailingGap
    -- EIP-7495: a layout of more than 256 entries is illegal.
    if active.length > maxActiveFields then
      throw (.layoutTooWide active.length maxActiveFields)
    -- EIP-7495: a ProgressiveContainer with no fields is illegal.
    if fields.isEmpty then throw .containerEmpty
    -- EIP-7495: a layout whose count of `1` differs from the count of fields is illegal.
    let set := active.countP (· == true)
    if set != fields.length then throw (.layoutFieldCount set fields.length)
    -- EthLib's own: names are data here, so every field needs exactly one name.
    if names.length != fields.length then throw (.layoutFieldCount names.length fields.length)
    -- EthLib's own: unique names make field lookup unambiguous.
    if (firstDuplicate names).isSome then throw .badDeclaration
    -- A progressive container is legal only when all its field types are.
    Desc.allWellFormed fields
  | .compatibleUnion selectors options => do
    -- EIP-8016: a union without any type options is illegal.
    if selectors.isEmpty || options.isEmpty then throw .unionEmpty
    -- EthLib's own: EIP-8016 writes a map from selectors to types, and EthLib writes two lists.
    --
    -- So EthLib checks what a map gives for free: one option per selector, and no repeated one.
    if selectors.length != options.length then throw .badDeclaration
    -- Repeated selectors would let one tag identify different payload types.
    if let some selector := firstDuplicate selectors then
      throw (.unionSelectorRepeated selector)
    -- EIP-8016: a selector outside 1 to 127 is illegal.
    match selectors.find? (fun selector => selector < minSelector || selector > maxSelector) with
    | some selector => throw (.unionSelectorRange selector minSelector maxSelector)
    | none => pure ()
    -- A union is legal only when all its option types are.
    Desc.allWellFormed options
    -- EIP-8016: two options whose trees are not compatible make the union illegal.
    --
    -- Every pair of options must merkleize alike, which is what makes one tree serve all.
    Desc.optionsCompatible selectors options
  -- A boolean, a byte list, a bitlist and a progressive bitlist are always legal.
  | _ => .ok ()

/-- Whether every type in a list names a real type. -/
def Desc.allWellFormed : List Desc → Except Err Unit
  | [] => .ok ()
  | shape :: rest => do
    shape.wellFormed
    Desc.allWellFormed rest

/-- Whether every pair of a union's options merkleizes alike. -/
def Desc.optionsCompatible : List Nat → List Desc → Except Err Unit
  | _, [] => .ok ()
  | selectors, option :: rest => do
    -- This option is checked against every later one, so each pair is checked once.
    match (List.range rest.length).find? (fun slot => !(rest[slot]?.all (isCompatible option))) with
    | some slot => throw (.unionIncompatible (selectors.headD 0) (selectors.getD (slot + 1) 0))
    | none => pure ()
    Desc.optionsCompatible (selectors.drop 1) rest

end

end EthLib.Serialization.Ssz

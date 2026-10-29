import EthLib.Serialization.Ssz.Type.Desc
import EthLib.Serialization.Ssz.Codec.Error

/-! Declaration validity and compatibility of Merkle layouts. -/

namespace EthLib.Serialization.Ssz

/-- A layout fits one 256-bit hash operand, as required by [EIP-7495](https://eips.ethereum.org/EIPS/eip-7495). -/
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
  | .byteVector length => some (.asVector length)
  -- A sequence of single bytes is the same shape as a byte array of that width.
  | .vector (.uint 1) length => some (.asVector length)
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
    if left == right then true
    else match left.byteSequence, right.byteSequence with
    -- A byte array and a sequence of single bytes are one shape, outranking what follows.
    | none, none =>
      match left, right with
      | .bool, .bool => true
      | .uint a, .uint b => a == b
      -- No two of the three bitfield shapes agree, whatever capacity each declares.
      | .bitVector a, .bitVector b => a == b
      | .bitList a, .bitList b => a == b
      -- A bound never reaches the tree, so any two progressive bitfields agree on one.
      | .progressiveBitList _, .progressiveBitList _ => true
      | .vector leftElement a, .vector rightElement b =>
        a == b && compatibleAt budget leftElement rightElement
      | .list leftElement a, .list rightElement b =>
        a == b && compatibleAt budget leftElement rightElement
      | .progressiveList leftElement _, .progressiveList rightElement _ =>
        compatibleAt budget leftElement rightElement
      | .container leftNames leftFields, .container rightNames rightFields =>
        leftNames == rightNames && fieldsCompatible budget leftFields rightFields
      -- A progressive container answers for the positions its layout sets, not its width.
      | .progressiveContainer leftActive leftNames leftFields,
        .progressiveContainer rightActive rightNames rightFields =>
        layoutsAgree budget leftActive leftNames leftFields rightActive rightNames rightFields
      | .compatibleUnion _ leftOptions, .compatibleUnion _ rightOptions =>
        unionOptionsAgree budget leftOptions rightOptions
      | _, _ => false
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
  if left.1 == right.1 then
    left.2.1 == right.2.1 &&
      match leftFields[left.2.2]?, rightFields[right.2.2]? with
      | some leftField, some rightField => compatibleAt budget leftField rightField
      | _, _ => false
  else
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

Most rules here are ones the specification lists under illegal types.

The others come from the EIPs for progressive containers and unions.
A few more keep one field name or selector from meaning two things.

The proofs of the codec and the trees assume these rules.
For example, a shape encoding to nothing at every value would let two values share one encoding.
-/
def Desc.wellFormed : Desc → Except Err Unit
  -- SSZ defines unsigned integers at six widths and no others.
  | .uint width =>
    if [1, 2, 4, 8, 16, 32].contains width then .ok () else .error (.uintWidth width)
  -- A vector holds at least one element, an empty one naming no tree.
  | .vector element length => do
    if length == 0 then throw .vectorEmpty
    element.wellFormed
  -- A fixed count of nothing encodes to nothing, which no count of them could recover.
  | .bitVector length => if length == 0 then .error .vectorEmpty else .ok ()
  | .byteVector length => if length == 0 then .error .vectorEmpty else .ok ()
  | .list element _ => element.wellFormed
  | .progressiveList element _ => element.wellFormed
  | .container names fields => do
    -- A struct of no fields encodes to nothing, whatever value it holds.
    if fields.isEmpty then throw .containerEmpty
    -- Every field needs exactly one name, with no ignored names or unnamed fields.
    if names.length != fields.length then throw (.layoutFieldCount names.length fields.length)
    -- Unique names make field lookup unambiguous.
    if (firstDuplicate names).isSome then throw .badDeclaration
    Desc.allWellFormed fields
  | .progressiveContainer active names fields => do
    -- A layout holds at least one position, and never ends on a gap.
    if active.isEmpty then throw .layoutWidth
    if active.getLast! == false then throw .layoutTrailingGap
    if active.length > maxActiveFields then
      throw (.layoutTooWide active.length maxActiveFields)
    if fields.isEmpty then throw .containerEmpty
    -- Every occupied position corresponds to exactly one declared field.
    let set := active.countP (· == true)
    if set != fields.length then throw (.layoutFieldCount set fields.length)
    -- Every field needs exactly one name, with no ignored names or unnamed fields.
    if names.length != fields.length then throw (.layoutFieldCount names.length fields.length)
    -- Unique names make field lookup unambiguous.
    if (firstDuplicate names).isSome then throw .badDeclaration
    Desc.allWellFormed fields
  | .compatibleUnion selectors options => do
    -- A union declares at least one option, each under a selector of its own.
    if selectors.isEmpty || options.isEmpty then throw .unionEmpty
    -- Every union selector must name exactly one option.
    if selectors.length != options.length then throw .badDeclaration
    -- Repeated selectors would let one tag identify different payload types.
    if let some selector := firstDuplicate selectors then
      throw (.unionSelectorRepeated selector)
    -- Every selector sits in the range the specification reserves for them.
    match selectors.find? (fun selector => selector < minSelector || selector > maxSelector) with
    | some selector => throw (.unionSelectorRange selector minSelector maxSelector)
    | none => pure ()
    Desc.allWellFormed options
    -- Every pair of options must merkleize alike, which is what makes one tree serve all.
    Desc.optionsCompatible selectors options
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
    match (List.range rest.length).find? (fun slot => !isCompatible option rest[slot]!) with
    | some slot => throw (.unionIncompatible (selectors.headD 0) (selectors.getD (slot + 1) 0))
    | none => pure ()
    Desc.optionsCompatible (selectors.drop 1) rest

end

end EthLib.Serialization.Ssz

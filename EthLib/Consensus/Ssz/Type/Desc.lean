/-! The SSZ type universe, written as data. -/

namespace EthLib.Consensus.Ssz

/-- Width of the offset an encoding puts in front of each variable-size part. -/
abbrev bytesPerOffset : Nat := 4

/--
An SSZ type.

Types are data here rather than Lean types.

One definition of serialization or of merkleization then covers the whole universe.
-/
inductive Desc where
  /-- A true or false value. -/
  | bool
  /-- An unsigned integer of the given width in bytes. -/
  | uint (byteWidth : Nat)
  /-- A fixed number of opaque bytes. -/
  | byteVector (length : Nat)
  /-- A variable number of opaque bytes, up to a limit. -/
  | byteList (limit : Nat)
  /-- A fixed number of bits. -/
  | bitVector (length : Nat)
  /-- A variable number of bits, up to a limit. -/
  | bitList (limit : Nat)
  /-- A variable number of bits, up to a limit where one is declared. -/
  | progressiveBitList (limit : Option Nat)
  /-- A fixed number of elements. -/
  | vector (element : Desc) (length : Nat)
  /-- A variable number of elements, up to a limit. -/
  | list (element : Desc) (limit : Nat)
  /-- A variable number of elements, up to a limit where one is declared. -/
  | progressiveList (element : Desc) (limit : Option Nat)
  /-- A fixed sequence of named fields. -/
  | container (names : List String) (fields : List Desc)
  /-- Named fields that keep their tree positions as the set of them changes. -/
  | progressiveContainer (activeFields : List Bool) (names : List String) (fields : List Desc)
  /-- A choice between options that share one tree shape. -/
  | compatibleUnion (selectors : List Nat) (options : List Desc)
  deriving Inhabited

/-- Zero is reserved for possible optional values, per [EIP-8016](https://eips.ethereum.org/EIPS/eip-8016). -/
abbrev minSelector : Nat := 1

/-- The high bit is reserved for future extensions, per [EIP-8016](https://eips.ethereum.org/EIPS/eip-8016). -/
abbrev maxSelector : Nat := 127

/-- Whether a count is within a capacity its shape declares only where it has one. -/
def withinBound : Option Nat → Nat → Bool
  | none, _ => true
  | some bound, count => count ≤ bound

mutual

/-- Structural equality, descending into nested components. -/
def Desc.beq : Desc → Desc → Bool
  | .bool, .bool => true
  | .uint a, .uint b => a == b
  | .byteVector a, .byteVector b => a == b
  | .byteList a, .byteList b => a == b
  | .bitVector a, .bitVector b => a == b
  | .bitList a, .bitList b => a == b
  | .progressiveBitList a, .progressiveBitList b => a == b
  | .vector a n, .vector b m => Desc.beq a b && n == m
  | .list a n, .list b m => Desc.beq a b && n == m
  | .progressiveList a n, .progressiveList b m => Desc.beq a b && n == m
  | .container names fields, .container others types =>
      names == others && Desc.beqList fields types
  | .progressiveContainer active names fields, .progressiveContainer mask others types =>
      active == mask && names == others && Desc.beqList fields types
  | .compatibleUnion selectors options, .compatibleUnion others types =>
      selectors == others && Desc.beqList options types
  | _, _ => false

/-- Pairwise equality of nested components, preserving their order and count. -/
def Desc.beqList : List Desc → List Desc → Bool
  -- Both lists must end together, so extra fields cannot compare equal.
  | [], [] => true
  | x :: xs, y :: ys => Desc.beq x y && Desc.beqList xs ys
  | _, _ => false

end

instance : BEq Desc := ⟨Desc.beq⟩

mutual

/--
Encoded width in bytes, where the type has one.

Nothing is returned for a type whose encoding varies with the value it holds.
-/
def Desc.fixedSize : Desc → Option Nat
  | .bool => some 1
  | .uint width => some width
  | .byteVector length => some length
  -- A fixed bit count still takes whole bytes, so the last one may be part padding.
  | .bitVector length => some ((length + 7) / 8)
  | .vector element length => element.fixedSize.map (· * length)
  | .container _ fields => Desc.fieldsFixedSize fields
  -- A gap contributes no bytes, so only the declared fields are measured.
  | .progressiveContainer _ _ fields => Desc.fieldsFixedSize fields
  | _ => none

/-- Total width of a field list, where every field has one. -/
def Desc.fieldsFixedSize : List Desc → Option Nat
  | [] => some 0
  | field :: rest =>
    match field.fixedSize, Desc.fieldsFixedSize rest with
    | some width, some remaining => some (width + remaining)
    -- One variable field leaves the whole struct variable.
    | _, _ => none

end

mutual

/--
Levels of type nesting, counting this one.

A basic or packed type counts one level, and each enclosing type adds one more.

This bounds how far a path can descend, since each step of a path enters one nested type.
-/
def Desc.nesting : Desc → Nat
  | .vector element _ => element.nesting + 1
  | .list element _ => element.nesting + 1
  | .progressiveList element _ => element.nesting + 1
  | .container _ fields => Desc.deepestNesting fields + 1
  | .progressiveContainer _ _ fields => Desc.deepestNesting fields + 1
  | .compatibleUnion _ options => Desc.deepestNesting options + 1
  -- A basic value and a packed one hold no type below them.
  | _ => 1

/-- The deepest nesting among a list of types. -/
def Desc.deepestNesting : List Desc → Nat
  | [] => 0
  | shape :: rest => max shape.nesting (Desc.deepestNesting rest)

end

/--
The six unsigned integers SSZ defines, named as the specification names them.

A width in a declaration is a byte count, so eight bytes is a sixty-four-bit integer.
-/
def Desc.uint8 : Desc := .uint 1

@[inherit_doc Desc.uint8] def Desc.uint16 : Desc := .uint 2

@[inherit_doc Desc.uint8] def Desc.uint32 : Desc := .uint 4

@[inherit_doc Desc.uint8] def Desc.uint64 : Desc := .uint 8

@[inherit_doc Desc.uint8] def Desc.uint128 : Desc := .uint 16

@[inherit_doc Desc.uint8] def Desc.uint256 : Desc := .uint 32

/-- Whether the type encodes to the same width whatever value it holds. -/
def Desc.isFixed (d : Desc) : Bool := d.fixedSize.isSome

/--
Width of the part of a struct's encoding that comes before the bodies.

A fixed field sits there whole, and a variable one leaves an offset in its place.
-/
def Desc.leadingWidth : List Desc → Nat
  | [] => 0
  | field :: rest => field.fixedSize.getD bytesPerOffset + Desc.leadingWidth rest

end EthLib.Consensus.Ssz

import EthLib.Serialization.Ssz.Type.Desc

/-! Values, and what it means for one to fit a type. -/

namespace EthLib.Serialization.Ssz

/--
An SSZ value, carrying no type of its own.

A value is read against a type rather than being one.

A decoder can then hand back what it read and have the result checked afterwards.
-/
inductive Value where
  /-- A boolean. -/
  | bool (b : Bool)
  /-- An unsigned integer, whose width comes from the type it is read against. -/
  | uint (n : Nat)
  /-- Opaque bytes, for the two byte-array shapes. -/
  | bytes (data : Array UInt8)
  /-- Bits, for the three bitfield shapes. -/
  | bits (data : Array Bool)
  /-- Elements in order, for the sequences and for the structs. -/
  | seq (elements : List Value)
  /-- One option of a union, under the selector it was chosen by. -/
  | union (selector : Nat) (data : Value)
  deriving Inhabited

mutual

/-- Structural equality, descending into nested components. -/
def Value.beq : Value → Value → Bool
  | .bool a, .bool b => a == b
  | .uint a, .uint b => a == b
  | .bytes a, .bytes b => a == b
  | .bits a, .bits b => a == b
  | .seq a, .seq b => Value.beqList a b
  | .union a x, .union b y => a == b && Value.beq x y
  | _, _ => false

/-- Pairwise equality of nested components, preserving their order and count. -/
def Value.beqList : List Value → List Value → Bool
  | [], [] => true
  | x :: xs, y :: ys => Value.beq x y && Value.beqList xs ys
  | _, _ => false

end

instance : BEq Value := ⟨Value.beq⟩

mutual

/--
Whether a value fits a type.

Under a legal declaration, the codec refuses a value that does not fit.

Every value it decodes fits.
-/
def Value.fits : Desc → Value → Bool
  | .bool, .bool _ => true
  | .uint width, .uint n => n < 2 ^ (8 * width)
  | .byteVector length, .bytes data => data.size == length
  | .byteList limit, .bytes data => data.size ≤ limit
  | .bitVector length, .bits data => data.size == length
  | .bitList limit, .bits data => data.size ≤ limit
  | .progressiveBitList limit, .bits data => withinBound limit data.size
  | .vector element length, .seq elements =>
      elements.length == length && Value.allFit element elements
  | .list element limit, .seq elements =>
      elements.length ≤ limit && Value.allFit element elements
  | .progressiveList element limit, .seq elements =>
      withinBound limit elements.length && Value.allFit element elements
  | .container _ fields, .seq elements => Value.fieldsFit fields elements
  -- A struct holds one value per declared field, never one per layout position.
  | .progressiveContainer _ _ fields, .seq elements => Value.fieldsFit fields elements
  | .compatibleUnion selectors options, .union selector data =>
      Value.optionFits selectors options selector data
  | _, _ => false

/-- Whether every element of a sequence fits the one element type. -/
def Value.allFit (element : Desc) : List Value → Bool
  | [] => true
  | value :: rest => Value.fits element value && Value.allFit element rest

/-- Whether a struct's values pair one to one with its fields, each fitting its own. -/
def Value.fieldsFit : List Desc → List Value → Bool
  | [], [] => true
  | field :: fields, value :: values =>
    Value.fits field value && Value.fieldsFit fields values
  | _, _ => false

/-- Whether a union's value fits the option its selector names. -/
def Value.optionFits : List Nat → List Desc → Nat → Value → Bool
  | [], [], _, _ => false
  | chosen :: selectors, option :: options, selector, data =>
      if chosen == selector then Value.fits option data
      else Value.optionFits selectors options selector data
  -- Selectors and options that do not pair up name no union.
  | _, _, _, _ => false

end

end EthLib.Serialization.Ssz

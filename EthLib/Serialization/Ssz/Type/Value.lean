module

public import EthLib.Serialization.Ssz.Type.Desc

/-!
Values, and what it means for one to fit a type.

The core typing rules are stated in EthLib's own terms, one rule per comment.

[EIP-7916][eip7916], [EIP-7495][eip7495] and [EIP-8016][eip8016] add the values of their types.

[eip7916]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7916.md#progressivelisttype-and-progressivebitlist
[eip7495]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7495.md#progressivecontaineractive_fields
[eip8016]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-8016.md#compatibleunionselector-type
-/

@[expose] public section

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
  | bytes (data : ByteArray)
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

/--
Whether a number is an unsigned integer of a byte width, that is, below `2 ^ (8 * width)`.

It holds when no bit of the number lies at or above bit `8 * width`.
-/
def uintFits (width n : Nat) : Bool :=
  -- A shift builds no big power, where a comparison with `2 ^ (8 * width)` would.
  n >>> (8 * width) == 0

/-- A number fits a byte width exactly when it is below `2 ^ (8 * width)`. -/
@[simp] theorem uintFits_iff (width n : Nat) : uintFits width n = true ↔ n < 2 ^ (8 * width) := by
  simp [uintFits, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]

/-- A number does not fit a byte width exactly when it is at least `2 ^ (8 * width)`. -/
@[simp] theorem uintFits_eq_false_iff (width n : Nat) :
    uintFits width n = false ↔ 2 ^ (8 * width) ≤ n := by
  rw [← Bool.not_eq_true, uintFits_iff, Nat.not_lt]

mutual

/--
Whether a value fits a type.

Under a legal declaration, the codec refuses a value that does not fit.

Every value it decodes fits.
-/
def Value.fits : Desc → Value → Bool
  -- boolean: true or false.
  | .bool, .bool _ => true
  -- uintN: an integer `n` with `0 <= n < 2^N`, for a type of `N / 8` bytes.
  | .uint width, .uint n => n < 2 ^ (8 * width)
  -- ByteVector[N]: exactly `N` bytes.
  | .byteVector length, .bytes data => data.size == length
  -- ByteList[N]: at most `N` bytes.
  | .byteList limit, .bytes data => data.size ≤ limit
  -- Bitvector[N]: exactly `N` bits.
  | .bitVector length, .bits data => data.size == length
  -- Bitlist[N]: at most `N` bits.
  | .bitList limit, .bits data => data.size ≤ limit
  -- EIP-7916: a ProgressiveBitlist has any number of bits.
  --
  -- The bound is EthLib's, and holds only where a shape declares one.
  | .progressiveBitList limit, .bits data => withinBound limit data.size
  -- Vector[type, N]: exactly `N` elements, each of the element type.
  | .vector element length, .seq elements =>
      elements.length == length && Value.allFit element elements
  -- List[type, N]: at most `N` elements, each of the element type.
  | .list element limit, .seq elements =>
      elements.length ≤ limit && Value.allFit element elements
  -- EIP-7916: a ProgressiveList[type] has any number of elements, each of the element type.
  --
  -- The bound is EthLib's, and holds only where a shape declares one.
  | .progressiveList element limit, .seq elements =>
      withinBound limit elements.length && Value.allFit element elements
  -- Container: one value per field, in order, each of the type of its field.
  | .container _ fields, .seq elements => Value.fieldsFit fields elements
  -- EIP-7495: a ProgressiveContainer holds its fields as a Container does.
  --
  -- A struct holds one value per declared field, never one per layout position.
  | .progressiveContainer _ _ fields, .seq elements => Value.fieldsFit fields elements
  -- EIP-8016: a CompatibleUnion holds a value of the option its selector names.
  | .compatibleUnion selectors options, .union selector data =>
      Value.optionFits selectors options selector data
  -- A value of the wrong kind for the type does not fit it.
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
  -- A selector that names no option fits nothing.
  | [], [], _, _ => false
  | chosen :: selectors, option :: options, selector, data =>
      if chosen == selector then Value.fits option data
      else Value.optionFits selectors options selector data
  -- Selectors and options that do not pair up name no union.
  | _, _, _, _ => false

end

end EthLib.Serialization.Ssz

module

public import EthLib.Serialization.Ssz.Typed.Basic

/-!
# Typed SSZ values: collections

Vectors, lists, bitfields, progressive lists and progressive bitlists, as Lean types.

A length or a limit is part of the type, so every value of the type fits its SSZ type.

Progressive lists and bitlists follow [EIP-7916](https://eips.ethereum.org/EIPS/eip-7916).
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- `List[α, limit]`: at most `limit` elements. -/
structure SszList (α : Type) (limit : Nat) where
  /-- The elements, in order. -/
  data : Array α
  /-- The count stays within the limit. -/
  bound : data.size ≤ limit
  deriving DecidableEq

/-- `Bitvector[length]`: exactly `length` bits. -/
structure Bitvector (length : Nat) where
  /-- The bits, in order. -/
  bits : Vector Bool length
  deriving DecidableEq

/-- `Bitlist[limit]`: at most `limit` bits. -/
structure Bitlist (limit : Nat) where
  /-- The bits, in order. -/
  bits : Array Bool
  /-- The count stays within the limit. -/
  bound : bits.size ≤ limit
  deriving DecidableEq

/-- `ProgressiveList[α]`: any number of elements, in a tree that grows with them. -/
structure ProgressiveList (α : Type) where
  /-- The elements, in order. -/
  data : Array α
  deriving DecidableEq

/-- `ProgressiveBitlist`: any number of bits, in a tree that grows with them. -/
structure ProgressiveBitlist where
  /-- The bits, in order. -/
  bits : Array Bool
  deriving DecidableEq

namespace SszType

/-- Each element read back as a typed value, in order, pushed onto the elements read so far. -/
def ofElementsOnto {α : Type} [SszType α] : List Value → Array α → Except Err (Array α)
  | [], read => .ok read
  | element :: rest, read =>
    -- A match, not a bind, keeps the call in tail position, so a long list needs no deep stack.
    match ofValue element with
    | .ok item => ofElementsOnto rest (read.push item)
    | .error fault => .error fault

/-- Each element read back as a typed value, in order. -/
def ofElements {α : Type} [SszType α] (elements : List Value) : Except Err (Array α) :=
  ofElementsOnto elements #[]

/--
The bytes so far, then the bytes of each element from index `i` on, one after another.

The loop calls itself last, so it runs in constant stack for any number of elements.
-/
def encodeElementsOnto {α : Type} [SszType α] (elements : Array α) (i : Nat) (out : ByteArray) :
    Except Err ByteArray :=
  if inside : i < elements.size then
    match encode elements[i] with
    | .ok bytes => encodeElementsOnto elements (i + 1) (out ++ bytes)
    | .error fault => .error fault
  else .ok out
termination_by elements.size - i

/--
The bytes of a sequence of fixed-size elements: their bytes, one after another.

They are written into one array, sized once for all the elements.

As in any sequence, a count of bytes that four bytes cannot name is refused.
-/
def encodeFixedElements {α : Type} [SszType α] (elements : Array α) : Except Err ByteArray := do
  let width := (desc α).fixedSize.getD 0
  let out ← encodeElementsOnto elements 0 (ByteArray.emptyWithCapacity (width * elements.size))
  if out.size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow out.size)
  return out

end SszType

open SszType

/-- `Vector[α, length]`. -/
instance {α : Type} [SszType α] {length : Nat} : SszType (Vector α length) where
  desc := .vector (desc α) length
  toValue v := .seq (v.toList.map toValue)
  ofValue
    | .seq elements => do
      let items ← ofElements elements
      if exact : items.size = length then return ⟨items, exact⟩
      else throw (.count length items.size)
    | _ => .error .typeMismatch
  -- Fixed-size elements need no offset table, so their bytes follow one another.
  encode v :=
    if (desc α).isFixed then encodeFixedElements v.toArray
    else do return ⟨← Ssz.serialize (.vector (desc α) length) (.seq (v.toList.map toValue))⟩

instance {α : Type} [SszType α] {limit : Nat} : SszType (SszList α limit) where
  desc := .list (desc α) limit
  toValue l := .seq (l.data.toList.map toValue)
  ofValue
    | .seq elements => do
      let items ← ofElements elements
      if within : items.size ≤ limit then return ⟨items, within⟩
      else throw (.overLimit limit items.size)
    | _ => .error .typeMismatch

/--
`ByteList[limit]`, the alias of `List[byte, limit]`.

It takes precedence over a list of `uint8` elements, which encodes and roots alike.
-/
instance (priority := high) {limit : Nat} : SszType (SszList UInt8 limit) where
  desc := .byteList limit
  toValue l := .bytes l.data
  ofValue
    | .bytes data =>
      if within : data.size ≤ limit then .ok ⟨data, within⟩
      else .error (.overLimit limit data.size)
    | _ => .error .typeMismatch

instance {length : Nat} : SszType (Bitvector length) where
  desc := .bitVector length
  toValue b := .bits b.bits.toArray
  ofValue
    | .bits data =>
      if exact : data.size = length then .ok ⟨⟨data, exact⟩⟩
      else .error (.count length data.size)
    | _ => .error .typeMismatch

instance {limit : Nat} : SszType (Bitlist limit) where
  desc := .bitList limit
  toValue b := .bits b.bits
  ofValue
    | .bits data =>
      if within : data.size ≤ limit then .ok ⟨data, within⟩
      else .error (.overLimit limit data.size)
    | _ => .error .typeMismatch

instance {α : Type} [SszType α] : SszType (ProgressiveList α) where
  desc := .progressiveList (desc α) none
  toValue l := .seq (l.data.toList.map toValue)
  ofValue
    | .seq elements => ProgressiveList.mk <$> ofElements elements
    | _ => .error .typeMismatch

instance : SszType ProgressiveBitlist where
  desc := .progressiveBitList none
  toValue b := .bits b.bits
  ofValue
    | .bits data => .ok ⟨data⟩
    | _ => .error .typeMismatch

end EthLib.Serialization.Ssz

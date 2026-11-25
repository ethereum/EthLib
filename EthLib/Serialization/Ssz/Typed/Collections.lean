module

public import EthLib.Serialization.Ssz.Typed.Basic

/-!
# Typed SSZ values: collections

Vectors, lists, bitfields, progressive lists and progressive bitlists, as Lean types.

A length or a limit is part of the type, so every value of the type fits its SSZ type.

Each type roots as its untyped value, by the SSZ rule of its kind.

The rules are stated in EthLib's own terms, one step per comment.

Progressive lists and bitlists follow [EIP-7916][eip7916].

[eip7916]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7916.md#progressivelisttype-and-progressivebitlist
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
  -- Each element reads against the element type, in order, and the first refusal stops.
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
  -- Fixed-size elements serialize to the concatenation of their serializations, in order.
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
  -- `n` elements of fixed width `w` take `n * w` bytes, so the array is sized once.
  let width := (desc α).fixedSize.getD 0
  let out ← encodeElementsOnto elements 0 (ByteArray.emptyWithCapacity (width * elements.size))
  -- Every SSZ sequence encodes to fewer than `2^32` bytes, since an offset has four bytes.
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
      -- Vector[type, N]: exactly `N` elements.
      Base.exactArray length items (.count length)
    | _ => .error .typeMismatch
  -- Fixed-size elements need no offset table, so their bytes follow one another.
  --
  -- Variable-size elements: the untyped encoder writes the offsets, then the bodies.
  encode v :=
    if (desc α).isFixed then encodeFixedElements v.toArray
    else Ssz.serialize (.vector (desc α) length) (.seq (v.toList.map toValue))

instance {α : Type} [SszType α] {limit : Nat} : SszType (SszList α limit) where
  desc := .list (desc α) limit
  toValue l := .seq (l.data.toList.map toValue)
  ofValue
    | .seq elements => do
      let items ← ofElements elements
      -- List[type, N]: at most `N` elements.
      if within : items.size ≤ limit then return ⟨items, within⟩
      else throw (.overLimit limit items.size)
    | _ => .error .typeMismatch
  -- Fixed-size elements need no offset table, so their bytes follow one another.
  --
  -- Variable-size elements: the untyped encoder writes the offsets, then the bodies.
  encode l :=
    if (desc α).isFixed then encodeFixedElements l.data
    else Ssz.serialize (.list (desc α) limit) (.seq (l.data.toList.map toValue))

/--
`ByteList[limit]`, the alias of `List[byte, limit]`.

It takes precedence over a list of `uint8` elements, which encodes and roots alike.
-/
instance (priority := high) {limit : Nat} : SszType (SszList UInt8 limit) where
  desc := .byteList limit
  toValue l := .bytes ⟨l.data⟩
  ofValue
    | .bytes data =>
      -- ByteList[N]: at most `N` bytes.
      if within : data.size ≤ limit then .ok ⟨data.data, within⟩
      else .error (.overLimit limit data.size)
    | _ => .error .typeMismatch

instance {length : Nat} : SszType (Bitvector length) where
  desc := .bitVector length
  toValue b := .bits b.bits.toArray
  ofValue
    -- Bitvector[N]: exactly `N` bits.
    | .bits data => Bitvector.mk <$> Base.exactArray length data (.count length)
    | _ => .error .typeMismatch

instance {limit : Nat} : SszType (Bitlist limit) where
  desc := .bitList limit
  toValue b := .bits b.bits
  ofValue
    | .bits data =>
      -- Bitlist[N]: at most `N` bits.
      if within : data.size ≤ limit then .ok ⟨data, within⟩
      else .error (.overLimit limit data.size)
    | _ => .error .typeMismatch

instance {α : Type} [SszType α] : SszType (ProgressiveList α) where
  -- EIP-7916: ProgressiveList[type] has no limit, so the type declares none.
  desc := .progressiveList (desc α) none
  toValue l := .seq (l.data.toList.map toValue)
  ofValue
    -- Any number of elements, so no count is refused.
    | .seq elements => ProgressiveList.mk <$> ofElements elements
    | _ => .error .typeMismatch
  -- Fixed-size elements need no offset table, so their bytes follow one another.
  --
  -- Otherwise the encoding is that of a List[type, N], as EIP-7916 states, offsets then bodies.
  encode l :=
    if (desc α).isFixed then encodeFixedElements l.data
    else Ssz.serialize (.progressiveList (desc α) none) (.seq (l.data.toList.map toValue))

instance : SszType ProgressiveBitlist where
  -- EIP-7916: ProgressiveBitlist has no limit, so the type declares none.
  desc := .progressiveBitList none
  toValue b := .bits b.bits
  ofValue
    -- Any number of bits, so no count is refused.
    | .bits data => .ok ⟨data⟩
    | _ => .error .typeMismatch

end EthLib.Serialization.Ssz

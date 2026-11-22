module

public import EthLib.Base.Fork
public import EthLib.Serialization.Ssz.Typed.Collections
public import EthLib.Serialization.Ssz.Typed.Container

/-!
# Typed SSZ values: kinds that a fork changes

A fork can change the SSZ kind of a type and keep its contents.

From that fork on, a list with a limit becomes a progressive list, whose tree grows with it.

A bitlist becomes a progressive bitlist, and a container a progressive container.

One Lean type then holds the value at every fork, and the fork chooses its kind.

Before the switch, each type encodes and roots as the kind it replaces.

The rules are stated in EthLib's own terms, one step per comment.

[EIP-7688][eip7688] makes these changes; at the pinned commit its status is Review.

[eip7688]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7688.md#specification
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Base SszType

/-- A list with a limit before the switch fork, and a progressive list from it on. -/
structure ForkList (switch fork : Fork) (α : Type) (limit : Nat) where
  /-- The elements, in order. -/
  data : Array α
  /-- Before the switch, the count stays within the limit. -/
  bound : fork < switch → data.size ≤ limit

/-- A bitlist with a limit before the switch fork, and a progressive bitlist from it on. -/
structure ForkBitlist (switch fork : Fork) (limit : Nat) where
  /-- The bits, in order. -/
  bits : Array Bool
  /-- Before the switch, the count stays within the limit. -/
  bound : fork < switch → bits.size ≤ limit

/-- The fork-chosen list with the elements of a list with the same limit. -/
def ForkList.ofSszList {switch fork : Fork} {α : Type} {limit : Nat} (l : SszList α limit) :
    ForkList switch fork α limit :=
  ⟨l.data, fun _ => l.bound⟩

/-- The fork-chosen bitlist with the bits of a bitlist with the same limit. -/
def ForkBitlist.ofBitlist {switch fork : Fork} {limit : Nat} (b : Bitlist limit) :
    ForkBitlist switch fork limit :=
  ⟨b.bits, fun _ => b.bound⟩

instance {switch fork : Fork} {α : Type} [DecidableEq α] {limit : Nat} :
    DecidableEq (ForkList switch fork α limit) := fun a b =>
  if same : a.data = b.data then .isTrue (by cases a; cases b; simp_all)
  else .isFalse (fun eq => same (by rw [eq]))

instance {switch fork : Fork} {limit : Nat} : DecidableEq (ForkBitlist switch fork limit) :=
  fun a b =>
    if same : a.bits = b.bits then .isTrue (by cases a; cases b; simp_all)
    else .isFalse (fun eq => same (by rw [eq]))

instance {switch fork : Fork} {α : Type} [SszType α] {limit : Nat} :
    SszType (ForkList switch fork α limit) where
  -- EIP-7688: from the switch, List[type, N] becomes ProgressiveList[type]; before, it is kept.
  desc := if switch ≤ fork then .progressiveList (desc α) none else .list (desc α) limit
  toValue l := .seq (l.data.toList.map toValue)
  ofValue
    | .seq elements => do
      let items ← ofElements elements
      -- Before the switch, at most `N` elements.
      --
      -- From it, EIP-7688 leaves the limit to the application logic, so none is checked here.
      if within : fork < switch → items.size ≤ limit then return ⟨items, within⟩
      else throw (.overLimit limit items.size)
    | _ => .error .typeMismatch
  -- Fixed-size elements need no offset table, so their bytes follow one another.
  --
  -- Otherwise the untyped encoder writes the list of the fork, offsets then bodies.
  --
  -- EIP-7916 serializes a ProgressiveList[type] as a List[type, N], so the bytes do not change.
  encode l :=
    if (desc α).isFixed then encodeFixedElements l.data
    else do
      let shape := if switch ≤ fork then .progressiveList (desc α) none else .list (desc α) limit
      return ⟨← Ssz.serialize shape (.seq (l.data.toList.map toValue))⟩

/-- Bytes: a byte list before the switch, and a progressive list of bytes from it on.

It takes precedence over a list of `uint8` elements. -/
instance (priority := high) {switch fork : Fork} {limit : Nat} :
    SszType (ForkList switch fork UInt8 limit) where
  -- Before the switch, ByteList[N]; from it, ProgressiveByteList, which is ProgressiveList[byte].
  desc := if switch ≤ fork then .progressiveList (desc UInt8) none else .byteList limit
  toValue l := if switch ≤ fork then .seq (l.data.toList.map toValue) else .bytes l.data
  ofValue value :=
    if switch ≤ fork then
      match value with
      | .seq elements => do
        let items ← ofElements elements
        -- From the switch, no limit is checked, as for any list that EIP-7688 converts.
        if within : fork < switch → items.size ≤ limit then return ⟨items, within⟩
        else throw (.overLimit limit items.size)
      | _ => .error .typeMismatch
    else
      match value with
      -- Before the switch, ByteList[N]: at most `N` bytes.
      | .bytes data =>
        if within : fork < switch → data.size ≤ limit then .ok ⟨data, within⟩
        else .error (.overLimit limit data.size)
      | _ => .error .typeMismatch

instance {switch fork : Fork} {limit : Nat} : SszType (ForkBitlist switch fork limit) where
  -- EIP-7688: from the switch, Bitlist[N] becomes ProgressiveBitlist; before, it is kept.
  desc := if switch ≤ fork then .progressiveBitList none else .bitList limit
  toValue b := .bits b.bits
  ofValue
    -- Before the switch, at most `N` bits; from it, the limit is left to the application logic.
    | .bits data =>
      if within : fork < switch → data.size ≤ limit then .ok ⟨data, within⟩
      else .error (.overLimit limit data.size)
    | _ => .error .typeMismatch

/--
A container before the switch fork, and a progressive container from it on.

The layout holds one bit per position, and it applies only from the switch on.
-/
@[instance_reducible]
def SszType.forkContainer {σ β : Type} [SszFields β] (switch fork : Fork) (active : List Bool)
    (names : List String) (fields : σ → β) (build : β → σ) : SszType σ :=
  -- EIP-7688: from the switch, a Container becomes a ProgressiveContainer with the given layout.
  --
  -- EIP-7688 sets one bit per field at the conversion, then appends a 1 for each added field.
  --
  -- A removed field has its bit cleared to 0.
  --
  -- The caller gives that layout.
  if switch ≤ fork then .progressiveContainer active names fields build
  else .container names fields build

end EthLib.Serialization.Ssz

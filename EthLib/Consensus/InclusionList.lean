module

public import EthLib.Consensus.Containers.InclusionList

/-!
# `Consensus.InclusionList`

From Heze: what a node keeps of the inclusion lists it receives, by slot and dependent root.

A node keeps the first list of each committee member, and whether it came in time.

A member that sends a second, different list for the same key is an equivocator.

The lists of equivocators count for nothing.

[EIP-7805](https://eips.ethereum.org/EIPS/eip-7805#il-equivocation) gives these rules.
-/

@[expose] public section

namespace EthLib.Consensus

/-- From Heze: one transaction of an inclusion list, as opaque bytes without a limit. -/
abbrev InclusionListTransaction := Serialization.Ssz.ProgressiveList UInt8

/-- From Heze: a signed inclusion list, with whether it came before the deadline. -/
structure InclusionListEntry where
  /-- The signed list. -/
  signedInclusionList : SignedInclusionList
  /-- Whether the list came before the inclusion list deadline of its slot. -/
  timely : Bool
  deriving DecidableEq

/-- From Heze: the inclusion lists a node keeps, by slot and dependent root.

For each key, the entries keep the order in which they arrived. -/
structure InclusionListStore where
  /-- The first list of each committee member, with the member, in order of arrival. -/
  inclusionLists : Slot → Root → List (ValidatorIndex × InclusionListEntry)
  /-- The members that sent two different lists. -/
  equivocators : Slot → Root → List ValidatorIndex

namespace InclusionListStore

/-- The store of a node that has received no inclusion list. -/
def empty : InclusionListStore := ⟨fun _ _ => [], fun _ _ => []⟩

/-- A map with a new value at one slot and root, read from the old one. -/
def modify {α : Type} (map : Slot → Root → α) (slot : Slot) (root : Root) (change : α → α) :
    Slot → Root → α :=
  fun slot' root' => if slot' = slot ∧ root' = root then change (map slot root) else map slot' root'

/-- The store after a signed inclusion list arrives.

A first list of its member is kept with its timeliness.

A later list of the same member is dropped, and it marks the member when it differs. -/
def process (store : InclusionListStore) (signed : SignedInclusionList) (timely : Bool) :
    InclusionListStore :=
  let list := signed.message
  let member := list.validatorIndex
  match (store.inclusionLists list.slot list.dependentRoot).lookup member with
  | some stored =>
    if stored.signedInclusionList.message = list then store
    else
      { store with
        equivocators := modify store.equivocators list.slot list.dependentRoot
          fun members => if member ∈ members then members else members ++ [member] }
  | none =>
    { store with
      inclusionLists := modify store.inclusionLists list.slot list.dependentRoot
        (· ++ [(member, ⟨signed, timely⟩)]) }

/-- The entries that count at a slot and root: no equivocator's, and only timely ones if asked. -/
def counted (store : InclusionListStore) (slot : Slot) (root : Root) (onlyTimely : Bool) :
    List (ValidatorIndex × InclusionListEntry) :=
  (store.inclusionLists slot root).filter fun (member, entry) =>
    member ∉ store.equivocators slot root && (!onlyTimely || entry.timely)

/-- The transactions of the entries that count, each once.

The source leaves the order open, so here each transaction keeps its first place. -/
def transactions (store : InclusionListStore) (slot : Slot) (root : Root) (onlyTimely : Bool) :
    List InclusionListTransaction :=
  ((store.counted slot root onlyTimely).flatMap fun (_, entry) =>
    entry.signedInclusionList.message.transactions.data.toList).eraseDups

/-- One bit for each seat of a committee, set when the seat's member has an entry that counts. -/
def bits {preset : Preset} (store : InclusionListStore) (committee : InclusionListCommittee preset)
    (slot : Slot) (root : Root) (onlyTimely : Bool) : InclusionListBits preset :=
  ⟨committee.map fun member => (store.counted slot root onlyTimely).any (·.1 == member)⟩

/-- Whether some bits set every bit that the store sets for a committee. -/
def isInclusive {preset : Preset} (store : InclusionListStore)
    (committee : InclusionListCommittee preset) (slot : Slot) (root : Root)
    (bits : InclusionListBits preset) (onlyTimely : Bool) : Bool :=
  let own := store.bits committee slot root onlyTimely
  (List.finRange preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat).all fun i =>
    !own.bits[i] || bits.bits[i]

end InclusionListStore

end EthLib.Consensus

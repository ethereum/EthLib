module

public import EthLib.Consensus.Gossip.Seen
public import EthLib.Networking.Gossip.Validation

/-!
# `Consensus.Gossip.InclusionList`

From Heze: gossip validation of inclusion lists, the topic that [EIP-7805] adds.

A member of the inclusion list committee of a slot sends the transactions it wants included.

Gossip forwards at most two valid lists of a member for a slot and a dependent root.

A second list lets nodes see that the member equivocates, as [IL equivocation] describes.

The list must be for the current slot, with transactions of bytes, within a size limit.

Its dependent block fixes the committee, in its state advanced to the start of the lookahead.

The member must sit on that committee, and must have signed the list.

Some steps of the rule can fail, such as a root, or an addition out of range.

Such a failure is an error rather than an outcome.

[EIP-7805]: https://eips.ethereum.org/EIPS/eip-7805#p2p-changes
[IL equivocation]: https://eips.ethereum.org/EIPS/eip-7805#il-equivocation
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Networking.Gossip

variable {preset : Preset} {fork : Fork}

/-- The total size of the transactions of an inclusion list, in bytes. -/
def InclusionList.transactionsSize (list : InclusionList) : Nat :=
  (list.transactions.data.toList.map (·.data.size)).sum

/-- From Heze: the checks of a signed inclusion list on its topic, at a time in milliseconds. -/
def validateInclusionList (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (signed : SignedInclusionList) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let list := signed.message
  -- IGNORE when the node holds two valid lists of the member for the slot and dependent root.
  --
  -- Gossip forwards up to two lists of each member, as EIP-7805 specifies.
  (ignoreUnless (seen.inclusionListKeys.count (list.slot, list.dependentRoot, list.validatorIndex)
      < 2) "already seen two valid inclusion lists from this validator").andThenM fun _ => do
  -- IGNORE unless the clock is in the slot, with the gossip clock disparity at both ends.
  let current ← store.isCurrentSlot config list.slot currentTimeMs
  (ignoreUnless current "inclusion list is not for the current slot").andThenM fun _ =>
  -- Let `n` be the total size of the transactions of the list, in bytes.
  let size := list.transactionsSize
  -- IGNORE when `n = 0`.
  (ignoreUnless (size != 0) "inclusion list contains no transactions").andThenM fun _ =>
  -- REJECT unless `n` is at most `MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST`.
  --
  -- The size of a list does not exceed a maximum, as EIP-7805 specifies.
  (rejectUnless (size ≤ config.MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST.toNat)
    "inclusion list transactions exceed the maximum size").andThenM fun _ =>
  -- REJECT when a transaction of the list is empty.
  (rejectUnless (list.transactions.data.toList.all (·.data.size != 0))
    "inclusion list contains an empty transaction").andThenM fun _ =>
  -- IGNORE unless the dependent block is known.
  match store.blocks[list.dependentRoot]? with
  | none => return .ignore "dependent block has not been seen"
  | some block =>
  -- IGNORE unless the dependent block has a state, since a block without one failed validation.
  match store.blockStates[list.dependentRoot]? with
  | none => return .ignore "dependent block failed validation"
  | some dependentState => do
  -- Let `e` be the epoch of the slot of the list, and `d` the dependent slot of `e`.
  let epoch := computeEpochAtSlot preset list.slot
  let dependentSlot ← (computeShufflingDependentSlot preset epoch).mapError .arith
  -- REJECT unless the dependent block is at a slot at most `d`.
  (rejectUnless (block.slot ≤ dependentSlot)
    "dependent block is after the shuffling dependent slot").andThenM fun _ => do
  -- IGNORE unless the dependent block is the head, or the parent of a known block after `d`.
  let possible ← store.isValidDependentRoot config list.dependentRoot dependentSlot
  (ignoreUnless possible "dependent block is not a possible dependent block").andThenM
    fun _ => do
  -- The state of the dependent block, advanced to the first slot of the lookahead of `e`.
  --
  -- A state at or past that slot stays as it is.
  let start ← (computeShufflingLookaheadStartSlot preset epoch).mapError .arith
  let state ← lookaheadState config checks dependentState start
  -- REJECT unless the member sits on the inclusion list committee of the slot in that state.
  --
  -- The member is part of the inclusion list committee, as EIP-7805 specifies.
  let committee ← (getInclusionListCommittee state list.slot).mapError .accessor
  (rejectUnless (committee.toList.contains list.validatorIndex)
    "includer is not a member of the committee").andThenM fun _ => do
  -- REJECT unless the member signed the list with its key in that state.
  --
  -- The list is signed by its member, as EIP-7805 specifies.
  let valid ← (isValidInclusionListSignature config state signed).mapError .accessor
  return rejectUnless valid "invalid inclusion list signature"

/-- The keys after a valid inclusion list: one more count for its slot, root and member. -/
def Seen.recordInclusionList (seen : Seen) (signed : SignedInclusionList) : Seen :=
  let list := signed.message
  { seen with
    inclusionListKeys :=
      (list.slot, list.dependentRoot, list.validatorIndex) :: seen.inclusionListKeys }

end EthLib.Consensus

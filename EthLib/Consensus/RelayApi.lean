module

public import EthLib.Consensus.BeaconApi.Spelling
public import EthLib.Consensus.BuilderApi.Bid
public import EthLib.Consensus.Containers.RelayApi

/-!
# `Consensus.RelayApi`

What a relay keeps from the blocks that builders submit, and the bid that it serves from one.

A new submission replaces the previous one with the same builder key, even when it is worth less.

The [submission endpoint] states this rule.

The rule names no slot, so a store here holds the submissions for one slot, and ignores others.

From Bellatrix to Fulu, the relay serves the header of the payload as a bid of the Builder API.

From Deneb the bid carries the commitments to the blobs, by the [Deneb relaying rules].

From Electra it also carries the requests of the submission, by the [Electra bid].

A relay lists for builders the registered proposers of the current and next epoch.

Each entry holds a slot, the index of its proposer and its signed registration: [`responses.yaml`].

A slot whose proposer has no registration has no entry, by [`validators.yaml`].

The source says "scheduled to propose", but not how a relay learns that schedule.

So the rule here holds for any schedule, and from Fulu the lookahead gives one: [EIP-7917].

The data API lists the [delivered payloads] and the [received bids].

Their entries have the types of [`bids.yaml`].

A filter keeps the entries whose fields equal each value that it gives.

The limit and the cursor of a query are not modelled here.

The JSON of a received bid is that of its bid, plus the two timestamps as strings.

This library writes each timestamp in decimal, as the example of [`misc.yaml`] does.

Delivered payloads may also be sorted by value, lowest or highest first, as [`misc.yaml`] says.

[submission endpoint]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/apis/relay/builder/blocks.yaml
[Deneb relaying rules]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/deneb/builder.md#bidding
[Electra bid]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/electra/builder.md#builderbid
[`validators.yaml`]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/apis/relay/builder/validators.yaml
[`responses.yaml`]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/types/responses.yaml
[EIP-7917]: https://eips.ethereum.org/EIPS/eip-7917#specification
[delivered payloads]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/apis/relay/data/proposer_payload_delivered.yaml
[received bids]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/apis/relay/data/builder_blocks_received.yaml
[`bids.yaml`]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/types/bids.yaml
[`misc.yaml`]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/types/misc.yaml
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz BuilderApi

variable {preset : Preset} {fork : Fork}

namespace RelayApi

/-- The latest submission of each builder for one slot. -/
structure SubmissionStore (preset : Preset) (fork : Fork) where
  /-- The slot of the submissions. -/
  slot : Slot
  /-- The submissions, latest first; a submission keeps at most one per builder key. -/
  entries : List (SubmitBlockRequest preset fork) := []

namespace SubmissionStore

/-- The submission kept for a builder key, if any. -/
def get (store : SubmissionStore preset fork) (pubkey : BLSPubkey) :
    Option (SubmitBlockRequest preset fork) :=
  store.entries.find? (·.message.builderPubkey = pubkey)

/-- The store after a submission: it replaces the entry of its builder, whatever their values.

A submission for another slot leaves the store as it was. -/
def submit (store : SubmissionStore preset fork) (request : SubmitBlockRequest preset fork) :
    SubmissionStore preset fork :=
  if request.message.slot = store.slot then
    { store with
      entries := request ::
        store.entries.filter (·.message.builderPubkey ≠ request.message.builderPubkey) }
  else store

end SubmissionStore

/-! ## The validators that a relay lists -/

/-- An entry of the list of validators that a relay serves to builders.

It names a slot, the index of its proposer and the signed registration of that proposer. -/
structure ValidatorsResponseEntry where
  /-- The slot. -/
  slot : Slot
  /-- The index of the validator that proposes in the slot. -/
  validatorIndex : ValidatorIndex
  /-- The signed registration of that validator. -/
  entry : SignedValidatorRegistrationV1
  deriving DecidableEq

instance : SszType ValidatorsResponseEntry :=
  .container ["slot", "validator_index", "entry"]
    (fun e => (e.slot, e.validatorIndex, e.entry))
    (fun (slot, validatorIndex, entry) => ⟨slot, validatorIndex, entry⟩)

/-- The JSON writes the slot and the index as decimal strings, as `Uint64` values of the API. -/
instance : BeaconApi.ApiSpelling ValidatorsResponseEntry := .unmarked

/-- The list of validators that a relay serves to builders. -/
abbrev ValidatorsResponse := List ValidatorsResponseEntry

/-- Whether a slot lies in an epoch or in the next one. -/
def InTwoEpochs (preset : Preset) (epoch : Epoch) (slot : Slot) : Prop :=
  epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ slot.toNat ∧
    slot.toNat < (epoch.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat

/-- Whether a list is what a relay serves for an epoch and the next, by a schedule of proposers.

The schedule gives the proposer of a slot, and the key map gives the key of a validator.

Every entry lies in the two epochs, and names the proposer of its slot and its registration.

Every slot of the two epochs whose proposer has a registration has exactly one entry. -/
structure ValidatorsResponse.Sound (preset : Preset) (schedule : Slot → Option ValidatorIndex)
    (keyOf : ValidatorIndex → Option BLSPubkey) (registry : Registry) (epoch : Epoch)
    (response : ValidatorsResponse) : Prop where
  /-- Each entry lies in the two epochs and names the proposer of its slot and its registration. -/
  listed : ∀ entry ∈ response, InTwoEpochs preset epoch entry.slot ∧
    schedule entry.slot = some entry.validatorIndex ∧
    ∃ key, keyOf entry.validatorIndex = some key ∧ registry.find? key = some entry.entry
  /-- Each slot of the two epochs whose proposer has a registration has exactly one entry. -/
  complete : ∀ slot index key signed, InTwoEpochs preset epoch slot →
    schedule slot = some index → keyOf index = some key → registry.find? key = some signed →
    response.countP (·.slot = slot) = 1

/-- The entries of a schedule for a count of slots from a first slot, in the order of the slots.

A slot number of 2^64 or more, or a slot whose proposer has no key or registration, has no entry. -/
def scheduledEntries (schedule : Slot → Option ValidatorIndex)
    (keyOf : ValidatorIndex → Option BLSPubkey) (registry : Registry) (first count : Nat) :
    ValidatorsResponse :=
  (List.range count).filterMap fun offset =>
    if fits : first + offset < 2 ^ 64 then do
      let slot : Slot := ⟨⟨first + offset, fits⟩⟩
      let index ← schedule slot
      let key ← keyOf index
      let entry ← registry.find? key
      some ⟨slot, index, entry⟩
    else none

/-- The key of the validator at an index of a state, if there is one. -/
def validatorPubkey? (state : BeaconState preset fork) (index : ValidatorIndex) :
    Option BLSPubkey :=
  state.validators.data[index.toNat]?.map (·.pubkey)

/-- The first slot of the current epoch of a state, as a natural number. -/
def currentEpochStart (state : BeaconState preset fork) : Nat :=
  (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat

/-- From Fulu: the proposer of a slot of the current or next epoch, by the lookahead of a state.

Other slots, and slots past the end of the lookahead, have none. -/
def lookaheadSchedule (state : BeaconState preset fork) (fulu : .fusaka ≤ fork) (slot : Slot) :
    Option ValidatorIndex :=
  if currentEpochStart state ≤ slot.toNat ∧
      slot.toNat < currentEpochStart state + 2 * preset.SLOTS_PER_EPOCH.toNat then
    (state.proposerLookahead fulu)[slot.toNat - currentEpochStart state]?
  else none

/-- From Fulu: the list of validators that a relay serves, by the lookahead of its state.

It covers the current and next epoch, in the order of the slots. -/
def validatorsResponse (state : BeaconState preset fork) (fulu : .fusaka ≤ fork)
    (registry : Registry) : ValidatorsResponse :=
  scheduledEntries (lookaheadSchedule state fulu) (validatorPubkey? state) registry
    (currentEpochStart state) (2 * preset.SLOTS_PER_EPOCH.toNat)

/-! ## The data API -/

/-- A payload that a relay delivered to a proposer.

It is the bid trace with the number of the block and the number of its transactions.

A received bid adds two timestamps to it.

The source does not say which field of the payload each number comes from.

So both are fields of the entry, not values computed from the payload. -/
structure BidTraceV2 where
  /-- The bid trace. -/
  trace : BidTrace
  /-- The number of the block. -/
  blockNumber : UInt64
  /-- The number of transactions in the block. -/
  numTx : UInt64
  deriving DecidableEq

/-- The JSON holds the fields of the bid trace, the number of the block and the count, flat. -/
instance : SszType BidTraceV2 :=
  .container (BidTrace.names ++ ["block_number", "num_tx"])
    (fun b => (b.trace.slot, b.trace.parentHash, b.trace.blockHash, b.trace.builderPubkey,
      b.trace.proposerPubkey, b.trace.proposerFeeRecipient, b.trace.gasLimit, b.trace.gasUsed,
      b.trace.value, b.blockNumber, b.numTx))
    (fun (slot, parentHash, blockHash, builderPubkey, proposerPubkey, proposerFeeRecipient,
        gasLimit, gasUsed, value, blockNumber, numTx) =>
      ⟨⟨slot, parentHash, blockHash, builderPubkey, proposerPubkey, proposerFeeRecipient,
        gasLimit, gasUsed, value⟩, blockNumber, numTx⟩)

/-- The JSON writes the integers as decimal strings, as `Uint64` and `Uint256` values of the API. -/
instance : BeaconApi.ApiSpelling BidTraceV2 := .unmarked

/-- A bid that a relay received from a builder: a delivered payload entry with two timestamps.

The source gives each timestamp the type `Int64`, written as a string.

It names them but does not say what they measure. -/
structure BidTraceV2WithTimestamp where
  /-- The bid. -/
  bid : BidTraceV2
  /-- The timestamp under the key `timestamp`. -/
  timestamp : Int64
  /-- The timestamp under the key `timestamp_ms`. -/
  timestampMs : Int64
  deriving DecidableEq

namespace BidTraceV2WithTimestamp

/-- The JSON of a signed integer of 64 bits: its decimal digits, after a minus sign if negative. -/
def int64Json (x : Int64) : Lean.Json :=
  .str (toString x.toInt)

/-- The integer that a text spells as decimal digits, after a minus sign if negative.

Any text gives an integer, so the reader checks that writing it again gives the text back. -/
def decimalInt (text : String) : Int :=
  match text.toList with
  | '-' :: digits => -(Nat.ofDigitChars 10 digits 0 : Int)
  | digits => Nat.ofDigitChars 10 digits 0

/-- The signed integer of 64 bits that a JSON string holds.

Only the string that the writer gives is read, so any other spelling of the number is refused.

The relay source gives the value the type string, so a JSON number is refused as well.

The reader of an unsigned integer accepts a JSON number, by the mapping of SSZ to JSON. -/
def readInt64 : Lean.Json → Except Err Int64
  | .str text =>
    let i := decimalInt text
    if toString i = text ∧ -2 ^ 63 ≤ i ∧ i < 2 ^ 63 then .ok (Int64.ofInt i)
    else .error .typeMismatch
  | _ => .error .typeMismatch

/-- The JSON object of a received bid: the object of the bid, with the two timestamps added. -/
def toJson (entry : BidTraceV2WithTimestamp) : Except Err Lean.Json := do
  let .obj fields ← BeaconApi.toApiJson entry.bid | throw .typeMismatch
  return .obj ((fields.insert "timestamp" (int64Json entry.timestamp)).insert "timestamp_ms"
    (int64Json entry.timestampMs))

/-- The received bid that a JSON object holds.

The reader takes the two timestamps out of the object, then reads the rest as a bid.

So, as for a bid, a key that the source does not declare is refused. -/
def ofJson (document : Lean.Json) : Except Err BidTraceV2WithTimestamp := do
  let .obj fields := document | throw .structNotAnObject
  let some timestamp := (document.getObjVal? "timestamp").toOption
    | throw (.missingField "timestamp")
  let some timestampMs := (document.getObjVal? "timestamp_ms").toOption
    | throw (.missingField "timestamp_ms")
  let bid ← BeaconApi.ofApiJson BidTraceV2 (.obj ((fields.erase "timestamp_ms").erase "timestamp"))
  return ⟨bid, ← readInt64 timestamp, ← readInt64 timestampMs⟩

end BidTraceV2WithTimestamp

/-- The order of the delivered payloads by their value: lowest first, or highest first. -/
inductive OrderBy where
  /-- Lowest value first. -/
  | ascending
  /-- Highest value first. -/
  | descending
  deriving DecidableEq, Repr

namespace OrderBy

/-- The string of an order in a query. -/
def name : OrderBy → String
  | .ascending => "value"
  | .descending => "-value"

/-- The order that a string names, if any. -/
def ofName? : String → Option OrderBy
  | "value" => some .ascending
  | "-value" => some .descending
  | _ => none

end OrderBy

/-- The filters of a query of delivered payloads; an absent filter keeps every payload. -/
structure DeliveredFilter where
  /-- The slot. -/
  slot : Option Slot := none
  /-- The hash of the block. -/
  blockHash : Option Hash32 := none
  /-- The number of the block. -/
  blockNumber : Option UInt64 := none
  /-- The key of the proposer. -/
  proposerPubkey : Option BLSPubkey := none
  /-- The key of the builder. -/
  builderPubkey : Option BLSPubkey := none

/-- Whether a filter keeps a delivered payload: each present filter equals its field. -/
def DeliveredFilter.keeps (filter : DeliveredFilter) (entry : BidTraceV2) : Bool :=
  filter.slot.all (· = entry.trace.slot) &&
    filter.blockHash.all (· = entry.trace.blockHash) &&
    filter.blockNumber.all (· = entry.blockNumber) &&
    filter.proposerPubkey.all (· = entry.trace.proposerPubkey) &&
    filter.builderPubkey.all (· = entry.trace.builderPubkey)

/-- The filters of a query of received bids; an absent filter keeps every bid. -/
structure ReceivedFilter where
  /-- The slot. -/
  slot : Option Slot := none
  /-- The hash of the block. -/
  blockHash : Option Hash32 := none
  /-- The number of the block. -/
  blockNumber : Option UInt64 := none
  /-- The key of the builder. -/
  builderPubkey : Option BLSPubkey := none

/-- Whether a filter keeps a received bid: each present filter equals its field. -/
def ReceivedFilter.keeps (filter : ReceivedFilter) (entry : BidTraceV2WithTimestamp) : Bool :=
  filter.slot.all (· = entry.bid.trace.slot) &&
    filter.blockHash.all (· = entry.bid.trace.blockHash) &&
    filter.blockNumber.all (· = entry.bid.blockNumber) &&
    filter.builderPubkey.all (· = entry.bid.trace.builderPubkey)

/-- Delivered payloads, sorted by value in the given order.

The source does not order payloads of equal value; here they keep their input order. -/
def sortBy (order : OrderBy) (entries : List BidTraceV2) : List BidTraceV2 :=
  match order with
  | .ascending => entries.mergeSort fun a b => a.trace.value ≤ b.trace.value
  | .descending => entries.mergeSort fun a b => b.trace.value ≤ a.trace.value

end RelayApi

/-- From Bellatrix to Fulu: the bid that a relay serves from a submission, under a key.

It holds the header of the payload and the value of the bid trace, which it does not check.

From Deneb it holds the commitments of the blobs bundle, and from Electra the requests.

The relay source does not fix the key that signs the served bid, so it is an argument.

It fails when the header of the payload cannot be computed, which never happens. -/
def SubmitBlockRequest.bid (request : SubmitBlockRequest preset fork)
    (range : HasBuilderApi fork) (pubkey : BLSPubkey) : Except Err (BuilderBid preset fork) :=
  getBid request.executionPayload request.message.value pubkey
    (fun deneb => .ofSszList (request.blobsBundle ⟨deneb, range.2⟩).commitments)
    (fun electra => request.executionRequests ⟨electra, range.2⟩)

end EthLib.Consensus

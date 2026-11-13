module

public import EthLib.Consensus.Containers.BuilderApi
public import EthLib.Serialization.Ssz.Typed.Text

/-!
# `Consensus.Containers.BuilderConfig`

From Gloas, a validator asks its beacon node for a block with a builder configuration.

It lists the builders to ask for bids, each with the terms of its bid.

It also gives the terms of the bids that the node receives on gossip.

A bid's terms say which builders may sign it, and set its floor, its cap and its weight.

The [Beacon API] defines these containers, which never reach a builder.

[Beacon API]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/types/gloas/builder_entry.yaml
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- The most builder entries in a request to produce a block. -/
def MAX_BUILDER_ENTRIES : Nat := 64

/-- The longest URL of a builder entry, in bytes. -/
def MAX_BUILDER_URL_SIZE : Nat := 2048

/-- The most builder keys that one builder entry accepts. -/
def MAX_BUILDER_PUBKEYS : Nat := 64

/-- From Gloas: one builder that the node asks for a bid, and the terms of that bid. -/
structure BuilderEntry where
  /-- Where the request for a bid goes: a URL, held in SSZ as its UTF-8 bytes. -/
  url : SszString MAX_BUILDER_URL_SIZE
  /-- The proposer's authentication of the request, which the node forwards unchanged. -/
  auth : SignedBuilderRequestAuth
  /-- The builder keys whose bids the entry accepts; none means any builder. -/
  builderPubkeys : SszList BLSPubkey MAX_BUILDER_PUBKEYS
  /-- The largest execution payment counted in the value of a bid, in Gwei. -/
  maxExecutionPayment : Gwei
  /-- The smallest value of a bid that the entry accepts, in Gwei. -/
  minBid : Gwei
  /-- The weight of a bid, in percent of its value. -/
  builderBoostFactor : UInt64

instance : SszType BuilderEntry :=
  .container
    ["url", "auth", "builder_pubkeys", "max_execution_payment", "min_bid",
      "builder_boost_factor"]
    (fun e => (e.url, e.auth, e.builderPubkeys, e.maxExecutionPayment, e.minBid,
      e.builderBoostFactor))
    (fun (url, auth, builderPubkeys, maxExecutionPayment, minBid, builderBoostFactor) =>
      ⟨url, auth, builderPubkeys, maxExecutionPayment, minBid, builderBoostFactor⟩)

/-- From Gloas: the builders to ask for bids, and the terms of the bids received on gossip. -/
structure BuilderConfig where
  /-- The smallest value of a bid received on gossip, in Gwei. -/
  minBid : Gwei
  /-- The weight of a bid received on gossip, in percent of its value. -/
  builderBoostFactor : UInt64
  /-- The builders to ask, one entry for each request. -/
  builders : SszList BuilderEntry MAX_BUILDER_ENTRIES

instance : SszType BuilderConfig :=
  .container ["min_bid", "builder_boost_factor", "builders"]
    (fun c => (c.minBid, c.builderBoostFactor, c.builders))
    (fun (minBid, builderBoostFactor, builders) => ⟨minBid, builderBoostFactor, builders⟩)

/-- Whether a builder entry serves a request for a slot.

Its URL and its [authentication data] must not be empty, and its authentication must name the slot.

[authentication data]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/types/gloas/request_auth.yaml
-/
def BuilderEntry.serves (entry : BuilderEntry) (slot : Slot) : Bool :=
  !entry.url.text.isEmpty && entry.auth.message.data.data.size != 0 &&
    entry.auth.message.slot == slot

/-- Whether two builder entries share their URL and their authentication data. -/
def BuilderEntry.sameRequest (a b : BuilderEntry) : Bool :=
  a.url.text == b.url.text && a.auth.message.data.data == b.auth.message.data.data

/-- From Gloas: the terms that apply to a bid.

A bid that the node asked for takes those of its builder entry.

A bid received on gossip takes those of the top of the configuration. -/
structure BidTerms where
  /-- The builder keys that may sign the bid; none means any builder. -/
  builderPubkeys : List BLSPubkey
  /-- The largest execution payment counted in the value of the bid, in Gwei. -/
  maxExecutionPayment : Gwei
  /-- The smallest value of the bid that is accepted, in Gwei. -/
  minBid : Gwei
  /-- The weight of the bid, in percent of its value. -/
  builderBoostFactor : UInt64
  deriving DecidableEq

/-- The terms of a bid that a builder entry asked for. -/
def BuilderEntry.terms (entry : BuilderEntry) : BidTerms :=
  ⟨entry.builderPubkeys.data.toList, entry.maxExecutionPayment, entry.minBid,
    entry.builderBoostFactor⟩

/-- The terms of the bids that a configuration asks for in a request for a slot, in order.

An entry that does not serve the slot gives no bid, and does not fail the request.

The source forbids two entries with one URL and one authentication data.

Of such entries that serve the slot, the first one is kept. -/
def BuilderConfig.entryTerms (config : BuilderConfig) (slot : Slot) : List BidTerms :=
  let usable := config.builders.data.toList.filter (·.serves slot)
  let distinct := usable.foldl (fun kept entry =>
    if kept.any (·.sameRequest entry) then kept else kept ++ [entry]) []
  distinct.map BuilderEntry.terms

/-- The terms of a bid received on gossip.

They accept any builder, and count the whole execution payment. -/
def BuilderConfig.gossipTerms (config : BuilderConfig) : BidTerms :=
  ⟨[], MAX_EXECUTION_PAYMENT, config.minBid, config.builderBoostFactor⟩

end EthLib.Consensus

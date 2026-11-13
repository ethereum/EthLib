module

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

[submission endpoint]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/apis/relay/builder/blocks.yaml
[Deneb relaying rules]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/deneb/builder.md#bidding
[Electra bid]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/electra/builder.md#builderbid
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

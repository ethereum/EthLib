module

public import EthLib.Consensus.BeaconApi.Encoding

/-!
# `Consensus.BeaconApi.Events`

The events that a beacon node sends on its [event stream], and how the stream writes them.

A client subscribes to a list of topics, and receives only the events of those topics.

Each event is a message of a [server-sent event] stream: its topic, then its data as JSON.

The events of objects that the node received and the events of the fork choice share these types.

[event stream]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/eventstream/index.yaml
[server-sent event]: https://html.spec.whatwg.org/multipage/server-sent-events.html#event-stream-interpretation
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean

/-- The topic of an event, one for each name that the source lists. -/
inductive EventTopic where
  /-- A new head, which the source deprecates for the new head with its payload status. -/
  | head
  /-- A new head of the fork choice, with the status of its payload. -/
  | headV2
  /-- A block that the fork choice imported. -/
  | block
  /-- A block that passed the gossip rules of its topic. -/
  | blockGossip
  /-- An attestation that passed the gossip rules of its topic. -/
  | attestation
  /-- A single attestation that passed the gossip rules of its topic. -/
  | singleAttestation
  /-- A voluntary exit that passed the gossip rules of its topic. -/
  | voluntaryExit
  /-- A change of credentials that passed the gossip rules of its topic. -/
  | blsToExecutionChange
  /-- A proposer slashing that passed the gossip rules of its topic. -/
  | proposerSlashing
  /-- An attester slashing that passed the gossip rules of its topic. -/
  | attesterSlashing
  /-- A new finalized checkpoint of the fork choice. -/
  | finalizedCheckpoint
  /-- A new head that does not descend from the old one. -/
  | chainReorg
  /-- A sync contribution that passed the gossip rules of its topic. -/
  | contributionAndProof
  /-- A new latest finality update of the light client. -/
  | lightClientFinalityUpdate
  /-- A new latest optimistic update of the light client. -/
  | lightClientOptimisticUpdate
  /-- The payload attributes for the next proposal. -/
  | payloadAttributes
  /-- A data column sidecar that passed the gossip rules of its topic. -/
  | dataColumnSidecar
  /-- A payload envelope that the fork choice imported. -/
  | executionPayload
  /-- A payload envelope that passed the gossip rules of its topic. -/
  | executionPayloadGossip
  /-- A payload whose data the node found available. -/
  | executionPayloadAvailable
  /-- A payload bid that passed the gossip rules of its topic. -/
  | executionPayloadBid
  /-- A payload attestation that passed the gossip rules of its topic. -/
  | payloadAttestationMessage
  /-- One run of the fast confirmation rule. -/
  | fastConfirmation
  /-- Proposer preferences that passed the gossip rules of their topic. -/
  | proposerPreferences
  deriving DecidableEq, Repr

namespace EventTopic

/-- The name of a topic, as the source writes it. -/
def name : EventTopic → String
  | .head => "head"
  | .headV2 => "head_v2"
  | .block => "block"
  | .blockGossip => "block_gossip"
  | .attestation => "attestation"
  | .singleAttestation => "single_attestation"
  | .voluntaryExit => "voluntary_exit"
  | .blsToExecutionChange => "bls_to_execution_change"
  | .proposerSlashing => "proposer_slashing"
  | .attesterSlashing => "attester_slashing"
  | .finalizedCheckpoint => "finalized_checkpoint"
  | .chainReorg => "chain_reorg"
  | .contributionAndProof => "contribution_and_proof"
  | .lightClientFinalityUpdate => "light_client_finality_update"
  | .lightClientOptimisticUpdate => "light_client_optimistic_update"
  | .payloadAttributes => "payload_attributes"
  | .dataColumnSidecar => "data_column_sidecar"
  | .executionPayload => "execution_payload"
  | .executionPayloadGossip => "execution_payload_gossip"
  | .executionPayloadAvailable => "execution_payload_available"
  | .executionPayloadBid => "execution_payload_bid"
  | .payloadAttestationMessage => "payload_attestation_message"
  | .fastConfirmation => "fast_confirmation"
  | .proposerPreferences => "proposer_preferences"

/-- Every topic, in the order of the source. -/
def all : List EventTopic :=
  [.head, .headV2, .block, .blockGossip, .attestation, .singleAttestation, .voluntaryExit,
   .blsToExecutionChange, .proposerSlashing, .attesterSlashing, .finalizedCheckpoint, .chainReorg,
   .contributionAndProof, .lightClientFinalityUpdate, .lightClientOptimisticUpdate,
   .payloadAttributes, .dataColumnSidecar, .executionPayload, .executionPayloadGossip,
   .executionPayloadAvailable, .executionPayloadBid, .payloadAttestationMessage, .fastConfirmation,
   .proposerPreferences]

/-- The topic that a name gives, if any. -/
def ofName? (text : String) : Option EventTopic :=
  all.find? (·.name == text)

end EventTopic

/-- The topic that a name of a request gives, or an error with code 400 for a name that is none.
-/
def readEventTopic (text : String) : Except ErrorMessage EventTopic :=
  match EventTopic.ofName? text with
  | some topic => .ok topic
  | none => .error { code := 400, message := s!"Invalid topic: {text}" }

/-- The topics of a request, in order, or an error with code 400 for a name that is no topic. -/
def readEventTopics (texts : List String) : Except ErrorMessage (List EventTopic) :=
  texts.mapM readEventTopic

/-- An event: its topic and its data. -/
structure ApiEvent where
  /-- The topic of the event. -/
  topic : EventTopic
  /-- The data of the event, as JSON. -/
  data : Json

namespace ApiEvent

/-- Whether a client that subscribed to some topics receives an event. -/
def subscribed (topics : List EventTopic) (event : ApiEvent) : Bool :=
  topics.contains event.topic

/-- The message of an event in the stream: a line with the topic and a line with the data.

The writer must give the JSON text of the data on one line, as a compact writer does.

A line break in that text would end the data line, so the message would be malformed.

A blank line ends the message. -/
def toStream (write : Json → String) (event : ApiEvent) : String :=
  s!"event: {event.topic.name}\ndata: {write event.data}\n\n"

end ApiEvent

/-- The messages of the events that a client receives, in order. -/
def eventStream (write : Json → String) (topics : List EventTopic) (events : List ApiEvent) :
    String :=
  String.join ((events.filter (·.subscribed topics)).map (·.toStream write))

end EthLib.Consensus.BeaconApi

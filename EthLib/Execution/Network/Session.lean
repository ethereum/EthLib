module

public import EthLib.Execution.Network.Message

/-!
# `Execution.Network.Session`

The rules of an eth session, from [`caps/eth.md`][eth], and when snap may run beside it.

[eth]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md

"Basic Operation" asks each side to send Status first.

The session is active once the peer's Status has arrived, and any other message may then come.

A response repeats the request ID of a request that this node sent, as "Protocol Messages" says.

So the session keeps the requests that no response has answered yet.

A node must not send a transaction twice to one peer, nor back to the peer it came from.

"Transactions (0x02)" states this rule, so the session keeps the hashes sent and received.

"NewBlockHashes (0x01)" and "NewBlock (0x07)" ask a proof-of-stake node to discard them.

The session is that of a proof-of-stake network.

The content of a response is checked apart, by the checks of each message.

The source leaves some reactions open, and the session decides none of them:

- a second Status from the peer gets its own error;
- a response that answers no pending request gets its own error;
- a snap message on a connection without eth is only flagged, by the check of shared capabilities;
- a peer that sends a transaction twice, or back to this node, is accepted.

The session reads every message, sent or received, as one of its negotiated version.

The decoder of that version gives such messages, and the session does not check it again.

A peer that keeps sending NewBlock or NewBlockHashes "should be disconnected", with no count.

So the session only discards each such message.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Networking.Devp2p
open EthLib.Serialization.Rlp

/-- What this node knows of an eth session with one peer. -/
structure EthSession where
  /-- The negotiated version. -/
  version : EthVersion
  /-- The Status of the peer, none until it arrives. -/
  remoteStatus : Option Status
  /-- Whether this node has sent its own Status. -/
  statusSent : Bool
  /-- The requests this node sent that no response has answered yet, oldest first. -/
  pending : List Message
  /-- The hashes of the transactions this node sent in Transactions or PooledTransactions. -/
  sentTxs : List Hash32
  /-- The hashes of the transactions the peer sent in Transactions or PooledTransactions. -/
  receivedTxs : List Hash32

/-- The session at its start, before any message, on a negotiated version. -/
def EthSession.init (version : EthVersion) : EthSession :=
  ⟨version, none, false, [], [], []⟩

/-- What a node does with a message that the session accepts. -/
inductive EthVerdict where
  /-- The node handles the message. -/
  | accept
  /-- The node drops the message, as the source asks of NewBlockHashes and NewBlock. -/
  | discard
  deriving DecidableEq, Repr

/-- Every way the session rejects a received message. -/
inductive EthSessionError where
  /-- A message other than Status came before the peer's Status. -/
  | beforeStatus
  /-- The peer's Status fails the checks of a Status. -/
  | badStatus (error : StatusError)
  /-- A second Status came in an active session.

  The source fixes no reaction to it. -/
  | secondStatus
  /-- A response repeats a request ID that no pending request of the same type has.

  The source fixes no reaction to it in general.

  "Cells (0x15)" asks to disconnect a peer that sends elements it was not asked for. -/
  | unsolicited (requestId : UInt64)
  /-- A BlockRangeUpdate announces a range that starts after it ends. -/
  | badRange (earliest latest : Nat)
  /-- A received transaction has no hash, since its item does not encode.

  An item fails to encode only when a length reaches `2^64`, so no decoded item does. -/
  | transaction (error : RlpError)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

A refused Status carries the code of its own error, from 101.

The other codes start at 701, above every code of the other errors of the eth messages.

A new constructor takes a new code, so that each code keeps its meaning. -/
def EthSessionError.code : EthSessionError → UInt32
  | .beforeStatus => 701
  | .badStatus e => e.code
  | .secondStatus => 702
  | .unsolicited _ => 703
  | .badRange .. => 704
  | .transaction _ => 705

namespace Message

/-- The request ID of a response, and none for every other message. -/
def responseId? : Message → Option UInt64
  | blockHeaders i _ | blockBodies i _ | pooledTransactions i _ | receipts i _ _
  | blockAccessLists i _ | cells i _ _ _ => some i
  | _ => none

/-- Whether a message is a request, which asks the peer for a response. -/
def isRequest : Message → Bool
  | getBlockHeaders .. | getBlockBodies .. | getPooledTransactions .. | getReceipts ..
  | getBlockAccessLists .. | getCells .. => true
  | _ => false

/-- The hashes of the transactions that a Transactions or PooledTransactions message holds.

Every other message holds none. -/
def transactionHashes : Message → Except RlpError (List Hash32)
  | transactions txs | pooledTransactions _ txs => txs.mapM wireHash
  | _ => pure []

end Message

/--
The session after the peer sends the message `m`, and what to do with the message.

The node has the schedule `s`, and its head has a block number and a timestamp.

- Before the peer's Status, only a Status that passes its checks is accepted.
- A second Status gives its own error, and the source fixes no reaction to it.
- NewBlockHashes and NewBlock are discarded.
- A BlockRangeUpdate must announce a valid range.
- A response must answer a pending request, and the oldest one it answers leaves the list.
- The hashes of received transactions join the received ones.
- A received transaction whose item does not encode has no hash, and is rejected.
-/
def receiveEth (s : Schedule) (number timestamp : Nat) (session : EthSession) (m : Message) :
    Except EthSessionError (EthSession × EthVerdict) := do
  match session.remoteStatus with
  | none =>
    let .status status := m | throw .beforeStatus
    (checkStatus session.version s number timestamp status).mapError .badStatus
    return ({ session with remoteStatus := some status }, .accept)
  | some _ =>
    match m with
    | .status _ => throw .secondStatus
    | .newBlockHashes _ | .newBlock .. => return (session, .discard)
    | .blockRangeUpdate r =>
      if r.Valid then return (session, .accept) else throw (.badRange r.earliest r.latest)
    | _ =>
      let pending ← match m.responseId? with
        | none => pure session.pending
        | some i =>
          if session.pending.any (Message.answers · m) then
            pure (session.pending.eraseP (Message.answers · m))
          else throw (.unsolicited i)
      let hashes ← m.transactionHashes.mapError .transaction
      return ({ session with pending, receivedTxs := session.receivedTxs ++ hashes }, .accept)

/--
The session after this node sends the message `m`, or none when the node must not send it.

"Basic Operation" asks each side to send Status first, and the session is active once both have.

Before that, only a Status may be sent.

A Status is never refused, since the source fixes no rule on a second one.

A Transactions message must hold at least one transaction, as "Transactions (0x02)" says.

It is refused when one of its transactions appears twice.

It is refused too when it holds one that this node sent before, or that the peer sent.

In an active session, a PooledTransactions message is never refused for a resend.

The session does not track the requests of the peer, so it does not check what a response answers.

The transactions of both messages are recorded as sent.

A message with a transaction whose item does not encode cannot go on the wire, and is refused.

A request joins the pending ones.
-/
def sendEth (session : EthSession) (m : Message) : Option EthSession :=
  match m, session.statusSent && session.remoteStatus.isSome with
  | .status _, _ => some { session with statusSent := true }
  | _, false => none
  | .transactions _, true => do
    let hashes ← m.transactionHashes.toOption
    if hashes ≠ [] ∧ hashes.Nodup ∧
        ∀ h ∈ hashes, h ∉ session.sentTxs ∧ h ∉ session.receivedTxs then
      some { session with sentTxs := session.sentTxs ++ hashes }
    else none
  | .pooledTransactions .., true => do
    let hashes ← m.transactionHashes.toOption
    some { session with sentTxs := session.sentTxs ++ hashes }
  | _, true =>
    if m.isRequest then some { session with pending := session.pending ++ [m] } else some session

/-- Whether these shared capabilities, with their first IDs, meet the eth requirement of snap.

`caps/snap.md` calls snap "a dependent satellite of eth", in [Relation to eth][rel].

So snap needs some version of eth among the shared capabilities.

[rel]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md#relation-to-eth
-/
def snapAllowed (offsets : List (Capability × Nat)) : Bool :=
  offsets.any fun entry => entry.1.name == ETH_NAME

/-- A message of an eth session, sent by this node or received from the peer. -/
inductive EthEvent where
  /-- This node sends the message. -/
  | sent (m : Message)
  /-- The peer sends the message. -/
  | received (m : Message)

/-- The hashes of the transactions that an event records as sent.

A sent Transactions or PooledTransactions message records its hashes, and every other event none.
-/
def EthEvent.sentHashes : EthEvent → List Hash32
  | .sent m => m.transactionHashes.toOption.getD []
  | .received _ => []

/-- The hashes of the transactions that an event brings from the peer. -/
def EthEvent.receivedHashes : EthEvent → List Hash32
  | .sent _ => []
  | .received m => m.transactionHashes.toOption.getD []

/-- The session after the events in turn, or none when one is refused or rejected.

The node has the schedule `s`, and its head has a block number and a timestamp. -/
def EthSession.run (s : Schedule) (number timestamp : Nat) (session : EthSession)
    (events : List EthEvent) : Option EthSession :=
  events.foldlM (init := session) fun session event =>
    match event with
    | .sent m => sendEth session m
    | .received m => ((receiveEth s number timestamp session m).toOption).map (·.1)

end EthLib.Execution.Network

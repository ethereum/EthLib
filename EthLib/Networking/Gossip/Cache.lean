module

public import EthLib.Base.Bytes
public import EthLib.Networking.Gossip.Rpc

/-!
# `Networking.Gossip.Cache`

The two caches of a gossipsub router: the message cache and the seen cache.

The source is [gossipsub v1.0, section Message Cache][mcache].

[mcache]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.0.md#message-cache
-/

@[expose] public section

namespace EthLib.Networking.Gossip

/-- The ID of a message on the consensus layer: 20 bytes. -/
abbrev MessageId := Vector UInt8 20

/-- The bytes of a message ID, as the IHAVE and IWANT messages carry them. -/
def MessageId.toBytes (id : MessageId) : ByteArray :=
  Base.packBytes id

/-- The message ID of some bytes, if there are exactly 20 of them. -/
def MessageId.ofBytes? (bytes : ByteArray) : Option MessageId :=
  Base.exactBytes? 20 bytes

/-- The message cache: its history windows, the newest first, each with its messages and IDs.

It keeps whole messages, one window per heartbeat. -/
structure MessageCache where
  /-- The windows, the newest first; each lists its messages, the newest first. -/
  windows : List (List (MessageId × Message)) := [[]]
  deriving DecidableEq

/-- The cache with a message added to the current window. -/
def MessageCache.put (cache : MessageCache) (id : MessageId) (m : Message) : MessageCache :=
  -- Message Cache, put: the message joins the current window, the newest one.
  match cache.windows with
  | [] => ⟨[[(id, m)]]⟩
  | window :: older => ⟨((id, m) :: window) :: older⟩

/-- The newest message of an ID in the cache, if any. -/
def MessageCache.get (cache : MessageCache) (id : MessageId) : Option Message :=
  -- Message Cache, get: the message of the ID, if it is still in a window.
  --
  -- EthLib returns the newest one when an ID occurs twice.
  cache.windows.flatten.lookup id

/-- The IDs of the messages of a topic in the newest windows, at most the gossip count of them. -/
def MessageCache.gossipIds (cache : MessageCache) (gossip : Nat) (topic : String) :
    List MessageId :=
  -- Message Cache, gossip IDs: the IDs of the topic in the gossip count of newest windows.
  --
  -- So a message is told of in gossip only while fewer shifts ran than the gossip count.
  ((cache.windows.take gossip).flatten.filter (·.2.topic = topic)).map (·.1)

/-- The cache with a new empty window, keeping at most the history length of windows. -/
def MessageCache.shift (cache : MessageCache) (len : Nat) : MessageCache :=
  -- Message Cache, shift: a new current window, and the windows past the history length go.
  --
  -- So a message stays as many heartbeats as the history length.
  ⟨([] :: cache.windows).take len⟩

/-- The seen cache: each message ID seen, with the time in milliseconds when it was inserted.

It keeps each ID until a lifetime ends.

A caller passes the seen-cache parameter, in seconds, times 1000 as the lifetime.

The source calls it a timed least-recently-used cache, and does not say if a lookup refreshes it. -/
structure SeenCache where
  /-- The IDs, the newest first, each with the time when it was inserted. -/
  entries : List (MessageId × Nat) := []
  deriving DecidableEq

/-- Whether an ID was inserted less than the lifetime before now, both in milliseconds. -/
def SeenCache.contains (cache : SeenCache) (now ttlMs : Nat) (id : MessageId) : Bool :=
  -- Seen recently: inserted at a time `t` with `now < t + ttl`, for the lifetime `ttl`.
  cache.entries.any fun (i, t) => i = id && now < t + ttlMs

/-- The cache with an ID inserted now. -/
def SeenCache.insert (cache : SeenCache) (now : Nat) (id : MessageId) : SeenCache :=
  -- The entry keeps the time of its insertion; EthLib never refreshes it on a lookup.
  ⟨(id, now) :: cache.entries⟩

/-- The cache without the entries inserted at least the lifetime before now. -/
def SeenCache.expire (cache : SeenCache) (now ttlMs : Nat) : SeenCache :=
  -- An entry inserted at `t` stays while `now < t + ttl`, as a lookup reads it.
  ⟨cache.entries.filter fun (_, t) => now < t + ttlMs⟩

end EthLib.Networking.Gossip

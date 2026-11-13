module

public import EthLib.Networking.Gossip.Rpc

/-!
# `Networking.Gossip.Cache`

The two caches of a gossipsub router: the message cache and the seen cache.

The message cache keeps whole messages in history windows, one window per heartbeat.

A message goes into the current window, the newest one.

A shift starts a new window, and drops the windows beyond the history length.

So a message stays as many heartbeats as the history length.

It is told of in gossip only while fewer shifts ran than the gossip count.

The seen cache keeps each message ID with the time when it was inserted, until a lifetime ends.

The source is [gossipsub v1.0, "Message Cache"][mcache].

The source calls the seen cache "a timed least-recently-used cache".

It does not say whether a lookup refreshes the time of an entry.

Here an entry keeps the time when it was inserted.

[mcache]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#message-cache
-/

@[expose] public section

namespace EthLib.Networking.Gossip

/-- The ID of a message on the consensus layer: 20 bytes. -/
abbrev MessageId := Vector UInt8 20

/-- The message cache: its history windows, the newest first, each with its messages and IDs. -/
structure MessageCache where
  /-- The windows, the newest first; each lists its messages, the newest first. -/
  windows : List (List (MessageId × Message)) := [[]]
  deriving DecidableEq

/-- The cache with a message added to the current window. -/
def MessageCache.put (cache : MessageCache) (id : MessageId) (m : Message) : MessageCache :=
  match cache.windows with
  | [] => ⟨[[(id, m)]]⟩
  | window :: older => ⟨((id, m) :: window) :: older⟩

/-- The newest message of an ID in the cache, if any. -/
def MessageCache.get (cache : MessageCache) (id : MessageId) : Option Message :=
  cache.windows.flatten.lookup id

/-- The IDs of the messages of a topic in the newest windows, at most the gossip count of them. -/
def MessageCache.gossipIds (cache : MessageCache) (gossip : Nat) (topic : String) :
    List MessageId :=
  ((cache.windows.take gossip).flatten.filter (·.2.topic = topic)).map (·.1)

/-- The cache with a new empty window, keeping at most the history length of windows. -/
def MessageCache.shift (cache : MessageCache) (len : Nat) : MessageCache :=
  ⟨([] :: cache.windows).take len⟩

/-- The seen cache: each message ID seen, with the time in milliseconds when it was inserted.

A caller passes the seen-cache parameter, in seconds, times 1000 as the lifetime. -/
structure SeenCache where
  /-- The IDs, the newest first, each with the time when it was inserted. -/
  entries : List (MessageId × Nat) := []
  deriving DecidableEq

/-- Whether an ID was inserted less than the lifetime before now, both in milliseconds. -/
def SeenCache.contains (cache : SeenCache) (now ttlMs : Nat) (id : MessageId) : Bool :=
  cache.entries.any fun (i, t) => i = id && now < t + ttlMs

/-- The cache with an ID inserted now. -/
def SeenCache.insert (cache : SeenCache) (now : Nat) (id : MessageId) : SeenCache :=
  ⟨(id, now) :: cache.entries⟩

/-- The cache without the entries inserted at least the lifetime before now. -/
def SeenCache.expire (cache : SeenCache) (now ttlMs : Nat) : SeenCache :=
  ⟨cache.entries.filter fun (_, t) => now < t + ttlMs⟩

end EthLib.Networking.Gossip

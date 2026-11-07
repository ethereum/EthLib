module

public import EthLib.Execution.Network.Protocol
public import EthLib.Execution.State.Account

/-!
# `Execution.Network.Snap`

The snap capability, which a node uses to download the state of a recent block.

The source is [`caps/snap.md`][snap] of the devp2p specifications.

[snap]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md

- snap/1 has the IDs 0x00 to 0x07, as `snap.md` gave them at [`a1d196b`][snap1].
- snap/2, [EIP-8189][eip-8189], status Last Call, removes GetTrieNodes (0x06) and TrieNodes (0x07).
  It keeps their IDs reserved.
  It adds GetBlockAccessLists (0x08) and BlockAccessLists (0x09).

[snap1]: https://github.com/ethereum/devp2p/blob/a1d196b39a9ed2d16e623e1d7a2ba9f3d77ae08f/caps/snap.md

Peers negotiate the version, so the messages depend on the version, not on the fork.

A request ID is a 64-bit integer, as in the eth capability.

An account crosses the wire in its slim form.

There an empty storage root stands for the root of the empty trie.

An empty code hash stands for the hash of empty code.

"Data format" calls them an "empty list", but an empty field in RLP is the empty string `0x80`.

EthLib reads them as that string, as go-ethereum writes them.

That writer is [`state_account.go` at `0d06140`][geth].

The Merkle proofs of a range are carried as lists of trie nodes.

[eip-8189]: https://eips.ethereum.org/EIPS/eip-8189
[geth]: https://github.com/ethereum/go-ethereum/blob/0d061403cf53263b95f9beec48f07046e78e1bed/core/types/state_account.go#L64
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

/-- A version of the snap capability. -/
inductive SnapVersion where
  /-- snap/1: ranges of accounts and slots, byte codes and trie nodes. -/
  | snap1
  /-- snap/2: trie nodes give way to block access lists. -/
  | snap2
  deriving DecidableEq, Repr

namespace SnapVersion

/-- The version number, as a node announces it in Hello. -/
def number : SnapVersion → Nat
  | snap1 => 1
  | snap2 => 2

/-- The version with a number, if EthLib specifies one. -/
def ofNumber? : Nat → Option SnapVersion
  | 1 => some snap1
  | 2 => some snap2
  | _ => none

/-- The number of message IDs of a version: its highest message ID plus one.

snap/2 keeps 0x06 and 0x07 reserved, so its count reaches BlockAccessLists (0x09). -/
def messageCount : SnapVersion → Nat
  | snap1 => 0x08
  | snap2 => 0x0a

end SnapVersion

/-- The name of the capability, `snap` in ASCII. -/
def SNAP_NAME : ByteArray := ⟨#[0x73, 0x6e, 0x61, 0x70]⟩

/-- The capability of a version, as a node lists it in Hello. -/
def SnapVersion.capability (v : SnapVersion) : Networking.Devp2p.Capability := ⟨SNAP_NAME, v.number⟩

/-- The number of message IDs of a capability, for the multiplexing of RLPx.

It is the count of an eth or snap version that EthLib specifies, and 0 for any other. -/
def capabilityLength (c : Networking.Devp2p.Capability) : Nat :=
  if c.name = SNAP_NAME then ((SnapVersion.ofNumber? c.version).map (·.messageCount)).getD 0
  else ethLength c

/-! ## Accounts in slim form -/

/-- The root of the empty trie: the Keccak-256 hash of the RLP empty string. -/
def EMPTY_TRIE_ROOT : Hash32 := Cryptography.Hash.Keccak.keccak256 ⟨#[0x80]⟩

/-- The slim form of an account: the empty root and the empty code hash as empty strings. -/
def slimAccount (account : State.Account) (storageRoot : Hash32) : Item :=
  .list [Codec.toItem account.nonce, Codec.toItem account.balance,
    if storageRoot = EMPTY_TRIE_ROOT then .bytes .empty else Codec.toItem storageRoot,
    if account.codeHash = State.EMPTY_CODE_HASH then .bytes .empty
    else Codec.toItem account.codeHash]

/-- The account and its storage root in slim form.

An empty storage root is the root of the empty trie.

An empty code hash is the hash of empty code. -/
def ofSlimAccount (item : Item) : Except RlpError (State.Account × Hash32) := do
  match ← item.fields 4 with
  | [n, b, r, c] =>
    let root ← if r = .bytes .empty then pure EMPTY_TRIE_ROOT else r.field 2
    let code ← if c = .bytes .empty then pure State.EMPTY_CODE_HASH else c.field 3
    return (⟨← n.field 0, ← b.field 1, code⟩, root)
  | items => throw (.wrongFieldCount 4 items.length)

/-! ## Messages -/

/-- An entry of a range: the hash of its key, the path in the trie, and its data. -/
structure RangeEntry where
  /-- The hash of the account address or of the storage slot key. -/
  hash : Hash32
  /-- The account body in slim form, or the slot data. -/
  data : ByteArray
  deriving DecidableEq

/-- An entry as the RLP list `[hash, data]`. -/
def RangeEntry.toItem (e : RangeEntry) : Item := .list [Codec.toItem e.hash, Codec.toItem e.data]

/-- The entry in the RLP list `[hash, data]`. -/
def RangeEntry.ofItem (item : Item) : Except RlpError RangeEntry := do
  match ← item.fields 2 with
  | [h, d] => return ⟨← h.field 0, ← d.field 1⟩
  | items => throw (.wrongFieldCount 2 items.length)

instance : Codec RangeEntry := ⟨RangeEntry.toItem, RangeEntry.ofItem⟩

/-- A message of the snap capability. -/
inductive SnapMessage where
  /-- GetAccountRange (0x00): `[reqID, rootHash, startingHash, limitHash, responseBytes]`. -/
  | getAccountRange (requestId : UInt64) (root start limit : Hash32) (responseBytes : Nat)
  /-- AccountRange (0x01): `[reqID, [[accHash, accBody], ...], [node, ...]]`. -/
  | accountRange (requestId : UInt64) (accounts : List RangeEntry) (proof : List ByteArray)
  /-- GetStorageRanges (0x02):
  `[reqID, rootHash, [accountHash, ...], startingHash, limitHash, responseBytes]`. -/
  | getStorageRanges (requestId : UInt64) (root : Hash32) (accounts : List Hash32)
      (start limit : ByteArray) (responseBytes : Nat)
  /-- StorageRanges (0x03): `[reqID, [[[slotHash, slotData], ...], ...], [node, ...]]`. -/
  | storageRanges (requestId : UInt64) (slots : List (List RangeEntry)) (proof : List ByteArray)
  /-- GetByteCodes (0x04): `[reqID, [hash, ...], bytes]`. -/
  | getByteCodes (requestId : UInt64) (hashes : List Hash32) (responseBytes : Nat)
  /-- ByteCodes (0x05): `[reqID, [code, ...]]`. -/
  | byteCodes (requestId : UInt64) (codes : List ByteArray)
  /-- GetTrieNodes (0x06) of snap/1: `[reqID, rootHash, [[accPath, slotPath, ...], ...], bytes]`.
  -/
  | getTrieNodes (requestId : UInt64) (root : Hash32) (paths : List (List ByteArray))
      (responseBytes : Nat)
  /-- TrieNodes (0x07) of snap/1: `[reqID, [node, ...]]`. -/
  | trieNodes (requestId : UInt64) (nodes : List ByteArray)
  /-- GetBlockAccessLists (0x08) of snap/2: `[reqID, [hash, ...], bytes]`. -/
  | getBlockAccessLists (requestId : UInt64) (hashes : List Hash32) (responseBytes : Nat)
  /-- BlockAccessLists (0x09) of snap/2: `[reqID, [bal, ...]]`.

  Each access list is its RLP item, or the empty string when the peer does not have it.

  `snap.md` types an entry `B`, but hashes it as `keccak256(rlp.encode(bal))`.

  An access list is an RLP list.

  So EthLib embeds each list as its item, as [EIP-8189][eip-8189] describes the message.

  [eip-8189]: https://eips.ethereum.org/EIPS/eip-8189#specification -/
  | blockAccessLists (requestId : UInt64) (lists : List Item)
  deriving DecidableEq

/-- Every way a snap message can be rejected. -/
inductive SnapError where
  /-- The version does not use the message ID. -/
  | unknownId (id : Nat)
  /-- The data is not RLP of the shape that the message asks for. -/
  | rlp (error : RlpError)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

A new constructor takes a new code, so that each code keeps its meaning. -/
def SnapError.code : SnapError → UInt32
  | .unknownId _ => 1
  | .rlp _ => 2

namespace SnapMessage

/-- The message ID. -/
def id : SnapMessage → Nat
  | getAccountRange .. => 0x00
  | accountRange .. => 0x01
  | getStorageRanges .. => 0x02
  | storageRanges .. => 0x03
  | getByteCodes .. => 0x04
  | byteCodes .. => 0x05
  | getTrieNodes .. => 0x06
  | trieNodes .. => 0x07
  | getBlockAccessLists .. => 0x08
  | blockAccessLists .. => 0x09

/-- The data of the message, as one RLP item. -/
def toItem : SnapMessage → Item
  | getAccountRange i r s l b =>
    .list [Codec.toItem i, Codec.toItem r, Codec.toItem s, Codec.toItem l, Codec.toItem b]
  | accountRange i as p => .list [Codec.toItem i, Codec.toItem as, Codec.toItem p]
  | getStorageRanges i r as s l b =>
    .list [Codec.toItem i, Codec.toItem r, Codec.toItem as, Codec.toItem s, Codec.toItem l,
      Codec.toItem b]
  | storageRanges i ss p => .list [Codec.toItem i, Codec.toItem ss, Codec.toItem p]
  | getByteCodes i hs b => .list [Codec.toItem i, Codec.toItem hs, Codec.toItem b]
  | byteCodes i cs => .list [Codec.toItem i, Codec.toItem cs]
  | getTrieNodes i r ps b => .list [Codec.toItem i, Codec.toItem r, Codec.toItem ps, Codec.toItem b]
  | trieNodes i ns => .list [Codec.toItem i, Codec.toItem ns]
  | getBlockAccessLists i hs b => .list [Codec.toItem i, Codec.toItem hs, Codec.toItem b]
  | blockAccessLists i ls => .list [Codec.toItem i, .list ls]

/-- Whether a version uses a message ID: 0x06 and 0x07 on snap/1, 0x08 and 0x09 on snap/2. -/
def usesId (version : SnapVersion) (id : Nat) : Bool :=
  id < 0x06 || (version = .snap1 && id < 0x08) || (version = .snap2 && 0x08 ≤ id && id < 0x0a)

/-- The message with the ID `id` and the data `item`, on the version `version`. -/
def ofItem (version : SnapVersion) (id : Nat) (item : Item) : Except SnapError SnapMessage := do
  if !usesId version id then throw (.unknownId id)
  Except.mapError .rlp do
    match id, ← item.toItems with
    | 0x00, [i, r, s, l, b] =>
      return getAccountRange (← i.field 0) (← r.field 1) (← s.field 2) (← l.field 3) (← b.field 4)
    | 0x01, [i, as, p] => return accountRange (← i.field 0) (← as.field 1) (← p.field 2)
    | 0x02, [i, r, as, s, l, b] =>
      return getStorageRanges (← i.field 0) (← r.field 1) (← as.field 2) (← s.field 3)
        (← l.field 4) (← b.field 5)
    | 0x03, [i, ss, p] => return storageRanges (← i.field 0) (← ss.field 1) (← p.field 2)
    | 0x04, [i, hs, b] => return getByteCodes (← i.field 0) (← hs.field 1) (← b.field 2)
    | 0x05, [i, cs] => return byteCodes (← i.field 0) (← cs.field 1)
    | 0x06, [i, r, ps, b] =>
      return getTrieNodes (← i.field 0) (← r.field 1) (← ps.field 2) (← b.field 3)
    | 0x07, [i, ns] => return trieNodes (← i.field 0) (← ns.field 1)
    | 0x08, [i, hs, b] => return getBlockAccessLists (← i.field 0) (← hs.field 1) (← b.field 2)
    | 0x09, [i, ls] => return blockAccessLists (← i.field 0) (← ls.toItems.mapError (.inField 1))
    | _, items => throw (.wrongFieldCount (expectedFields id) items.length)
where
  /-- The number of fields of the message with an ID. -/
  expectedFields : Nat → Nat
    | 0x00 => 5
    | 0x02 => 6
    | 0x05 | 0x07 | 0x09 => 2
    | 0x06 => 4
    | _ => 3

/-- The message with the ID `id` whose data is the RLP encoding `data`. -/
def decode (version : SnapVersion) (id : Nat) (data : ByteArray) :
    Except SnapError SnapMessage := do
  ofItem version id (← (Serialization.Rlp.decode data).mapError .rlp)

/-- The RLP encoding of the data of a message. -/
def encode (m : SnapMessage) : Except SnapError ByteArray :=
  (Serialization.Rlp.encode m.toItem).mapError .rlp

/-- The request ID that every snap message carries first. -/
def requestId : SnapMessage → UInt64
  | getAccountRange i .. | accountRange i .. | getStorageRanges i .. | storageRanges i ..
  | getByteCodes i .. | byteCodes i .. | getTrieNodes i .. | trieNodes i ..
  | getBlockAccessLists i .. | blockAccessLists i .. => i

/-- Whether `response` answers `request`.

It is the response type of the request type, and it repeats the request ID. -/
def answers (request response : SnapMessage) : Bool :=
  match request, response with
  | getAccountRange i .., accountRange j .. => i == j
  | getStorageRanges i .., storageRanges j .. => i == j
  | getByteCodes i .., byteCodes j .. => i == j
  | getTrieNodes i .., trieNodes j .. => i == j
  | getBlockAccessLists i .., blockAccessLists j .. => i == j
  | _, _ => false

end SnapMessage

/-! ## Checks of responses -/

/--
Whether the codes of a ByteCodes answer a request of the code hashes `requested`.

The codes come in the order of the request.

The peer skips the codes it does not have, as "GetByteCodes (0x04)" says.

So the hashes of the codes form a sublist of the requested hashes.
-/
def codesAnswer (requested : List Hash32) (codes : List ByteArray) : Bool :=
  (codes.map Cryptography.Hash.Keccak.keccak256).isSublist requested

/--
Whether the access lists of a BlockAccessLists answer a request, by position.

`expected` holds the access list hash of the header of each requested block.

The peer may cut the list short from the tail, as "BlockAccessLists (0x09)" says.

It puts the empty string for a list it does not have, as that section also says.

Every other entry must hash to the access list hash of its block.
-/
def accessListsAnswer (expected : List Hash32) (lists : List Item) : Bool :=
  lists.length ≤ expected.length &&
    (lists.zip expected).all fun (list, hash) =>
      list == .bytes .empty ||
        match Serialization.Rlp.encode list with
        | .ok bytes => Cryptography.Hash.Keccak.keccak256 bytes == hash
        | .error _ => false

end EthLib.Execution.Network

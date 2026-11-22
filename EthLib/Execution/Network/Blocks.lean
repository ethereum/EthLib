module

public import EthLib.Base.Hash32
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Serialization.Rlp.Codec
public import EthLib.Serialization.Rlp.Decode

/-!
# `Execution.Network.Blocks`

The block exchange of the eth capability, from Protocol Messages in [`caps/eth.md`][eth].

[eth]: https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/caps/eth.md#protocol-messages

- GetBlockHeaders (0x03) asks for headers from a start block, with a fixed gap between them.
- BlockHeaders (0x04) answers with the headers it has, at most as many as asked.
- GetBlockBodies (0x05) asks for the bodies of blocks by hash, and BlockBodies (0x06) answers.
- NewBlockHashes (0x01) and NewBlock (0x07) announce blocks.

Since the Merge, a node must discard NewBlockHashes and NewBlock, as EIP-3675 says.

The messages keep their IDs, so a reader still decodes them.

A request carries a request ID, a 64-bit integer, and its response repeats it.

[EIP-2481][eip-2481] adds the request ID.

A header, a body and a block cross the wire as RLP items.

Their fields depend on the fork of each block, so the messages carry them as items.

A header of BlockHeaders also keeps the bytes it was read from, which give its hash.

[eip-2481]: https://eips.ethereum.org/EIPS/eip-2481#specification
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

/-- The message ID of NewBlockHashes. -/
def NEW_BLOCK_HASHES_ID : Nat := 0x01

/-- The message ID of GetBlockHeaders. -/
def GET_BLOCK_HEADERS_ID : Nat := 0x03

/-- The message ID of BlockHeaders. -/
def BLOCK_HEADERS_ID : Nat := 0x04

/-- The message ID of GetBlockBodies. -/
def GET_BLOCK_BODIES_ID : Nat := 0x05

/-- The message ID of BlockBodies. -/
def BLOCK_BODIES_ID : Nat := 0x06

/-- The message ID of NewBlock. -/
def NEW_BLOCK_ID : Nat := 0x07

/-- The block that a request of headers starts from: its number or its hash. -/
inductive BlockId where
  /-- The block with this number.

  `eth.md` writes the number as `P`, with no bound.

  EthLib bounds it below 2^64, a choice of its own.

  So a number never has the 32 bytes of a hash. -/
  | number (n : UInt64)
  /-- The block with this hash. -/
  | hash (h : Hash32)
  deriving DecidableEq, Repr

namespace BlockId

/-- A start block as `{P, B_32}`: a scalar for a number, 32 bytes for a hash. -/
def toItem : BlockId → Item
  -- `startblock: {P, B_32}`.
  | .number n => Codec.toItem n
  | .hash h => Codec.toItem h

/-- The start block in an item: 32 bytes are a hash, and a shorter scalar is a number.

A scalar below 2^64 has at most 8 bytes, so a reader tells the two apart by the length. -/
def ofItem : Item → Except RlpError BlockId
  -- 32 bytes are a hash; a number below `2^64` takes at most 8 bytes, EthLib's own bound.
  | .bytes b =>
    if b.size = 32 then hash <$> Codec.ofItem (.bytes b) else number <$> Codec.ofItem (.bytes b)
  | .list _ => .error .listAsBytes

end BlockId

instance : Codec BlockId := ⟨BlockId.toItem, BlockId.ofItem⟩

/-- A request of headers: `[startblock, limit, skip, reverse]`. -/
structure HeaderRequest where
  /-- The first block of the answer. -/
  start : BlockId
  /-- The most headers that the answer holds. -/
  limit : Nat
  /-- How many blocks lie between two headers of the answer. -/
  skip : Nat
  /-- Whether the numbers fall, rather than rise. -/
  reverse : Bool
  deriving DecidableEq, Repr

/-- A request as the RLP list `[startblock, limit, skip, reverse]`. -/
def HeaderRequest.toItem (r : HeaderRequest) : Item :=
  .list [Codec.toItem r.start, Codec.toItem r.limit, Codec.toItem r.skip, Codec.toItem r.reverse]

/-- The request in the RLP list `[startblock, limit, skip, reverse]`. -/
def HeaderRequest.ofItem (item : Item) : Except RlpError HeaderRequest := do
  -- `[startblock: {P, B_32}, limit: P, skip: P, reverse: {0, 1}]`.
  match ← item.fields 4 with
  | [s, l, k, r] => return ⟨← s.field 0, ← l.field 1, ← k.field 2, ← r.field 3⟩
  | items => throw (.wrongFieldCount 4 items.length)

instance : Codec HeaderRequest := ⟨HeaderRequest.toItem, HeaderRequest.ofItem⟩

/-- A block announced by NewBlockHashes: `[blockhash, number]`. -/
structure BlockAnnouncement where
  /-- The hash of the block. -/
  hash : Hash32
  /-- The number of the block. -/
  number : Nat
  deriving DecidableEq, Repr

/-- An announcement as the RLP list `[blockhash, number]`. -/
def BlockAnnouncement.toItem (a : BlockAnnouncement) : Item :=
  .list [Codec.toItem a.hash, Codec.toItem a.number]

/-- The announcement in the RLP list `[blockhash, number]`. -/
def BlockAnnouncement.ofItem (item : Item) : Except RlpError BlockAnnouncement := do
  -- `[blockhash: B_32, number: P]`.
  match ← item.fields 2 with
  | [h, n] => return ⟨← h.field 0, ← n.field 1⟩
  | items => throw (.wrongFieldCount 2 items.length)

instance : Codec BlockAnnouncement := ⟨BlockAnnouncement.toItem, BlockAnnouncement.ofItem⟩

/-! ## The headers that answer a request -/

/-- The index of the number in a header, the ninth field at every fork. -/
def HEADER_NUMBER_INDEX : Nat := 8

/-- The hash of a header: the Keccak-256 hash of the bytes of its RLP encoding. -/
def headerHash (header : Encoded) : Hash32 :=
  -- `keccak256(header)`, over the bytes the header was read from, so no item is encoded again.
  Cryptography.Hash.Keccak.keccak256 header.bytes

/-- The number of a header, its ninth field. -/
def headerNumber (header : Item) : Except RlpError Nat := do
  -- `number: P`, the ninth field of the header in Block Encoding and Validity.
  let fields ← header.toItems
  match fields[HEADER_NUMBER_INDEX]? with
  | some n => Codec.ofItem n
  | none => throw (.wrongFieldCount (HEADER_NUMBER_INDEX + 1) fields.length)

/-- The index of the difficulty in a header, the eighth field at every fork. -/
def HEADER_DIFFICULTY_INDEX : Nat := 7

/-- The difficulty of a header, its eighth field. -/
def headerDifficulty (header : Item) : Except RlpError Nat := do
  -- `difficulty: P`, the eighth field.
  let fields ← header.toItems
  match fields[HEADER_DIFFICULTY_INDEX]? with
  | some d => Codec.ofItem d
  | none => throw (.wrongFieldCount (HEADER_DIFFICULTY_INDEX + 1) fields.length)

/-- The parent hash of a header, its first field. -/
def headerParent (header : Item) : Except RlpError Hash32 := do
  -- `parent-hash: B_32`, the first field.
  match ← header.toItems with
  | p :: _ => Codec.ofItem p
  | [] => throw (.wrongFieldCount 1 0)

/-- Why the headers of a BlockHeaders do not answer a GetBlockHeaders. -/
inductive HeadersError where
  /-- The answer holds more headers than the limit. -/
  | tooMany (count limit : Nat)
  /-- A header is not a list with a parent hash and a number. -/
  | rlp (error : RlpError)
  /-- The first header is not the start block. -/
  | wrongStart
  /-- A header is not the number of blocks apart from the one before it that was asked. -/
  | wrongNumber (expected got : Nat)
  /-- Two consecutive headers do not chain by their parent hash. -/
  | notChained (number : Nat)
  /-- The response is not BlockHeaders with the request ID of the GetBlockHeaders. -/
  | notAnswer
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 201, above every code of a message error and a Status error.

A new constructor takes a new code, so that each code keeps its meaning. -/
def HeadersError.code : HeadersError → UInt32
  | .tooMany .. => 201
  | .rlp _ => 202
  | .wrongStart => 203
  | .wrongNumber .. => 204
  | .notChained _ => 205
  | .notAnswer => 206

/-- The number that follows `n` in an answer: `skip + 1` blocks later, or earlier if reversed.

A falling answer stops at block 0, so a number below the step has no next number. -/
def HeaderRequest.next (r : HeaderRequest) (n : Nat) : Option Nat :=
  -- `skip` blocks apart, read as `skip` blocks between: a step of `skip + 1`.
  --
  -- Falling when `reverse` is 1, down to block 0.
  if r.reverse then (if r.skip + 1 ≤ n then some (n - (r.skip + 1)) else none)
  -- Rising by `skip + 1` when `reverse` is 0.
  else some (n + r.skip + 1)

/-- Whether the header `b` follows `a` in an answer to `r`.

The section Block Encoding and Validity asks the chain of headers in sequence. -/
def followsIn (r : HeaderRequest) (a b : Encoded) : Except HeadersError Unit := do
  let na ← (headerNumber a.item).mapError .rlp
  let nb ← (headerNumber b.item).mapError .rlp
  -- GetBlockHeaders: the next number is the one `skip + 1` blocks on, in the order of `reverse`.
  if r.next na ≠ some nb then throw (.wrongNumber ((r.next na).getD 0) nb)
  -- Block Encoding and Validity: consecutive headers chain by their parent hash.
  if r.skip = 0 then
    -- In a falling answer the earlier header is the child, in a rising one the later.
    let (child, parent) := if r.reverse then (a, b) else (b, a)
    if (← (headerParent child.item).mapError .rlp) ≠ headerHash parent then
      throw (.notChained nb)

/-- Whether consecutive headers of an answer each follow the one before. -/
def followAll (r : HeaderRequest) : List Encoded → Except HeadersError Unit
  | a :: b :: rest => do followsIn r a b; followAll r (b :: rest)
  | _ => pure ()

/-- Whether a header is the start block of a request, by its number or by its hash. -/
def isStart (start : BlockId) (header : Encoded) : Except HeadersError Bool :=
  match start with
  | .number n => do pure (decide ((← (headerNumber header.item).mapError .rlp) = n.toNat))
  | .hash h => pure (decide (headerHash header = h))

/--
Whether the headers `headers` answer the request `r`, as the section GetBlockHeaders (0x03) says.

The list may be empty, when the peer has none of the blocks.
-/
def checkHeaders (r : HeaderRequest) (headers : List Encoded) : Except HeadersError Unit := do
  -- At most `limit` items.
  if r.limit < headers.length then throw (.tooMany headers.length r.limit)
  -- Beginning at block `startblock`, by number or by hash; an empty list passes.
  if let first :: _ := headers then
    if !(← isStart r.start first) then throw .wrongStart
  -- Then `skip` blocks between consecutive headers, a step of `skip + 1`.
  followAll r headers

end EthLib.Execution.Network

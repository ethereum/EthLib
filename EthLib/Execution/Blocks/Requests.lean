module

public import EthLib.Base.BigEndian
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Execution.Blocks.Log

/-!
# `Blocks.Requests`

The requests that a block sends to the consensus layer, and the hash that commits to them.

From Pectra, [EIP-7685][eip-7685] gives each request list a type byte, then opaque data.

The header commits to the lists by the requests hash.

It is the SHA-256 hash of the SHA-256 hashes of the lists, in the order of their types.

A list with no data, only its type byte, does not enter the hash.

[EIP-6110][eip-6110] makes deposits the requests of type 0.

From Glamsterdam, [EIP-8282][eip-8282] adds the builder deposits, of type 3, and exits, of type 4.

That EIP is in Last Call, so its rules may still change.

The block finds them in the logs of the deposit contract, in the order of the logs.

Each deposit log carries its fields in the layout of the Solidity ABI.

The request keeps only the fields, without the offsets, sizes and padding of that layout.

A deposit log with any other layout makes the block invalid.

[eip-7685]: https://eips.ethereum.org/EIPS/eip-7685#specification
[eip-6110]: https://eips.ethereum.org/EIPS/eip-6110#block-validity
[eip-8282]: https://eips.ethereum.org/EIPS/eip-8282#constants
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base

/-! ## Request types -/

/-- The type of the deposit requests, from EIP-6110. -/
def DEPOSIT_REQUEST_TYPE : UInt8 := 0

/-- The type of the withdrawal requests, from EIP-7002. -/
def WITHDRAWAL_REQUEST_TYPE : UInt8 := 1

/-- The type of the consolidation requests, from EIP-7251. -/
def CONSOLIDATION_REQUEST_TYPE : UInt8 := 2

/-- The type of the builder deposit requests, from EIP-8282, from Glamsterdam. -/
def BUILDER_DEPOSIT_REQUEST_TYPE : UInt8 := 3

/-- The type of the builder exit requests, from EIP-8282, from Glamsterdam. -/
def BUILDER_EXIT_REQUEST_TYPE : UInt8 := 4

/-! ## Deposits -/

/-- The address of the deposit contract on mainnet. -/
def DEPOSIT_CONTRACT_ADDRESS : Address :=
  #v[0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40, 0x35, 0x6c, 0xbb, 0x83, 0x9c, 0xbe, 0x05,
    0x30, 0x3d, 0x77, 0x05, 0xfa]

/-- The first topic of a deposit log: the Keccak-256 hash of the signature of the event. -/
def DEPOSIT_EVENT_SIGNATURE_HASH : Hash32 :=
  #v[0x64, 0x9b, 0xbc, 0x62, 0xd0, 0xe3, 0x13, 0x42, 0xaf, 0xea, 0x4e, 0x5c, 0xd8, 0x2d, 0x40,
    0x49, 0xe7, 0xe1, 0xee, 0x91, 0x2f, 0xc0, 0x88, 0x9a, 0xa7, 0x90, 0x80, 0x3b, 0xe3, 0x90,
    0x38, 0xc5]

/-- The length of the data of a deposit log, in bytes. -/
def DEPOSIT_EVENT_LENGTH : Nat := 576

/-- The offset and the size of each field of a deposit log, in the order of the request.

The fields are the public key, the credentials, the amount, the signature and the index.

The offset is where the 32-byte size of the field starts, and the field follows its size. -/
def DEPOSIT_EVENT_FIELDS : List (Nat × Nat) := [(160, 48), (256, 32), (320, 8), (384, 96), (512, 8)]

/-- Why a deposit log has no deposit request. -/
inductive DepositError where
  /-- The data has another length than 576 bytes. -/
  | wrongLength (length : Nat)
  /-- The head gives a field, counted from 0, another offset than its own. -/
  | wrongOffset (field offset : Nat)
  /-- The size of a field, counted from 0, is not its own. -/
  | wrongSize (field size : Nat)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 301, above the codes of the other errors of a block.

A new constructor takes a new code, so that each code keeps its meaning. -/
def DepositError.code : DepositError → UInt32
  | .wrongLength _ => 301
  | .wrongOffset .. => 302
  | .wrongSize .. => 303

/-- The 32-byte big-endian word at a position of the data, as a number. -/
def wordAt (data : List UInt8) (position : Nat) : Nat :=
  bytesToNat ((data.drop position).take 32)

/-- The bytes of a field whose 32-byte size starts at `offset`. -/
def fieldAt (data : List UInt8) (offset size : Nat) : List UInt8 :=
  (data.drop (offset + 32)).take size

/-- The deposit request of the data of a deposit log: its five fields, one after the other.

The data must have 576 bytes, and the head must give each field its offset.

Each field must start with its size. -/
def depositRequestOfEvent (data : ByteArray) : Except DepositError ByteArray := do
  let bytes := data.data.toList
  if bytes.length ≠ DEPOSIT_EVENT_LENGTH then throw (.wrongLength bytes.length)
  -- The head holds the offset of each field, one word for each.
  DEPOSIT_EVENT_FIELDS.zipIdx.forM fun ((offset, _), field) =>
    if wordAt bytes (32 * field) = offset then pure () else
      throw (.wrongOffset field (wordAt bytes (32 * field)))
  -- Each field starts with its size.
  DEPOSIT_EVENT_FIELDS.zipIdx.forM fun ((offset, size), field) =>
    if wordAt bytes offset = size then pure () else
      throw (.wrongSize field (wordAt bytes offset))
  return ⟨(DEPOSIT_EVENT_FIELDS.flatMap fun (offset, size) => fieldAt bytes offset size).toArray⟩

/-- Whether a log is a deposit: it comes from the deposit contract, with the deposit topic first. -/
def isDepositLog (log : Log) : Bool :=
  log.address = DEPOSIT_CONTRACT_ADDRESS && log.topics.head? = some DEPOSIT_EVENT_SIGNATURE_HASH

/-- The data of the deposit requests of a block: the request of each deposit log, in order.

The logs are those of the receipts of the block, in order. -/
def depositRequests (logs : List Log) : Except DepositError ByteArray := do
  let requests ← (logs.filter isDepositLog).mapM fun log => depositRequestOfEvent log.data
  return requests.foldl (· ++ ·) .empty

/-! ## The requests hash -/

/-- The requests hash: the SHA-256 hash of the SHA-256 hash of each list with data, in order.

Each list is its type byte, then its data, and the lists come in the order of their types. -/
def requestsHash (requests : List ByteArray) : ByteArray :=
  Cryptography.Hash.sha256
    ((requests.filter (·.size > 1)).foldl (fun acc r => acc ++ Cryptography.Hash.sha256 r) .empty)

end EthLib.Execution.Blocks

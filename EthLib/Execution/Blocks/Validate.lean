module

public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Fees.BaseFee
public import EthLib.Execution.Fees.BlobBaseFee
public import EthLib.Execution.Fees.GasLimit

/-!
# `Blocks.Validate`

The checks that a header must pass against the header of its parent, from Paris on.

Before Paris, a header also needs a valid proof of work, which is not here.

Each check reads only the two headers.

The checks that need the body or the state of the parent are elsewhere.

Section 4.4.4 of the Yellow Paper, Shanghai version, states the checks: [`Paper.tex`][yp].

[EIP-3675][eip-3675] fixes the difficulty, the nonce and the ommers hash from Paris.

[EIP-4844][eip-4844] adds the excess blob gas at Dencun.

[EIP-7934][eip-7934] bounds the RLP size of a block from Fusaka.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip-3675]: https://eips.ethereum.org/EIPS/eip-3675#block-structure
[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#header-extension
[eip-7934]: https://eips.ethereum.org/EIPS/eip-7934#specification
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Fees
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The hash of the empty list of ommers: the Keccak-256 hash of `c0`, the RLP form of `[]`. -/
def EMPTY_OMMER_HASH : Hash32 := keccak256 ⟨#[0xc0]⟩

/-- The most bytes of the extra data of a header. -/
def MAX_EXTRA_DATA_BYTES : Nat := 32

/-- From Fusaka, the most bytes of the RLP form of a block: 10 MiB minus a margin of 2 MiB. -/
def MAX_RLP_BLOCK_SIZE : Nat := 10485760 - 2097152

/-- Why a header or a block is not valid. -/
inductive BlockError where
  /-- The header has number 0, which only the genesis block has. -/
  | genesisNumber
  /-- The excess blob gas is not the one that the parent gives. -/
  | wrongExcessBlobGas (expected actual : Nat)
  /-- The block uses more gas than its gas limit. -/
  | gasUsedAboveLimit
  /-- The gas limit moves too far from the parent's, or is below the minimum. -/
  | invalidGasLimit
  /-- The base fee is not the one that the parent gives. -/
  | wrongBaseFee (expected actual : Nat)
  /-- The timestamp is not after the parent's. -/
  | timestampNotAfterParent
  /-- The number is not the parent's plus 1. -/
  | wrongNumber
  /-- The extra data has more than 32 bytes. -/
  | extraDataTooLong
  /-- The difficulty is not 0. -/
  | nonzeroDifficulty
  /-- The nonce is not 8 zero bytes. -/
  | nonzeroNonce
  /-- The ommers hash is not the hash of the empty list. -/
  | wrongOmmersHash
  /-- The parent hash is not the hash of the parent's header. -/
  | wrongParentHash
  /-- A header or a block has no RLP form. -/
  | encoding (error : RlpError)
  /-- The RLP form of the block has more than the most bytes. -/
  | blockTooLarge (size : Nat)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

The codes start at 201, above the codes of RLP and receipt errors, so that none of them meet.

A new constructor takes a new code, so that each code keeps its meaning. -/
def BlockError.code : BlockError → UInt32
  | .genesisNumber => 201
  | .wrongExcessBlobGas _ _ => 202
  | .gasUsedAboveLimit => 203
  | .invalidGasLimit => 204
  | .wrongBaseFee _ _ => 205
  | .timestampNotAfterParent => 206
  | .wrongNumber => 207
  | .extraDataTooLong => 208
  | .nonzeroDifficulty => 209
  | .nonzeroNonce => 210
  | .wrongOmmersHash => 211
  | .wrongParentHash => 212
  | .encoding _ => 213
  | .blockTooLarge _ => 214

/-- The first error whose condition fails, in order, or success when every condition holds. -/
def firstFailure : List (Bool × BlockError) → Except BlockError Unit
  | [] => .ok ()
  | (condition, error) :: rest => if condition then firstFailure rest else .error error

/-- The excess blob gas of a parent, or 0 for a parent before Dencun. -/
def parentExcessBlobGas {parentFork : Fork} (parent : Header parentFork) : Nat :=
  if h : .dencun ≤ parentFork then (parent.excessBlobGas h).toNat else 0

/-- The blob gas that a parent used, or 0 for a parent before Dencun. -/
def parentBlobGasUsed {parentFork : Fork} (parent : Header parentFork) : Nat :=
  if h : .dencun ≤ parentFork then (parent.blobGasUsed h).toNat else 0

/-- The excess blob gas that a parent gives to a header at `fork`, from Dencun on. -/
def expectedExcessBlobGas {parentFork fork : Fork} (hLondon : .london ≤ parentFork)
    (h : .dencun ≤ fork) (parent : Header parentFork) : Nat :=
  BlobBaseFee.calcExcessBlobGas fork (BlobBaseFee.blobSchedule fork h)
    (parentExcessBlobGas parent) (parentBlobGasUsed parent) (parent.baseFeePerGas hLondon)

/-- The base fee that a parent gives to its child. -/
def expectedBaseFee {parentFork : Fork} (hLondon : .london ≤ parentFork)
    (parent : Header parentFork) : Nat :=
  BaseFee.calculateBaseFeePerGas parent.gasLimit parent.gasUsed (parent.baseFeePerGas hLondon)

/-- The checks of a header at `fork` against its parent, in order, each with its error. -/
def headerChecks {parentFork fork : Fork} (hLondon : .london ≤ parentFork)
    (hFork : parentFork ≤ fork) (parent : Header parentFork) (header : Header fork) :
    List (Bool × BlockError) :=
  let excessCheck :=
    if h : .dencun ≤ fork then
      let expected := expectedExcessBlobGas hLondon h parent
      let actual := (header.excessBlobGas h).toNat
      [(decide (actual = expected), BlockError.wrongExcessBlobGas expected actual)]
    else []
  let baseFee := header.baseFeePerGas (Nat.le_trans hLondon hFork)
  let parentHashCheck :=
    match parent.hash with
    | .ok parentHash => (decide (header.parentHash = parentHash), BlockError.wrongParentHash)
    | .error e => (false, BlockError.encoding e)
  [(decide (1 ≤ header.number), .genesisNumber)] ++ excessCheck ++
    [(decide (header.gasUsed ≤ header.gasLimit), .gasUsedAboveLimit),
      (GasLimit.checkGasLimit header.gasLimit parent.gasLimit, .invalidGasLimit),
      (decide (baseFee = expectedBaseFee hLondon parent),
        .wrongBaseFee (expectedBaseFee hLondon parent) baseFee),
      (decide (parent.timestamp.toNat < header.timestamp.toNat), .timestampNotAfterParent),
      (decide (header.number = parent.number + 1), .wrongNumber),
      (decide (header.extraData.size ≤ MAX_EXTRA_DATA_BYTES), .extraDataTooLong),
      (decide (header.difficulty = 0), .nonzeroDifficulty),
      (decide (header.nonce = Vector.replicate 8 0), .nonzeroNonce),
      (decide (header.ommersHash = EMPTY_OMMER_HASH), .wrongOmmersHash),
      parentHashCheck]

/-- Check a header at `fork` against its parent at `parentFork`, from Paris on.

The parent can be at an earlier fork, when the header is the first of a fork.

The parent of the first Paris block is a proof-of-work block, from London on. -/
def validateHeader {parentFork fork : Fork} (hLondon : .london ≤ parentFork)
    (hFork : parentFork ≤ fork) (_hParis : .paris ≤ fork) (parent : Header parentFork)
    (header : Header fork) : Except BlockError Unit :=
  firstFailure (headerChecks hLondon hFork parent header)

/-- Check the RLP size of a block: from Fusaka, at most the most bytes. -/
def validateBlockSize {fork : Fork} {Tx : Type} [Codec Tx] (block : Block fork Tx) :
    Except BlockError Unit :=
  if fork ≥ .fusaka then do
    let bytes ← (Codec.encode block).mapError .encoding
    firstFailure [(decide (bytes.size ≤ MAX_RLP_BLOCK_SIZE), .blockTooLarge bytes.size)]
  else .ok ()

end EthLib.Execution.Blocks

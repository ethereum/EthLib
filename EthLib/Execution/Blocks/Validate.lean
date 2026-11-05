module

public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Blocks.Difficulty
public import EthLib.Execution.Blocks.ProofOfWork
public import EthLib.Execution.Blocks.Requests
public import EthLib.Execution.Evm.Errors
public import EthLib.Execution.Transactions.Inclusion
public import EthLib.Execution.Trie.Root
public import EthLib.Execution.Fees.BaseFee
public import EthLib.Execution.Fees.BlobBaseFee
public import EthLib.Execution.Fees.GasLimit

/-!
# `Blocks.Validate`

The checks that a header must pass against the header of its parent, at every fork.

Each check reads only the two headers.

The checks that need the body or the state of the parent are elsewhere.

Section 4.4.4 of the Yellow Paper, Shanghai version, states the checks: [`Paper.tex`][yp].

Before Paris, the difficulty and the proof of work also count.

Section 4.3.4 of the Berlin version states them: [`Paper.tex`][yp-berlin].

[EIP-1559][eip-1559] adds the base fee at London, and sets it at the first London block.

[EIP-3675][eip-3675] fixes the difficulty, the nonce and the ommers hash from Paris.

[EIP-4844][eip-4844] adds the excess blob gas at Dencun.

[EIP-7934][eip-7934] bounds the RLP size of a block from Fusaka.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[yp-berlin]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[eip-1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
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

/-- The base fee of the first London block, whose parent has none: `INITIAL_BASE_FEE` of EIP-1559.
-/
def INITIAL_BASE_FEE : Nat := 1000000000

/-- The most bytes of the extra data of a header. -/
def MAX_EXTRA_DATA_BYTES : Nat := 32

/-- From Fusaka, the most bytes of the RLP form of a block: 10 MiB minus a margin of 2 MiB. -/
def MAX_RLP_BLOCK_SIZE : Nat := 10485760 - 2097152

mutual

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
  /-- Before Paris, the difficulty is not the one that the parent gives. -/
  | wrongDifficulty (expected actual : Nat)
  /-- Before Paris, the proof of work fails. -/
  | proofOfWork (error : PowError)
  /-- From Paris on, the parent is before London, so it has no base fee. -/
  | parentBeforeLondon
  /-- A system call that must succeed finds no code at `address`. -/
  | systemContractEmpty (address : Address)
  /-- A system call that must succeed fails at `address` with `error`. -/
  | systemCallFailed (address : Address) (error : Evm.EvmError)
  /-- The execution aborts with `error`, so the block is neither valid nor invalid.

  The state lacks data that it must hold, or the rules of the fork are not yet specified. -/
  | aborted (error : Evm.EvmError)
  /-- The transaction `index`, counted from 0, cannot enter the block, by `error`. -/
  | invalidTransaction (index : Nat) (error : Transactions.InclusionError)
  /-- The fork of the block is not the active fork of its chain at its number and its time. -/
  | wrongFork
  /-- The chain holds no parent for the block. -/
  | noParent
  /-- From Paris, the block holds ommers. -/
  | ommersAfterParis
  /-- A block of the DAO Fork's first ten lacks the extra data `dao-hard-fork`. -/
  | wrongDaoExtraData
  /-- A deposit log of the block has no deposit request. -/
  | deposit (error : DepositError)
  /-- A root of the block has no trie. -/
  | trie (error : Trie.TrieError)
  /-- The gas used `actual` of the body is not the gas used `expected` of the header. -/
  | wrongGasUsed (expected actual : Nat)
  /-- The transactions root is not the root of the transactions. -/
  | wrongTransactionsRoot
  /-- The state root is not the root of the state after the block. -/
  | wrongStateRoot
  /-- The receipts root is not the root of the receipts. -/
  | wrongReceiptRoot
  /-- The Bloom filter is not the filter of the logs of the block. -/
  | wrongBloom
  /-- From Shapella, the withdrawals root is not the root of the withdrawals. -/
  | wrongWithdrawalsRoot
  /-- From Dencun, the blob gas used `actual` of the body is not `expected` of the header. -/
  | wrongBlobGasUsed (expected actual : Nat)
  /-- From Pectra, the requests hash is not the hash of the requests. -/
  | wrongRequestsHash
  /-- Before Paris, the ommers are not valid, by `error`. -/
  | ommers (error : OmmerError)
  /-- A balance would reach `2^256`, which no rule of a block allows for. -/
  | state (error : State.StateError)
  /-- The transaction `index`, counted from 0, of the body does not decode at the fork. -/
  | undecodableTransaction (index : Nat) (error : Transactions.TransactionError)

/-- Why the ommers of a block are not valid. -/
inductive OmmerError where
  /-- The ommers hash of the header is not the hash of the ommers. -/
  | wrongOmmersHash
  /-- An ommer's number is 0, or not below the block's. -/
  | numberOutOfRange
  /-- The recent chain holds no block with the number of an ommer's parent. -/
  | parentMissing
  /-- An ommer is not a valid header against its parent. -/
  | invalidHeader (error : BlockError)
  /-- The block holds more than two ommers. -/
  | tooManyOmmers
  /-- The block holds one ommer twice. -/
  | duplicateOmmer
  /-- An ommer is the block itself, or a block of the recent chain. -/
  | ommerInChain
  /-- An ommer is already an ommer of a recent block. -/
  | ommerAlreadyIncluded
  /-- An ommer is not one to six blocks older than the block. -/
  | wrongAge
  /-- The parent of an ommer is not a block of the recent chain. -/
  | parentNotRecent
  /-- An ommer has the parent of the block, so it is a sibling, not an ommer. -/
  | siblingOfBlock
  /-- A header has no RLP form. -/
  | encoding (error : RlpError)
  /-- An ommer in the first ten blocks of the DAO Fork lacks the extra data of that fork. -/
  | wrongDaoExtraData

end

deriving instance DecidableEq for BlockError, OmmerError


/-- A constructor, named in full, applied to its arguments, in Lean syntax. -/
def constructorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  let applied : Std.Format := .group (.nest 2 (args.foldl (fun f a => f ++ .line ++ a) name))
  -- An argument position puts the application in parentheses, as `Repr.addAppParen` does.
  if prec ≥ max_prec then .group (.nest 1 (.text "(" ++ applied ++ .text ")")) else applied

mutual

/-- The form of a block error in Lean syntax, with its arguments. -/
def BlockError.reprPrec' : BlockError → Nat → Std.Format
  | .genesisNumber, _ => "EthLib.Execution.Blocks.BlockError.genesisNumber"
  | .wrongExcessBlobGas expected actual, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.wrongExcessBlobGas"
      [reprArg expected, reprArg actual] prec
  | .gasUsedAboveLimit, _ => "EthLib.Execution.Blocks.BlockError.gasUsedAboveLimit"
  | .invalidGasLimit, _ => "EthLib.Execution.Blocks.BlockError.invalidGasLimit"
  | .wrongBaseFee expected actual, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.wrongBaseFee"
      [reprArg expected, reprArg actual] prec
  | .timestampNotAfterParent, _ => "EthLib.Execution.Blocks.BlockError.timestampNotAfterParent"
  | .wrongNumber, _ => "EthLib.Execution.Blocks.BlockError.wrongNumber"
  | .extraDataTooLong, _ => "EthLib.Execution.Blocks.BlockError.extraDataTooLong"
  | .nonzeroDifficulty, _ => "EthLib.Execution.Blocks.BlockError.nonzeroDifficulty"
  | .nonzeroNonce, _ => "EthLib.Execution.Blocks.BlockError.nonzeroNonce"
  | .wrongOmmersHash, _ => "EthLib.Execution.Blocks.BlockError.wrongOmmersHash"
  | .wrongParentHash, _ => "EthLib.Execution.Blocks.BlockError.wrongParentHash"
  | .encoding error, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.encoding"
      [reprArg error] prec
  | .blockTooLarge size, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.blockTooLarge"
      [reprArg size] prec
  | .wrongDifficulty expected actual, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.wrongDifficulty"
      [reprArg expected, reprArg actual] prec
  | .proofOfWork error, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.proofOfWork"
      [reprArg error] prec
  | .parentBeforeLondon, _ => "EthLib.Execution.Blocks.BlockError.parentBeforeLondon"
  | .systemContractEmpty address, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.systemContractEmpty"
      [reprArg address] prec
  | .systemCallFailed address error, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.systemCallFailed"
      [reprArg address, reprArg error] prec
  | .aborted error, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.aborted"
      [reprArg error] prec
  | .invalidTransaction index error, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.invalidTransaction"
      [reprArg index, reprArg error] prec
  | .wrongFork, _ => "EthLib.Execution.Blocks.BlockError.wrongFork"
  | .noParent, _ => "EthLib.Execution.Blocks.BlockError.noParent"
  | .ommersAfterParis, _ => "EthLib.Execution.Blocks.BlockError.ommersAfterParis"
  | .wrongDaoExtraData, _ => "EthLib.Execution.Blocks.BlockError.wrongDaoExtraData"
  | .deposit error, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.deposit"
      [reprArg error] prec
  | .trie error, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.trie"
      [reprArg error] prec
  | .wrongGasUsed expected actual, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.wrongGasUsed"
      [reprArg expected, reprArg actual] prec
  | .wrongTransactionsRoot, _ => "EthLib.Execution.Blocks.BlockError.wrongTransactionsRoot"
  | .wrongStateRoot, _ => "EthLib.Execution.Blocks.BlockError.wrongStateRoot"
  | .wrongReceiptRoot, _ => "EthLib.Execution.Blocks.BlockError.wrongReceiptRoot"
  | .wrongBloom, _ => "EthLib.Execution.Blocks.BlockError.wrongBloom"
  | .wrongWithdrawalsRoot, _ => "EthLib.Execution.Blocks.BlockError.wrongWithdrawalsRoot"
  | .wrongBlobGasUsed expected actual, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.wrongBlobGasUsed"
      [reprArg expected, reprArg actual] prec
  | .wrongRequestsHash, _ => "EthLib.Execution.Blocks.BlockError.wrongRequestsHash"
  | .ommers error, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.ommers"
      [OmmerError.reprPrec' error max_prec] prec
  | .state error, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.state"
      [reprArg error] prec
  | .undecodableTransaction index error, prec =>
    constructorFormat "EthLib.Execution.Blocks.BlockError.undecodableTransaction"
      [reprArg index, reprArg error] prec

/-- The form of an ommer error in Lean syntax, with its arguments. -/
def OmmerError.reprPrec' : OmmerError → Nat → Std.Format
  | .wrongOmmersHash, _ => "EthLib.Execution.Blocks.OmmerError.wrongOmmersHash"
  | .numberOutOfRange, _ => "EthLib.Execution.Blocks.OmmerError.numberOutOfRange"
  | .parentMissing, _ => "EthLib.Execution.Blocks.OmmerError.parentMissing"
  | .invalidHeader error, prec =>
    constructorFormat "EthLib.Execution.Blocks.OmmerError.invalidHeader"
      [BlockError.reprPrec' error max_prec] prec
  | .tooManyOmmers, _ => "EthLib.Execution.Blocks.OmmerError.tooManyOmmers"
  | .duplicateOmmer, _ => "EthLib.Execution.Blocks.OmmerError.duplicateOmmer"
  | .ommerInChain, _ => "EthLib.Execution.Blocks.OmmerError.ommerInChain"
  | .ommerAlreadyIncluded, _ => "EthLib.Execution.Blocks.OmmerError.ommerAlreadyIncluded"
  | .wrongAge, _ => "EthLib.Execution.Blocks.OmmerError.wrongAge"
  | .parentNotRecent, _ => "EthLib.Execution.Blocks.OmmerError.parentNotRecent"
  | .siblingOfBlock, _ => "EthLib.Execution.Blocks.OmmerError.siblingOfBlock"
  | .encoding error, prec =>
    constructorFormat "EthLib.Execution.Blocks.OmmerError.encoding"
      [reprArg error] prec
  | .wrongDaoExtraData, _ => "EthLib.Execution.Blocks.OmmerError.wrongDaoExtraData"

end

instance : Repr BlockError := ⟨BlockError.reprPrec'⟩

instance : Repr OmmerError := ⟨OmmerError.reprPrec'⟩

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

The codes start at 201, above the codes of RLP and receipt errors, so that none of them meet.

Proof-of-work errors hold the codes 221 to 223, and ommer errors the codes 231 to 243.

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
  | .wrongDifficulty _ _ => 215
  | .proofOfWork _ => 216
  | .parentBeforeLondon => 217
  | .systemContractEmpty _ => 218
  | .systemCallFailed .. => 219
  | .aborted _ => 220
  | .invalidTransaction .. => 224
  | .wrongFork => 225
  | .noParent => 226
  | .ommersAfterParis => 227
  | .wrongDaoExtraData => 228
  | .deposit _ => 229
  | .trie _ => 230
  | .wrongGasUsed .. => 244
  | .wrongTransactionsRoot => 245
  | .wrongStateRoot => 246
  | .wrongReceiptRoot => 247
  | .wrongBloom => 248
  | .wrongWithdrawalsRoot => 249
  | .wrongBlobGasUsed .. => 250
  | .wrongRequestsHash => 251
  | .ommers _ => 252
  | .state _ => 253
  | .undecodableTransaction .. => 254

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 231, above the codes of the header and proof-of-work errors. -/
def OmmerError.code : OmmerError → UInt32
  | .wrongOmmersHash => 231
  | .numberOutOfRange => 232
  | .parentMissing => 233
  | .invalidHeader _ => 234
  | .tooManyOmmers => 235
  | .duplicateOmmer => 236
  | .ommerInChain => 237
  | .ommerAlreadyIncluded => 238
  | .wrongAge => 239
  | .parentNotRecent => 240
  | .siblingOfBlock => 241
  | .encoding _ => 242
  | .wrongDaoExtraData => 243

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

/-- The excess blob gas that a parent gives to a header at `fork`, from Dencun on.

The blob schedule is the header's, by default the schedule of the fork. -/
def expectedExcessBlobGas {parentFork fork : Fork} (hLondon : .london ≤ parentFork)
    (h : .dencun ≤ fork) (parent : Header parentFork)
    (schedule : Since .dencun fork BlobSchedule := BlobBaseFee.blobSchedule fork) : Nat :=
  BlobBaseFee.calcExcessBlobGas fork (schedule h)
    (parentExcessBlobGas parent) (parentBlobGasUsed parent) (parent.baseFeePerGas hLondon)

/-- The base fee that a parent gives to its child. -/
def expectedBaseFee {parentFork : Fork} (hLondon : .london ≤ parentFork)
    (parent : Header parentFork) : Nat :=
  BaseFee.calculateBaseFeePerGas parent.gasLimit parent.gasUsed (parent.baseFeePerGas hLondon)

/-- The base fee that a parent gives to a header at London or later.

The parent of the first London block has no base fee, and the header takes the initial base fee.
-/
def expectedBaseFeeAcross {parentFork : Fork} (parent : Header parentFork) : Nat :=
  if hLondon : .london ≤ parentFork then expectedBaseFee hLondon parent else INITIAL_BASE_FEE

/-- The difficulty that a parent gives to a header at `fork`, before Paris.

A parent has ommers when its ommers hash is not the hash of the empty list. -/
def expectedDifficulty {parentFork fork : Fork} (parent : Header parentFork)
    (header : Header fork) : Nat :=
  blockDifficulty fork header.number header.timestamp.toNat parent.timestamp.toNat
    parent.difficulty (parent.ommersHash != EMPTY_OMMER_HASH)

/-- The checks of a header at `fork` against its parent, in order, each with its error.

From Paris on, the parent must be from London on, as the base fee and the blob gas need.

Before Paris, the difficulty follows its rule; from Paris on, the proof-of-work fields are fixed.

The blob schedule is the header's, by default the schedule of the fork. -/
def headerChecks {parentFork fork : Fork} (_hFork : parentFork ≤ fork)
    (parent : Header parentFork) (header : Header fork)
    (schedule : Since .dencun fork BlobSchedule := BlobBaseFee.blobSchedule fork) :
    List (Bool × BlockError) :=
  let parentCheck :=
    if .paris ≤ fork then [(decide (.london ≤ parentFork), BlockError.parentBeforeLondon)] else []
  let excessCheck :=
    if h : .dencun ≤ fork then
      if hLondon : .london ≤ parentFork then
        let expected := expectedExcessBlobGas hLondon h parent schedule
        let actual := (header.excessBlobGas h).toNat
        [(decide (actual = expected), BlockError.wrongExcessBlobGas expected actual)]
      else []
    else []
  let baseFeeCheck :=
    if h : .london ≤ fork then
      let baseFee := header.baseFeePerGas h
      [(decide (baseFee = expectedBaseFeeAcross parent),
        BlockError.wrongBaseFee (expectedBaseFeeAcross parent) baseFee)]
    else []
  let workChecks :=
    if fork < .paris then
      [(decide (header.difficulty = expectedDifficulty parent header),
        BlockError.wrongDifficulty (expectedDifficulty parent header) header.difficulty)]
    else
      [(decide (header.difficulty = 0), BlockError.nonzeroDifficulty),
        (decide (header.nonce = Vector.replicate 8 0), .nonzeroNonce),
        (decide (header.ommersHash = EMPTY_OMMER_HASH), .wrongOmmersHash)]
  let parentHashCheck :=
    match parent.hash with
    | .ok parentHash => (decide (header.parentHash = parentHash), BlockError.wrongParentHash)
    | .error e => (false, BlockError.encoding e)
  parentCheck ++ [(decide (1 ≤ header.number), .genesisNumber)] ++ excessCheck ++
    [(decide (header.gasUsed ≤ header.gasLimit), .gasUsedAboveLimit),
      (GasLimit.checkGasLimitAcross parentFork fork header.gasLimit parent.gasLimit,
        .invalidGasLimit)] ++ baseFeeCheck ++
    [(decide (parent.timestamp.toNat < header.timestamp.toNat), .timestampNotAfterParent),
      (decide (header.number = parent.number + 1), .wrongNumber),
      (decide (header.extraData.size ≤ MAX_EXTRA_DATA_BYTES), .extraDataTooLong)] ++
    workChecks ++ [parentHashCheck]

/-- Check a header against its parent, every check but the proof of work.

The parent can be at an earlier fork, when the header is the first of a fork.

The blob schedule is the header's, by default the schedule of the fork. -/
def checkHeader {parentFork fork : Fork} (hFork : parentFork ≤ fork)
    (parent : Header parentFork) (header : Header fork)
    (schedule : Since .dencun fork BlobSchedule := BlobBaseFee.blobSchedule fork) :
    Except BlockError Unit :=
  firstFailure (headerChecks hFork parent header schedule)

/-- Check a header at `fork` against its parent at `parentFork`, at every fork.

Before Paris, the proof of work is checked last, after every other check passes.

The blob schedule is the header's, by default the schedule of the fork. -/
def validateHeader {parentFork fork : Fork} (hFork : parentFork ≤ fork)
    (parent : Header parentFork) (header : Header fork)
    (schedule : Since .dencun fork BlobSchedule := BlobBaseFee.blobSchedule fork) :
    Except BlockError Unit := do
  checkHeader hFork parent header schedule
  if fork < .paris then (checkProofOfWork header).mapError .proofOfWork

/-- Check the RLP size of a block: from Fusaka, at most the most bytes. -/
def validateBlockSize {fork : Fork} {Tx : Type} [Codec Tx] (block : Block fork Tx) :
    Except BlockError Unit :=
  if fork ≥ .fusaka then do
    let bytes ← block.encode.mapError .encoding
    firstFailure [(decide (bytes.size ≤ MAX_RLP_BLOCK_SIZE), .blockTooLarge bytes.size)]
  else .ok ()

end EthLib.Execution.Blocks

module

public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Blocks.BlockAccessList
public import EthLib.Execution.Blocks.Difficulty
public import EthLib.Execution.Blocks.ProofOfWork
public import EthLib.Execution.Blocks.Requests
public import EthLib.Execution.ErrorFormat
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
[eip-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#block-structure
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
  /-- The excess blob gas `actual` of the header is not `expected`, the one the parent gives. -/
  | wrongExcessBlobGas (expected actual : Nat)
  /-- The block uses `gasUsed` gas, more than its gas limit `gasLimit`. -/
  | gasUsedAboveLimit (gasUsed gasLimit : Nat)
  /-- The gas limit `gasLimit` moves too far from the parent's `parentGasLimit`, or is too low. -/
  | invalidGasLimit (gasLimit parentGasLimit : Nat)
  /-- The base fee `actual` of the header is not `expected`, the one the parent gives. -/
  | wrongBaseFee (expected actual : Nat)
  /-- The timestamp `timestamp` is not after the parent's `parentTimestamp`. -/
  | timestampNotAfterParent (timestamp parentTimestamp : Nat)
  /-- The number `actual` is not `expected`, the parent's plus 1. -/
  | wrongNumber (expected actual : Nat)
  /-- The extra data has `size` bytes, more than 32. -/
  | extraDataTooLong (size : Nat)
  /-- The difficulty `difficulty` is not 0. -/
  | nonzeroDifficulty (difficulty : Nat)
  /-- The nonce `nonce` is not 8 zero bytes. -/
  | nonzeroNonce (nonce : Bytes8)
  /-- The ommers hash `ommersHash` is not the hash of the empty list. -/
  | wrongOmmersHash (ommersHash : Hash32)
  /-- The parent hash `actual` of the header is not `expected`, the hash of the parent's header.

  A parent at a later fork than the header fails this check at once.

  Its hash is then none when its header has no RLP form. -/
  | wrongParentHash (expected : Option Hash32) (actual : Hash32)
  /-- A header or a block has no RLP form. -/
  | encoding (error : RlpError)
  /-- The RLP form of the block has `size` bytes, more than the most bytes. -/
  | blockTooLarge (size : Nat)
  /-- Before Paris, the difficulty `actual` is not `expected`, the one the parent gives. -/
  | wrongDifficulty (expected actual : Nat)
  /-- Before Paris, the proof of work fails. -/
  | proofOfWork (error : PowError)
  /-- From Paris on, the parent is at `parentFork`, before London, so it has no base fee. -/
  | parentBeforeLondon (parentFork : Fork)
  /-- A system call that must succeed finds no code at `address`. -/
  | systemContractEmpty (address : Address)
  /-- A system call that must succeed fails at `address` with `error`. -/
  | systemCallFailed (address : Address) (error : Evm.EvmError)
  /-- The execution aborts with `error`, so the block is neither valid nor invalid.

  The state lacks data that it must hold, or the rules of the fork are not yet specified. -/
  | aborted (error : Evm.EvmError)
  /-- The transaction `index`, counted from 0, cannot enter the block, by `error`. -/
  | invalidTransaction (index : Nat) (error : Transactions.InclusionError)
  /-- The fork `fork` of the block is not `active`, the active fork of its chain at the block.

  The active fork is none when the chain activates no fork at the number and the time. -/
  | wrongFork (active : Option Fork) (fork : Fork)
  /-- The chain holds no parent for the block. -/
  | noParent
  /-- From Paris, the block holds `count` ommers. -/
  | ommersAfterParis (count : Nat)
  /-- A block of the DAO Fork's first ten has the extra data `extraData`, not `dao-hard-fork`. -/
  | wrongDaoExtraData (extraData : ByteArray)
  /-- A deposit log of the block has no deposit request. -/
  | deposit (error : DepositError)
  /-- A root of the block has no trie. -/
  | trie (error : Trie.TrieError)
  /-- The gas used `actual` of the body is not the gas used `expected` of the header. -/
  | wrongGasUsed (expected actual : Nat)
  /-- The transactions root `expected` of the header is not `actual`, that of the transactions. -/
  | wrongTransactionsRoot (expected actual : Hash32)
  /-- The state root `expected` of the header is not `actual`, that of the state after the block.
  -/
  | wrongStateRoot (expected actual : Hash32)
  /-- The receipts root `expected` of the header is not `actual`, that of the receipts. -/
  | wrongReceiptRoot (expected actual : Hash32)
  /-- The Bloom filter `expected` of the header is not `actual`, that of the logs. -/
  | wrongBloom (expected actual : Bytes256)
  /-- From Shapella, the root `actual` of the withdrawals is not the root `expected` of the header.

  The root of the withdrawals is none only before Shapella, where no check reads it. -/
  | wrongWithdrawalsRoot (expected : Hash32) (actual : Option Hash32)
  /-- From Dencun, the blob gas used `actual` of the body is not `expected` of the header. -/
  | wrongBlobGasUsed (expected actual : Nat)
  /-- From Pectra, the requests hash `expected` of the header is not `actual`, that of the requests.
  -/
  | wrongRequestsHash (expected actual : Hash32)
  /-- Before Paris, the ommers are not valid, by `error`. -/
  | ommers (error : OmmerError)
  /-- A balance would reach `2^256`, which no rule of a block allows for. -/
  | state (error : State.StateError)
  /-- The transaction `index`, counted from 0, of the body does not decode at the fork. -/
  | undecodableTransaction (index : Nat) (error : Transactions.TransactionError)
  /-- From Glamsterdam, the block access list of the body breaks a rule of its form, by `error`.

  The list that a body builds has the right form, so only its size can break a rule. -/
  | blockAccessList (error : BlockAccessList.Error)
  /-- From Glamsterdam, the hash `actual` of the block access list is not `expected` of the header.

  The hash of the list is none only before Glamsterdam, where no check reads it. -/
  | wrongBlockAccessListHash (expected : Hash32) (actual : Option Hash32)

/-- Why the ommers of a block are not valid. -/
inductive OmmerError where
  /-- The hash `actual` of the ommers is not the ommers hash `expected` of the header. -/
  | wrongOmmersHash (expected actual : Hash32)
  /-- An ommer's number `number` is 0, or not below the block's number `blockNumber`. -/
  | numberOutOfRange (number blockNumber : Nat)
  /-- The recent chain holds no parent for the ommer with number `number`. -/
  | parentMissing (number : Nat)
  /-- An ommer is not a valid header against its parent. -/
  | invalidHeader (error : BlockError)
  /-- The block holds `count` ommers, more than two. -/
  | tooManyOmmers (count : Nat)
  /-- The block holds the ommer with hash `hash` twice. -/
  | duplicateOmmer (hash : Hash32)
  /-- The ommer with hash `hash` is the block itself, or a block of the recent chain. -/
  | ommerInChain (hash : Hash32)
  /-- The ommer with hash `hash` is already an ommer of a recent block. -/
  | ommerAlreadyIncluded (hash : Hash32)
  /-- The ommer with hash `hash` is `age` blocks older than the block, not one to six. -/
  | wrongAge (hash : Hash32) (age : Nat)
  /-- The parent `parentHash` of the ommer with hash `hash` is not a block of the recent chain. -/
  | parentNotRecent (hash parentHash : Hash32)
  /-- The ommer with hash `hash` has the parent of the block, so it is a sibling, not an ommer. -/
  | siblingOfBlock (hash : Hash32)
  /-- A header has no RLP form. -/
  | encoding (error : RlpError)
  /-- An ommer in the first ten blocks of the DAO Fork has the extra data `extraData`.

  It lacks the extra data of that fork. -/
  | wrongDaoExtraData (extraData : ByteArray)

end

deriving instance DecidableEq for BlockError, OmmerError

/-- A block error constructor, named in full, applied to its arguments. -/
def blockErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.Blocks.BlockError." ++ name) args prec

/-- An ommer error constructor, named in full, applied to its arguments. -/
def ommerErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.Blocks.OmmerError." ++ name) args prec

mutual

/-- The form of a block error in Lean syntax, with its arguments.

Each value has its name, and each hash and byte string is in hex. -/
def instReprBlockError.reprPrec : BlockError → Nat → Std.Format
  | .genesisNumber, p => blockErrorFormat "genesisNumber" [] p
  | .wrongExcessBlobGas expected actual, p =>
    blockErrorFormat "wrongExcessBlobGas"
      [namedArg "expected" expected, namedArg "actual" actual] p
  | .gasUsedAboveLimit gasUsed gasLimit, p =>
    blockErrorFormat "gasUsedAboveLimit"
      [namedArg "gasUsed" gasUsed, namedArg "gasLimit" gasLimit] p
  | .invalidGasLimit gasLimit parentGasLimit, p =>
    blockErrorFormat "invalidGasLimit"
      [namedArg "gasLimit" gasLimit, namedArg "parentGasLimit" parentGasLimit] p
  | .wrongBaseFee expected actual, p =>
    blockErrorFormat "wrongBaseFee" [namedArg "expected" expected, namedArg "actual" actual] p
  | .timestampNotAfterParent timestamp parentTimestamp, p =>
    blockErrorFormat "timestampNotAfterParent"
      [namedArg "timestamp" timestamp, namedArg "parentTimestamp" parentTimestamp] p
  | .wrongNumber expected actual, p =>
    blockErrorFormat "wrongNumber" [namedArg "expected" expected, namedArg "actual" actual] p
  | .extraDataTooLong size, p => blockErrorFormat "extraDataTooLong" [namedArg "size" size] p
  | .nonzeroDifficulty difficulty, p =>
    blockErrorFormat "nonzeroDifficulty" [namedArg "difficulty" difficulty] p
  | .nonzeroNonce nonce, p => blockErrorFormat "nonzeroNonce" [namedArg "nonce" nonce] p
  | .wrongOmmersHash ommersHash, p =>
    blockErrorFormat "wrongOmmersHash" [namedArg "ommersHash" ommersHash] p
  | .wrongParentHash expected actual, p =>
    blockErrorFormat "wrongParentHash" [namedArg "expected" expected, namedArg "actual" actual] p
  | .encoding error, p => blockErrorFormat "encoding" [reprArg error] p
  | .blockTooLarge size, p => blockErrorFormat "blockTooLarge" [namedArg "size" size] p
  | .wrongDifficulty expected actual, p =>
    blockErrorFormat "wrongDifficulty" [namedArg "expected" expected, namedArg "actual" actual] p
  | .proofOfWork error, p => blockErrorFormat "proofOfWork" [reprArg error] p
  | .parentBeforeLondon parentFork, p =>
    blockErrorFormat "parentBeforeLondon" [namedArg "parentFork" parentFork] p
  | .systemContractEmpty address, p =>
    blockErrorFormat "systemContractEmpty" [namedArg "address" address] p
  | .systemCallFailed address error, p =>
    blockErrorFormat "systemCallFailed" [namedArg "address" address, reprArg error] p
  | .aborted error, p => blockErrorFormat "aborted" [reprArg error] p
  | .invalidTransaction index error, p =>
    blockErrorFormat "invalidTransaction" [namedArg "index" index, reprArg error] p
  | .wrongFork active fork, p =>
    blockErrorFormat "wrongFork" [namedArg "active" active, namedArg "fork" fork] p
  | .noParent, p => blockErrorFormat "noParent" [] p
  | .ommersAfterParis count, p => blockErrorFormat "ommersAfterParis" [namedArg "count" count] p
  | .wrongDaoExtraData extraData, p =>
    blockErrorFormat "wrongDaoExtraData" [namedArg "extraData" extraData] p
  | .deposit error, p => blockErrorFormat "deposit" [reprArg error] p
  | .trie error, p => blockErrorFormat "trie" [reprArg error] p
  | .wrongGasUsed expected actual, p =>
    blockErrorFormat "wrongGasUsed" [namedArg "expected" expected, namedArg "actual" actual] p
  | .wrongTransactionsRoot expected actual, p =>
    blockErrorFormat "wrongTransactionsRoot"
      [namedArg "expected" expected, namedArg "actual" actual] p
  | .wrongStateRoot expected actual, p =>
    blockErrorFormat "wrongStateRoot" [namedArg "expected" expected, namedArg "actual" actual] p
  | .wrongReceiptRoot expected actual, p =>
    blockErrorFormat "wrongReceiptRoot" [namedArg "expected" expected, namedArg "actual" actual] p
  | .wrongBloom expected actual, p =>
    blockErrorFormat "wrongBloom" [namedArg "expected" expected, namedArg "actual" actual] p
  | .wrongWithdrawalsRoot expected actual, p =>
    blockErrorFormat "wrongWithdrawalsRoot"
      [namedArg "expected" expected, namedArg "actual" actual] p
  | .wrongBlobGasUsed expected actual, p =>
    blockErrorFormat "wrongBlobGasUsed" [namedArg "expected" expected, namedArg "actual" actual] p
  | .wrongRequestsHash expected actual, p =>
    blockErrorFormat "wrongRequestsHash"
      [namedArg "expected" expected, namedArg "actual" actual] p
  | .ommers error, p => blockErrorFormat "ommers" [instReprOmmerError.reprPrec error max_prec] p
  | .state error, p => blockErrorFormat "state" [reprArg error] p
  | .undecodableTransaction index error, p =>
    blockErrorFormat "undecodableTransaction" [namedArg "index" index, reprArg error] p
  | .blockAccessList error, p => blockErrorFormat "blockAccessList" [reprArg error] p
  | .wrongBlockAccessListHash expected actual, p =>
    blockErrorFormat "wrongBlockAccessListHash"
      [namedArg "expected" expected, namedArg "actual" actual] p

/-- The form of an ommer error in Lean syntax, with its arguments.

Each value has its name, and each hash and byte string is in hex. -/
def instReprOmmerError.reprPrec : OmmerError → Nat → Std.Format
  | .wrongOmmersHash expected actual, p =>
    ommerErrorFormat "wrongOmmersHash" [namedArg "expected" expected, namedArg "actual" actual] p
  | .numberOutOfRange number blockNumber, p =>
    ommerErrorFormat "numberOutOfRange"
      [namedArg "number" number, namedArg "blockNumber" blockNumber] p
  | .parentMissing number, p => ommerErrorFormat "parentMissing" [namedArg "number" number] p
  | .invalidHeader error, p =>
    ommerErrorFormat "invalidHeader" [instReprBlockError.reprPrec error max_prec] p
  | .tooManyOmmers count, p => ommerErrorFormat "tooManyOmmers" [namedArg "count" count] p
  | .duplicateOmmer hash, p => ommerErrorFormat "duplicateOmmer" [namedArg "hash" hash] p
  | .ommerInChain hash, p => ommerErrorFormat "ommerInChain" [namedArg "hash" hash] p
  | .ommerAlreadyIncluded hash, p =>
    ommerErrorFormat "ommerAlreadyIncluded" [namedArg "hash" hash] p
  | .wrongAge hash age, p =>
    ommerErrorFormat "wrongAge" [namedArg "hash" hash, namedArg "age" age] p
  | .parentNotRecent hash parentHash, p =>
    ommerErrorFormat "parentNotRecent" [namedArg "hash" hash, namedArg "parentHash" parentHash] p
  | .siblingOfBlock hash, p => ommerErrorFormat "siblingOfBlock" [namedArg "hash" hash] p
  | .encoding error, p => ommerErrorFormat "encoding" [reprArg error] p
  | .wrongDaoExtraData extraData, p =>
    ommerErrorFormat "wrongDaoExtraData" [namedArg "extraData" extraData] p

end

instance instReprBlockError : Repr BlockError := ⟨instReprBlockError.reprPrec⟩

instance instReprOmmerError : Repr OmmerError := ⟨instReprOmmerError.reprPrec⟩

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

The codes start at 201, above the codes of RLP and receipt errors, so that none of them meet.

Proof-of-work errors hold the codes 221 to 223, and ommer errors the codes 231 to 243.

A new constructor takes a new code, so that each code keeps its meaning. -/
def BlockError.code : BlockError → UInt32
  | .genesisNumber => 201
  | .wrongExcessBlobGas _ _ => 202
  | .gasUsedAboveLimit .. => 203
  | .invalidGasLimit .. => 204
  | .wrongBaseFee _ _ => 205
  | .timestampNotAfterParent .. => 206
  | .wrongNumber .. => 207
  | .extraDataTooLong .. => 208
  | .nonzeroDifficulty .. => 209
  | .nonzeroNonce .. => 210
  | .wrongOmmersHash .. => 211
  | .wrongParentHash .. => 212
  | .encoding _ => 213
  | .blockTooLarge _ => 214
  | .wrongDifficulty _ _ => 215
  | .proofOfWork _ => 216
  | .parentBeforeLondon .. => 217
  | .systemContractEmpty _ => 218
  | .systemCallFailed .. => 219
  | .aborted _ => 220
  | .invalidTransaction .. => 224
  | .wrongFork .. => 225
  | .noParent => 226
  | .ommersAfterParis .. => 227
  | .wrongDaoExtraData .. => 228
  | .deposit _ => 229
  | .trie _ => 230
  | .wrongGasUsed .. => 244
  | .wrongTransactionsRoot .. => 245
  | .wrongStateRoot .. => 246
  | .wrongReceiptRoot .. => 247
  | .wrongBloom .. => 248
  | .wrongWithdrawalsRoot .. => 249
  | .wrongBlobGasUsed .. => 250
  | .wrongRequestsHash .. => 251
  | .ommers _ => 252
  | .state _ => 253
  | .undecodableTransaction .. => 254
  | .blockAccessList _ => 255
  | .wrongBlockAccessListHash .. => 256

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 231, above the codes of the header and proof-of-work errors. -/
def OmmerError.code : OmmerError → UInt32
  | .wrongOmmersHash .. => 231
  | .numberOutOfRange .. => 232
  | .parentMissing .. => 233
  | .invalidHeader _ => 234
  | .tooManyOmmers .. => 235
  | .duplicateOmmer .. => 236
  | .ommerInChain .. => 237
  | .ommerAlreadyIncluded .. => 238
  | .wrongAge .. => 239
  | .parentNotRecent .. => 240
  | .siblingOfBlock .. => 241
  | .encoding _ => 242
  | .wrongDaoExtraData .. => 243

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
    if .paris ≤ fork then
      [(decide (.london ≤ parentFork), BlockError.parentBeforeLondon parentFork)]
    else []
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
      [(decide (header.difficulty = 0), BlockError.nonzeroDifficulty header.difficulty),
        (decide (header.nonce = Vector.replicate 8 0), .nonzeroNonce header.nonce),
        (decide (header.ommersHash = EMPTY_OMMER_HASH), .wrongOmmersHash header.ommersHash)]
  let parentHashCheck :=
    match parent.hash with
    | .ok parentHash =>
      (decide (header.parentHash = parentHash),
        BlockError.wrongParentHash (some parentHash) header.parentHash)
    | .error e => (false, BlockError.encoding e)
  parentCheck ++ [(decide (1 ≤ header.number), .genesisNumber)] ++ excessCheck ++
    [(decide (header.gasUsed ≤ header.gasLimit),
        .gasUsedAboveLimit header.gasUsed header.gasLimit),
      (GasLimit.checkGasLimitAcross parentFork fork header.gasLimit parent.gasLimit,
        .invalidGasLimit header.gasLimit parent.gasLimit)] ++ baseFeeCheck ++
    [(decide (parent.timestamp.toNat < header.timestamp.toNat),
        .timestampNotAfterParent header.timestamp.toNat parent.timestamp.toNat),
      (decide (header.number = parent.number + 1), .wrongNumber (parent.number + 1) header.number),
      (decide (header.extraData.size ≤ MAX_EXTRA_DATA_BYTES),
        .extraDataTooLong header.extraData.size)] ++
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

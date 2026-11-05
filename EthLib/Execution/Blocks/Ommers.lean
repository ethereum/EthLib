module

public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Blocks.Validate

/-!
# `Blocks.Ommers`

The ommers of a block before Paris: valid headers of recent blocks that the chain left out.

A block holds at most two ommers, and its header commits to them by the ommers hash.

Each ommer is a valid header, from one to six blocks older than the block.

Its parent is a recent block of the chain, but not the parent of the block itself.

No ommer is a block of the chain, an ommer of a recent block, or twice in the block.

Section 11.1 of the Yellow Paper, Berlin version, defines the rule: [`Paper.tex`][yp].

The checks here are stricter, as clients are: no ommer may be an ommer of any recent block.

The Yellow Paper excludes only the ommers of the block whose sibling the ommer is.

[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The most ommers of a block. -/
def MAX_OMMERS : Nat := 2

/-- The most blocks by which an ommer can be older than the block that holds it. -/
def MAX_OMMER_DEPTH : Nat := 6

/-- A block of the recent chain: its fork, its header and its ommers. -/
structure RecentBlock where
  /-- The fork of the block. -/
  fork : Fork
  /-- The header of the block. -/
  header : Header fork
  /-- The headers of the ommers of the block. -/
  ommers : List (Header fork)

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
  deriving Repr

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

/-- The hash of a header, with its encoding error as an ommer error. -/
def headerHash {fork : Fork} (h : Header fork) : Except OmmerError Hash32 :=
  h.hash.mapError .encoding

/-- Fail with an error unless a condition holds. -/
def ensure (condition : Bool) (error : OmmerError) : Except OmmerError Unit :=
  if condition then .ok () else .error error

/-- Check one ommer as a header against its parent, the recent block one number below it.

With the seal check off, the proof of work is left out, as for chains that run without one. -/
def checkOmmerHeader {fork : Fork} (checkSeal : Bool) (recent : List RecentBlock)
    (ommer : Header fork) : Except OmmerError Unit := do
  let some parent := recent.find? (·.header.number + 1 = ommer.number)
    | .error .parentMissing
  if hFork : parent.fork ≤ fork then
    let check := if checkSeal then validateHeader hFork parent.header ommer
      else checkHeader hFork parent.header ommer
    check.mapError .invalidHeader
  else .error (.invalidHeader .wrongParentHash)

/-- Check the ommers of a block, as section 11.1 of the Yellow Paper asks.

The recent chain is the last seven blocks, ending with the parent of the block, in order.

The checks run in a fixed order, and the first that fails gives the error. -/
def validateOmmers {fork : Fork} (checkSeal : Bool) (recent : List RecentBlock)
    (header : Header fork) (ommers : List (Header fork)) : Except OmmerError Unit := do
  let encoded ← (encode (Codec.toItem ommers)).mapError .encoding
  ensure (keccak256 encoded == header.ommersHash) .wrongOmmersHash
  ommers.forM fun ommer => do
    ensure (1 ≤ ommer.number && ommer.number < header.number) .numberOutOfRange
    checkOmmerHeader checkSeal recent ommer
  ensure (ommers.length ≤ MAX_OMMERS) .tooManyOmmers
  let ommerHashes ← ommers.mapM headerHash
  ensure ommerHashes.Nodup .duplicateOmmer
  let blockHash ← headerHash header
  let recentHashes ← recent.mapM fun b => headerHash b.header
  let recentOmmerHashes ← (recent.flatMap fun b => b.ommers.map headerHash).mapM id
  (ommers.zip ommerHashes).forM fun (ommer, hash) => do
    ensure (hash != blockHash && !recentHashes.contains hash) .ommerInChain
    ensure (!recentOmmerHashes.contains hash) .ommerAlreadyIncluded
    let age := header.number - ommer.number
    ensure (1 ≤ age && age ≤ MAX_OMMER_DEPTH) .wrongAge
    ensure (recentHashes.contains ommer.parentHash) .parentNotRecent
    ensure (ommer.parentHash != header.parentHash) .siblingOfBlock

end EthLib.Execution.Blocks

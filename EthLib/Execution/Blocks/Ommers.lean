module

public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Blocks.DaoFork
public import EthLib.Execution.Blocks.Validate

/-!
# `Blocks.Ommers`

The ommers of a block before Paris: valid headers of recent blocks that the chain left out.

A block holds at most two ommers, and its header commits to them by the ommers hash.

Each ommer is a valid header, from one to six blocks older than the block.

It is a header at the fork of its own number, which can be a fork before the block's.

Its parent is a recent block of the chain, but not the parent of the block itself.

No ommer is a block of the chain, an ommer of a recent block, or twice in the block.

Section 11.1 of the Yellow Paper, Berlin version, defines the rule: [`Paper.tex`][yp].

The checks here are stricter, as clients are: no ommer may be an ommer of any recent block.

The Yellow Paper excludes only the ommers of the block whose sibling the ommer is.

An ommer in the first ten blocks of the DAO Fork also carries the extra data of that fork.

[EIP-779][eip-779] states the rule for blocks, and cites the [specification][dao] of the fork.

It states the rule for block headers, so that clients with headers only can tell the chains apart.

So the rule covers every header in those ten blocks, and an ommer is such a header.

[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[eip-779]: https://eips.ethereum.org/EIPS/eip-779#specification
[dao]: https://web.archive.org/web/20180310140717/https://blog.slock.it/hard-fork-specification-24b889e70703
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
  /-- The headers of the ommers of the block, each with the fork of its own number. -/
  ommers : List ((f : Fork) × Header f)

/-- The hash of a header, with its encoding error as an ommer error. -/
def headerHash {fork : Fork} (h : Header fork) : Except OmmerError Hash32 :=
  h.hash.mapError .encoding

/-- Check one ommer as a header at its own fork, against its parent, the recent block one below it.

With the seal check off, the proof of work is left out, as for chains that run without one.

On a chain with the DAO Fork, the extra data rule of that fork applies to the ommer too. -/
def checkOmmerHeader (config : ChainConfig) (checkSeal : Bool) (recent : List RecentBlock)
    (ommer : (f : Fork) × Header f) : Except OmmerError Unit := do
  let some parent := recent.find? (·.header.number + 1 = ommer.2.number)
    | .error .parentMissing
  if hFork : parent.fork ≤ ommer.1 then
    let check := if checkSeal then validateHeader hFork parent.header ommer.2
      else checkHeader hFork parent.header ommer.2
    check.mapError .invalidHeader
  else .error (.invalidHeader .wrongParentHash)
  ensure (daoExtraDataValid config ommer.2) .wrongDaoExtraData

/-- Check the ommers of a block, as section 11.1 of the Yellow Paper asks.

The chain configuration gives the block of the DAO Fork.

The recent chain ends with the parent of the block, oldest first, and the checks read all of it.

The checks run in a fixed order, and the first that fails gives the error. -/
def validateOmmers {fork : Fork} (config : ChainConfig) (checkSeal : Bool)
    (recent : List RecentBlock) (header : Header fork) (ommers : List ((f : Fork) × Header f)) :
    Except OmmerError Unit := do
  let encoded ← (encode (ommersItem ommers)).mapError .encoding
  ensure (keccak256 encoded == header.ommersHash) .wrongOmmersHash
  ommers.forM fun ommer => do
    ensure (1 ≤ ommer.2.number && ommer.2.number < header.number) .numberOutOfRange
    checkOmmerHeader config checkSeal recent ommer
  ensure (ommers.length ≤ MAX_OMMERS) .tooManyOmmers
  let ommerHashes ← ommers.mapM (headerHash ·.2)
  ensure ommerHashes.Nodup .duplicateOmmer
  let blockHash ← headerHash header
  let recentHashes ← recent.mapM fun b => headerHash b.header
  let recentOmmerHashes ← (recent.flatMap fun b => b.ommers.map (headerHash ·.2)).mapM id
  (ommers.zip ommerHashes).forM fun (ommer, hash) => do
    ensure (hash != blockHash && !recentHashes.contains hash) .ommerInChain
    ensure (!recentOmmerHashes.contains hash) .ommerAlreadyIncluded
    let age := header.number - ommer.2.number
    ensure (1 ≤ age && age ≤ MAX_OMMER_DEPTH) .wrongAge
    ensure (recentHashes.contains ommer.2.parentHash) .parentNotRecent
    ensure (ommer.2.parentHash != header.parentHash) .siblingOfBlock

end EthLib.Execution.Blocks

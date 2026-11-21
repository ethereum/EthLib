module

public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Blocks.DaoFork
public import EthLib.Execution.Blocks.Validate

/-!
# `Blocks.Ommers`

The ommers of a block before Paris: valid headers of recent blocks that the chain left out.

Section 11.1 of the [Yellow Paper][yp], Berlin version, defines the rule.

[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The most ommers of a block, by section 11.1 of the Yellow Paper. -/
def MAX_OMMERS : Nat := 2

/-- The most blocks by which an ommer can be older than the block that holds it, by section 11.1. -/
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

The fork of the ommer is that of its own number, which can be a fork before the block's.

With the seal check off, the proof of work is left out, as for chains that run without one.

An ommer in the first ten blocks of the DAO Fork also carries the extra data of that fork.

[EIP-779][eip-779] states that rule for every block header.

It cites the [specification][dao] of the fork.

So clients with headers only can tell the chains apart, and an ommer is such a header.

[eip-779]: https://eips.ethereum.org/EIPS/eip-779#specification
[dao]: https://web.archive.org/web/20180310140717/https://blog.slock.it/hard-fork-specification-24b889e70703
-/
def checkOmmerHeader (config : ChainConfig) (checkSeal : Bool) (recent : List RecentBlock)
    (ommer : (f : Fork) × Header f) : Except OmmerError Unit := do
  -- The parent is the recent block one below the ommer's number.
  let some parent := recent.find? (·.header.number + 1 = ommer.2.number)
    | .error (.parentMissing ommer.2.number)
  if hFork : parent.fork ≤ ommer.1 then
    -- The header rules of the ommer's fork, with or without the proof of work.
    let check := if checkSeal then validateHeader hFork parent.header ommer.2
      else checkHeader hFork parent.header ommer.2
    check.mapError .invalidHeader
  -- A parent at a later fork than the ommer cannot be its parent.
  else .error (.invalidHeader
    (.wrongParentHash parent.header.hash.toOption ommer.2.parentHash))
  ensure (daoExtraDataValid config ommer.2) (.wrongDaoExtraData ommer.2.extraData)

/-- Check the ommers of a block, as section 11.1 of the Yellow Paper asks.

The chain configuration gives the block of the DAO Fork.

The recent chain ends with the parent of the block, oldest first, and the checks read all of it.

The checks run in a fixed order, and the first that fails gives the error.

They are stricter than the Yellow Paper, as clients are.

No ommer may be an ommer of any recent block.

The Yellow Paper excludes only the ommers of the block whose sibling the ommer is. -/
def validateOmmers {fork : Fork} (config : ChainConfig) (checkSeal : Bool)
    (recent : List RecentBlock) (header : Header fork) (ommers : List ((f : Fork) × Header f)) :
    Except OmmerError Unit := do
  -- The header commits to its ommers by the hash of their list.
  let encoded ← (encode (ommersItem ommers)).mapError .encoding
  ensure (keccak256 encoded == header.ommersHash)
    (.wrongOmmersHash header.ommersHash (keccak256 encoded))
  -- Each ommer is a valid header, numbered below the block.
  ommers.forM fun ommer => do
    ensure (1 ≤ ommer.2.number && ommer.2.number < header.number)
      (.numberOutOfRange ommer.2.number header.number)
    checkOmmerHeader config checkSeal recent ommer
  -- At most two ommers.
  ensure (ommers.length ≤ MAX_OMMERS) (.tooManyOmmers ommers.length)
  let ommerHashes ← ommers.mapM (headerHash ·.2)
  -- At most two ommers are left, so two equal hashes make the first hash the repeated one.
  ensure ommerHashes.Nodup (.duplicateOmmer (ommerHashes.headD 0))
  -- The hashes of the block, of the recent chain and of its ommers.
  let blockHash ← headerHash header
  let recentHashes ← recent.mapM fun b => headerHash b.header
  let recentOmmerHashes ← (recent.flatMap fun b => b.ommers.map (headerHash ·.2)).mapM id
  (ommers.zip ommerHashes).forM fun (ommer, hash) => do
    -- No ommer is a block of the chain.
    ensure (hash != blockHash && !recentHashes.contains hash) (.ommerInChain hash)
    -- No ommer is an ommer of a recent block, which is stricter than the Yellow Paper.
    ensure (!recentOmmerHashes.contains hash) (.ommerAlreadyIncluded hash)
    -- An ommer is one to six blocks older than the block.
    let age := header.number - ommer.2.number
    ensure (1 ≤ age && age ≤ MAX_OMMER_DEPTH) (.wrongAge hash age)
    -- Its parent is a recent block of the chain.
    ensure (recentHashes.contains ommer.2.parentHash) (.parentNotRecent hash ommer.2.parentHash)
    -- But not the parent of the block itself, which would make it a sibling.
    ensure (ommer.2.parentHash != header.parentHash) (.siblingOfBlock hash)

end EthLib.Execution.Blocks

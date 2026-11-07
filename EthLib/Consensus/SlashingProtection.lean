module

public import Lean.Data.Json
public import EthLib.Base.Except
public import EthLib.Consensus.Types
public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Serialization.Ssz.Codec.Json

/-!
# `Consensus.SlashingProtection`

The slashing protection of a signer, and the file that moves it between clients.

[EIP-3076] specifies both.

At the pinned text of EIP-3076 its status is Last Call.

A validator is slashed for two blocks of one slot.

It is also slashed for two votes that Casper FFG forbids together.

So a signer keeps a record of what it signed, and refuses to sign a message that conflicts with it.

The interchange file holds that record.

For each key, it holds the slots of its blocks and the epochs of its votes.

Each record may carry the signing root of its message, so that the same message can be signed again.

A signer that imports a file must refuse a message that breaks one of five conditions:

- A block conflicts with a recorded block of its slot.
- A block has a slot at most the least recorded slot, and is not a repeat.
- A vote is slashable with a recorded vote.
- A vote has a source epoch below the least recorded source epoch.
- A vote has a target epoch at most the least recorded target epoch, and is not a repeat.

A record holds the epochs of a vote and not its data.

So a vote is compared through its signing root.

Two votes with one target and different signing roots are a double vote.

So is a recorded vote without a signing root and a new vote with its target.

The file reads integers as decimal digits in strings, and keys and roots as `0x` hex.

The EIP leaves out several checks, and so does this module:

- It does not compare the genesis validators root of a file with that of the chain.
- It does not reject a file whose own records are slashable with each other.
- It keeps no low watermark, so it cannot see a gap between two imported files.
- It does not ask for the records of a key to be sorted, or for a key to appear once.

[EIP-3076]: https://eips.ethereum.org/EIPS/eip-3076
-/

@[expose] public section

namespace EthLib.Consensus

open Lean Base Cryptography.Bls

/-! ## The interchange file -/

/-- The version of the interchange format that this module reads and writes. -/
def INTERCHANGE_FORMAT_VERSION : String := "5"

/-- A block that a key signed: its slot, and the signing root when the file has it. -/
structure SignedBlockRecord where
  /-- The slot of the block. -/
  slot : Slot
  /-- The signing root of the block. -/
  signingRoot : Option Root
  deriving DecidableEq, Repr

/-- A vote that a key signed: its source and target epochs, and the signing root when known. -/
structure SignedAttestationRecord where
  /-- The epoch of the source checkpoint of the vote. -/
  sourceEpoch : Epoch
  /-- The epoch of the target checkpoint of the vote. -/
  targetEpoch : Epoch
  /-- The signing root of the attestation data. -/
  signingRoot : Option Root
  deriving DecidableEq, Repr

/-- What one key signed. -/
structure InterchangeEntry where
  /-- The public key. -/
  pubkey : BLSPubkey
  /-- The blocks it signed. -/
  signedBlocks : List SignedBlockRecord
  /-- The votes it signed. -/
  signedAttestations : List SignedAttestationRecord
  deriving DecidableEq, Repr

/-- An interchange file: its chain, by its genesis validators root, and what each key signed. -/
structure Interchange where
  /-- The genesis validators root of the chain. -/
  genesisValidatorsRoot : Root
  /-- What the keys signed, one entry at a time. -/
  data : List InterchangeEntry
  deriving DecidableEq, Repr

/-- Why an interchange file does not read, or why a signer refuses a message. -/
inductive SlashingProtectionError where
  /-- A field is missing, has the wrong JSON type, or has a malformed value. -/
  | field (path : String)
  /-- The file names a version of the format other than the one read here. -/
  | version (found : String)
  /-- A block conflicts with a recorded block of its slot. -/
  | slashableBlock (slot : Slot)
  /-- A block has a slot at most the least recorded slot, and is not a repeat. -/
  | blockSlotTooLow (slot minimum : Slot)
  /-- A vote is slashable with a recorded vote. -/
  | slashableAttestation (sourceEpoch targetEpoch : Epoch)
  /-- A vote has a source epoch below the least recorded source epoch. -/
  | sourceEpochTooLow (sourceEpoch minimum : Epoch)
  /-- A vote has a target epoch at most the least recorded target epoch, and is not a repeat. -/
  | targetEpochTooLow (targetEpoch minimum : Epoch)
  deriving DecidableEq, Repr

/-- The code of an error at the C boundary, one for each constructor. -/
def SlashingProtectionError.code : SlashingProtectionError → UInt32
  | .field _ => 1
  | .version _ => 2
  | .slashableBlock _ => 3
  | .blockSlotTooLow .. => 4
  | .slashableAttestation .. => 5
  | .sourceEpochTooLow .. => 6
  | .targetEpochTooLow .. => 7

/-! ## Reading and writing the file -/

namespace Interchange

/-- A field of an object, which must be present. -/
def field (path name : String) (document : Json) :
    Except SlashingProtectionError Json :=
  match document.getObjVal? name with
  | .ok value => .ok value
  | .error _ => .error (.field s!"{path}.{name}")

/-- A string. -/
def readString (path : String) : Json → Except SlashingProtectionError String
  | .str text => .ok text
  | _ => .error (.field path)

/-- A 64-bit integer, written as decimal digits in a string with no sign or leading zero. -/
def readUInt64 (path : String) (document : Json) : Except SlashingProtectionError UInt64 := do
  let text ← readString path document
  match Serialization.Ssz.readNat (.str text) with
  | .ok n => if n < 2 ^ 64 then .ok n.toUInt64 else .error (.field path)
  | .error _ => .error (.field path)

/-- A fixed number of bytes, written as `0x` hex in a string, in either letter case. -/
def readBytes (path : String) (size : Nat) (document : Json) :
    Except SlashingProtectionError (Vector UInt8 size) := do
  let text ← readString path document
  match Serialization.Ssz.ofHex text with
  | .ok bytes => if sized : bytes.size = size then .ok ⟨bytes, sized⟩ else .error (.field path)
  | .error _ => .error (.field path)

/-- An array, each element read in turn. -/
def readArray {α : Type} (path : String) (read : String → Json → Except SlashingProtectionError α) :
    Json → Except SlashingProtectionError (List α)
  | .arr elements =>
    (elements.toList.zipIdx).mapM fun (element, index) => read s!"{path}[{index}]" element
  | _ => .error (.field path)

/-- The signing root of a record, which the file may leave out. -/
def readSigningRoot (path : String) (document : Json) :
    Except SlashingProtectionError (Option Root) :=
  match document.getObjVal? "signing_root" with
  | .ok value => do return some (← readBytes s!"{path}.signing_root" 32 value)
  | .error _ => .ok none

/-- A signed block, from its object. -/
def readBlock (path : String) (document : Json) :
    Except SlashingProtectionError SignedBlockRecord := do
  return {
    slot := ← readUInt64 s!"{path}.slot" (← field path "slot" document)
    signingRoot := ← readSigningRoot path document }

/-- A signed vote, from its object. -/
def readAttestation (path : String) (document : Json) :
    Except SlashingProtectionError SignedAttestationRecord := do
  return {
    sourceEpoch := ← readUInt64 s!"{path}.source_epoch" (← field path "source_epoch" document)
    targetEpoch := ← readUInt64 s!"{path}.target_epoch" (← field path "target_epoch" document)
    signingRoot := ← readSigningRoot path document }

/-- What one key signed, from its object. -/
def readEntry (path : String) (document : Json) :
    Except SlashingProtectionError InterchangeEntry := do
  return {
    pubkey := ← readBytes s!"{path}.pubkey" 48 (← field path "pubkey" document)
    signedBlocks := ← readArray s!"{path}.signed_blocks" readBlock
      (← field path "signed_blocks" document)
    signedAttestations := ← readArray s!"{path}.signed_attestations" readAttestation
      (← field path "signed_attestations" document) }

/-- An interchange file, from its JSON document.

The version must be the one of this format.

A field that the format does not name is ignored, as the schema of the EIP allows. -/
def ofJson (document : Json) : Except SlashingProtectionError Interchange := do
  let metadata ← field "" "metadata" document
  let version ← readString ".metadata.interchange_format_version"
    (← field ".metadata" "interchange_format_version" metadata)
  unless version = INTERCHANGE_FORMAT_VERSION do throw (.version version)
  return {
    genesisValidatorsRoot := ← readBytes ".metadata.genesis_validators_root" 32
      (← field ".metadata" "genesis_validators_root" metadata)
    data := ← readArray ".data" readEntry (← field "" "data" document) }

/-- A 64-bit integer as the file writes it. -/
def uint64Json (value : UInt64) : Json := Serialization.Ssz.decimal value.toNat

/-- Bytes as the file writes them, in lowercase hex. -/
def bytesJson {size : Nat} (bytes : Vector UInt8 size) : Json :=
  .str (Serialization.Ssz.toHex bytes.toArray)

/-- The fields of a signing root, none when it is not known. -/
def signingRootFields : Option Root → List (String × Json)
  | some root => [("signing_root", bytesJson root)]
  | none => []

/-- A signed block as the file writes it. -/
def blockJson (block : SignedBlockRecord) : Json :=
  Json.mkObj ([("slot", uint64Json block.slot)] ++ signingRootFields block.signingRoot)

/-- A signed vote as the file writes it. -/
def attestationJson (attestation : SignedAttestationRecord) : Json :=
  Json.mkObj ([("source_epoch", uint64Json attestation.sourceEpoch),
    ("target_epoch", uint64Json attestation.targetEpoch)] ++
      signingRootFields attestation.signingRoot)

/-- What one key signed, as the file writes it. -/
def entryJson (entry : InterchangeEntry) : Json :=
  Json.mkObj [("pubkey", bytesJson entry.pubkey),
    ("signed_blocks", .arr (entry.signedBlocks.map blockJson).toArray),
    ("signed_attestations", .arr (entry.signedAttestations.map attestationJson).toArray)]

/-- An interchange file as a JSON document, at the version of this format. -/
def toJson (interchange : Interchange) : Json :=
  Json.mkObj [
    ("metadata", Json.mkObj [
      ("interchange_format_version", .str INTERCHANGE_FORMAT_VERSION),
      ("genesis_validators_root", bytesJson interchange.genesisValidatorsRoot)]),
    ("data", .arr (interchange.data.map entryJson).toArray)]

/-! ## The records of a key -/

/-- The blocks that a key signed, from every entry with that key, in order. -/
def blocksOf (interchange : Interchange) (pubkey : BLSPubkey) : List SignedBlockRecord :=
  (interchange.data.filter (·.pubkey = pubkey)).flatMap (·.signedBlocks)

/-- The votes that a key signed, from every entry with that key, in order. -/
def attestationsOf (interchange : Interchange) (pubkey : BLSPubkey) :
    List SignedAttestationRecord :=
  (interchange.data.filter (·.pubkey = pubkey)).flatMap (·.signedAttestations)

/-- The record after a key signs a block, as one more entry of that key. -/
def recordBlock (interchange : Interchange) (pubkey : BLSPubkey) (slot : Slot)
    (signingRoot : Root) : Interchange :=
  { interchange with
    data := interchange.data ++ [⟨pubkey, [⟨slot, some signingRoot⟩], []⟩] }

/-- The record after a key signs a vote, as one more entry of that key. -/
def recordAttestation (interchange : Interchange) (pubkey : BLSPubkey)
    (sourceEpoch targetEpoch : Epoch) (signingRoot : Root) : Interchange :=
  { interchange with
    data := interchange.data ++ [⟨pubkey, [], [⟨sourceEpoch, targetEpoch, some signingRoot⟩]⟩] }

end Interchange

/-! ## The conditions -/

/-- The least slot of some signed blocks, none without a block. -/
def minBlockSlot (blocks : List SignedBlockRecord) : Option Slot :=
  (blocks.map (·.slot)).min?

/-- The least source epoch of some signed votes, none without a vote. -/
def minSourceEpoch (attestations : List SignedAttestationRecord) : Option Epoch :=
  (attestations.map (·.sourceEpoch)).min?

/-- The least target epoch of some signed votes, none without a vote. -/
def minTargetEpoch (attestations : List SignedAttestationRecord) : Option Epoch :=
  (attestations.map (·.targetEpoch)).min?

/-- Whether a block is a repeat: some record has its slot and carries its signing root.

A record without a signing root is the repeat of no block.

A record with the root but another slot is not a repeat, since the root commits to the slot. -/
def isRepeatBlock (blocks : List SignedBlockRecord) (slot : Slot) (signingRoot : Root) : Bool :=
  blocks.any fun block => block.slot == slot && block.signingRoot == some signingRoot

/-- Whether a vote is a repeat: some record has its two epochs and carries its signing root.

A record without a signing root is the repeat of no vote.

A record with the root but other epochs is not a repeat, since the root commits to them. -/
def isRepeatAttestation (attestations : List SignedAttestationRecord)
    (sourceEpoch targetEpoch : Epoch) (signingRoot : Root) : Bool :=
  attestations.any fun attestation =>
    attestation.sourceEpoch == sourceEpoch && attestation.targetEpoch == targetEpoch &&
      attestation.signingRoot == some signingRoot

/-- Whether a recorded block conflicts with a new block of a slot and a signing root.

The two are slashable when they have one slot and are different blocks.

A record without a signing root conflicts with every new block of its slot, as the EIP asks. -/
def SignedBlockRecord.conflictsWith (block : SignedBlockRecord) (slot : Slot)
    (signingRoot : Root) : Bool :=
  block.slot == slot && block.signingRoot != some signingRoot

/-- Whether a recorded vote is slashable with a new vote of two epochs and a signing root.

A double vote has one target epoch and is a different vote, so its signing root differs.

A record without a signing root is a different vote from every new vote.

A surround vote has a source and a target strictly around those of the other vote, either way. -/
def SignedAttestationRecord.isSlashableWith (attestation : SignedAttestationRecord)
    (sourceEpoch targetEpoch : Epoch) (signingRoot : Root) : Bool :=
  (attestation.targetEpoch == targetEpoch && attestation.signingRoot != some signingRoot) ||
    (sourceEpoch < attestation.sourceEpoch && attestation.targetEpoch < targetEpoch) ||
    (attestation.sourceEpoch < sourceEpoch && targetEpoch < attestation.targetEpoch)

/-- The second condition: a block is after the least recorded slot, or is a repeat. -/
def checkBlockSlot (blocks : List SignedBlockRecord) (slot : Slot) (signingRoot : Root) :
    Except SlashingProtectionError Unit :=
  match minBlockSlot blocks with
  | some minimum =>
    ensure (minimum < slot ∨ isRepeatBlock blocks slot signingRoot)
      (.blockSlotTooLow slot minimum)
  | none => .ok ()

/-- Whether a key may sign a block, under the first two conditions, given the blocks it signed.

It refuses a block that conflicts with a recorded one, then a block not after the least slot.

A repeat of a recorded block passes the second check.

It does not check the slot against the clock or the chain. -/
def checkBlockSigning (blocks : List SignedBlockRecord) (slot : Slot) (signingRoot : Root) :
    Except SlashingProtectionError Unit := do
  ensure (∀ block ∈ blocks, block.conflictsWith slot signingRoot = false) (.slashableBlock slot)
  checkBlockSlot blocks slot signingRoot

/-- The fourth condition: a vote has a source epoch at least the least recorded one. -/
def checkSourceEpoch (attestations : List SignedAttestationRecord) (sourceEpoch : Epoch) :
    Except SlashingProtectionError Unit :=
  match minSourceEpoch attestations with
  | some minimum => ensure (minimum ≤ sourceEpoch) (.sourceEpochTooLow sourceEpoch minimum)
  | none => .ok ()

/-- The fifth condition: a vote has a target epoch after the least recorded one, or is a repeat. -/
def checkTargetEpoch (attestations : List SignedAttestationRecord)
    (sourceEpoch targetEpoch : Epoch) (signingRoot : Root) : Except SlashingProtectionError Unit :=
  match minTargetEpoch attestations with
  | some minimum =>
    ensure (minimum < targetEpoch ∨
        isRepeatAttestation attestations sourceEpoch targetEpoch signingRoot)
      (.targetEpochTooLow targetEpoch minimum)
  | none => .ok ()

/-- Whether a key may sign a vote, under the last three conditions, given the votes it signed.

It refuses a vote slashable with a recorded one, then a vote before the least source epoch.

It then refuses a vote not after the least target epoch, unless it is a repeat.

It does not check that the source epoch is at most the target epoch. -/
def checkAttestationSigning (attestations : List SignedAttestationRecord)
    (sourceEpoch targetEpoch : Epoch) (signingRoot : Root) :
    Except SlashingProtectionError Unit := do
  ensure (∀ attestation ∈ attestations,
      attestation.isSlashableWith sourceEpoch targetEpoch signingRoot = false)
    (.slashableAttestation sourceEpoch targetEpoch)
  checkSourceEpoch attestations sourceEpoch
  checkTargetEpoch attestations sourceEpoch targetEpoch signingRoot

namespace Interchange

/-- Whether a key may sign a block, given the blocks of every entry of that key. -/
def checkBlock (interchange : Interchange) (pubkey : BLSPubkey) (slot : Slot)
    (signingRoot : Root) : Except SlashingProtectionError Unit :=
  checkBlockSigning (interchange.blocksOf pubkey) slot signingRoot

/-- Whether a key may sign a vote, given the votes of every entry of that key. -/
def checkAttestation (interchange : Interchange) (pubkey : BLSPubkey)
    (sourceEpoch targetEpoch : Epoch) (signingRoot : Root) :
    Except SlashingProtectionError Unit :=
  checkAttestationSigning (interchange.attestationsOf pubkey) sourceEpoch targetEpoch
    signingRoot

/-- The record after importing a file, for a signer that keeps every message.

The entries of the file come after those already held.

It does not compare the genesis validators roots of the two. -/
def importFile (held file : Interchange) : Interchange :=
  { held with data := held.data ++ file.data }

end Interchange

end EthLib.Consensus

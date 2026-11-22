module

public import Lean.Data.Json
public import Std.Data.TreeMap
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

A signer that imports a file must refuse a message that breaks one of the five conditions.

The checked import refuses a file of another chain, which the conditions of the EIP leave out.

The [schema of the EIP][schema] says that the root serves to uniquely identify the chain.

The [interchange tests][tests] refuse such a file.

The conditions of the EIP leave out two more checks, and so does this module:

- It does not reject a file whose own records are slashable with each other.
- It does not ask for the records of a key to be sorted, or for a key to appear once.

Import follows the minimal strategy of the EIP, in its section Advice for Minimal Databases.

[EIP-3076]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3076.md
[schema]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3076.md#L49
[tests]: https://github.com/eth-clients/slashing-protection-interchange-tests/blob/bb7900688eecd287d8723154faac6addb5e63336/tests/generated/wrong_genesis_validators_root.json
-/

@[expose] public section

namespace EthLib.Consensus

open Lean Base Cryptography.Bls

/-! ## The interchange file -/

/-- The version of the interchange format that this module reads and writes. -/
def INTERCHANGE_FORMAT_VERSION : String := "5"

/-- A block slot and optional signing root, or an imported slot limit without a root. -/
structure SignedBlockRecord where
  /-- The slot of the block. -/
  slot : Slot
  /-- The signing root of the block. -/
  signingRoot : Option Root
  deriving DecidableEq, Repr

/-- A vote's epochs and optional signing root, or imported epoch limits without a root. -/
structure SignedAttestationRecord where
  /-- The epoch of the source checkpoint of the vote. -/
  sourceEpoch : Epoch
  /-- The epoch of the target checkpoint of the vote. -/
  targetEpoch : Epoch
  /-- The signing root of the attestation data. -/
  signingRoot : Option Root
  deriving DecidableEq, Repr

/-- The message records or imported limits of one key. -/
structure InterchangeEntry where
  /-- The public key. -/
  pubkey : BLSPubkey
  /-- Its signed blocks, or its imported slot limit. -/
  signedBlocks : List SignedBlockRecord
  /-- Its signed votes, or one imported limit on source and target epochs. -/
  signedAttestations : List SignedAttestationRecord
  deriving DecidableEq, Repr

/-- An interchange file: its chain, by its genesis validators root, and the records of its keys. -/
structure Interchange where
  /-- The genesis validators root of the chain. -/
  genesisValidatorsRoot : Root
  /-- The records of the keys, one entry at a time. -/
  data : List InterchangeEntry
  deriving DecidableEq, Repr

open scoped HexRepr

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
  /-- A file has the genesis validators root of another chain than the signer's. -/
  | wrongChain (expected actual : Root)
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
  | .wrongChain .. => 8

/-! ## Reading and writing the file -/

namespace Interchange

/-- A field of an object, which must be present. -/
def field (path name : String) (document : Json) :
    Except SlashingProtectionError Json :=
  -- The schema: a required property is present.
  match document.getObjVal? name with
  | .ok value => .ok value
  | .error _ => .error (.field s!"{path}.{name}")

/-- A string. -/
def readString (path : String) : Json → Except SlashingProtectionError String
  -- The schema: the type is string.
  | .str text => .ok text
  | _ => .error (.field path)

/-- A 64-bit integer, written as decimal digits in a string with no sign or leading zero. -/
def readUInt64 (path : String) (document : Json) : Except SlashingProtectionError UInt64 := do
  -- The schema: the type is string.
  --
  -- Rationale, Integer Representation: a string keeps a 64-bit integer whole in every language.
  let text ← readString path document
  -- The EIP sets no format for the digits.
  --
  -- EthLib reads base 10 with no sign or leading zero, as the example of the EIP writes them.
  match Serialization.Ssz.readNat (.str text) with
  -- The EIP sets no bound; EthLib refuses `2^64` and above, since a slot or an epoch has 64 bits.
  | .ok n => if n < 2 ^ 64 then .ok n.toUInt64 else .error (.field path)
  | .error _ => .error (.field path)

/-- A fixed number of bytes, written as `0x` hex in a string, in either letter case. -/
def readBytes (path : String) (size : Nat) (document : Json) :
    Except SlashingProtectionError (Vector UInt8 size) := do
  -- The schema: the type is string.
  let text ← readString path document
  -- The schema writes the key in `0x`-prefixed hex, and the example of the EIP writes the roots so.
  match Serialization.Ssz.ofHex text with
  -- The EIP sets no length, so EthLib asks for the size of the type.
  --
  -- That is 48 bytes for a key and 32 bytes for a root.
  | .ok bytes => exactBytes size ⟨bytes⟩ fun _ => .field path
  | .error _ => .error (.field path)

/-- An array, each element read in turn. -/
def readArray {α : Type} (path : String) (read : String → Json → Except SlashingProtectionError α) :
    Json → Except SlashingProtectionError (List α)
  -- The schema: the type is array.
  --
  -- The schema lists one schema for the items, which JSON Schema applies to the first item only.
  --
  -- EthLib reads every item with that schema, since the conditions read every block and vote.
  | .arr elements =>
    (elements.toList.zipIdx).mapM fun (element, index) => read s!"{path}[{index}]" element
  | _ => .error (.field path)

/-- The signing root of a record, which the file may leave out. -/
def readSigningRoot (path : String) (document : Json) :
    Except SlashingProtectionError (Option Root) :=
  -- The schema: the signing root is optional, in a block as in a vote.
  match document.getObjVal? "signing_root" with
  | .ok value => do return some (← readBytes s!"{path}.signing_root" 32 value)
  | .error _ => .ok none

/-- A signed block, from its object. -/
def readBlock (path : String) (document : Json) :
    Except SlashingProtectionError SignedBlockRecord := do
  -- The schema: the slot is required, and the signing root is not.
  return {
    slot := ← readUInt64 s!"{path}.slot" (← field path "slot" document)
    signingRoot := ← readSigningRoot path document }

/-- A signed vote, from its object. -/
def readAttestation (path : String) (document : Json) :
    Except SlashingProtectionError SignedAttestationRecord := do
  -- The schema: the source epoch and the target epoch are required, and the signing root is not.
  return {
    sourceEpoch := ← readUInt64 s!"{path}.source_epoch" (← field path "source_epoch" document)
    targetEpoch := ← readUInt64 s!"{path}.target_epoch" (← field path "target_epoch" document)
    signingRoot := ← readSigningRoot path document }

/-- The records of one key, from its object. -/
def readEntry (path : String) (document : Json) :
    Except SlashingProtectionError InterchangeEntry := do
  -- The schema: the key, its signed blocks and its signed votes are required.
  --
  -- The key is the BLS public key of the validator, in `0x`-prefixed hex.
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
  -- The schema: the metadata and the data are required.
  let metadata ← field "" "metadata" document
  -- The schema: the metadata holds the version of the format, a string.
  let version ← readString ".metadata.interchange_format_version"
    (← field ".metadata" "interchange_format_version" metadata)
  -- Additional Information: the version is 5.
  --
  -- Backwards Compatibility: the EIP is not compatible with the drafts below 5.
  --
  -- The EIP does not say how to treat another version; EthLib refuses it.
  unless version = INTERCHANGE_FORMAT_VERSION do throw (.version version)
  -- The schema: the metadata also holds the genesis validators root, and the data is an array.
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
  -- The schema does not require the signing root, so an unknown one is left out.
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

/-- The records of one key, as the file writes it. -/
def entryJson (entry : InterchangeEntry) : Json :=
  Json.mkObj [("pubkey", bytesJson entry.pubkey),
    ("signed_blocks", .arr (entry.signedBlocks.map blockJson).toArray),
    ("signed_attestations", .arr (entry.signedAttestations.map attestationJson).toArray)]

/-- An interchange file as a JSON document, at the version of this format. -/
def toJson (interchange : Interchange) : Json :=
  -- Additional Information: the version is 5.
  Json.mkObj [
    ("metadata", Json.mkObj [
      ("interchange_format_version", .str INTERCHANGE_FORMAT_VERSION),
      ("genesis_validators_root", bytesJson interchange.genesisValidatorsRoot)]),
    ("data", .arr (interchange.data.map entryJson).toArray)]

/-! ## The records of a key -/

/-- The block records of a key, from every entry with that key, in order. -/
def blocksOf (interchange : Interchange) (pubkey : BLSPubkey) : List SignedBlockRecord :=
  -- Conditions 1 and 2 read the blocks of the key of the proposer.
  --
  -- The EIP does not say that a key has one entry, so every entry of the key counts.
  (interchange.data.filter (·.pubkey = pubkey)).flatMap (·.signedBlocks)

/-- The vote records of a key, from every entry with that key, in order. -/
def attestationsOf (interchange : Interchange) (pubkey : BLSPubkey) :
    List SignedAttestationRecord :=
  -- Conditions 3 to 5 read the votes of the key of the attester, from every entry of the key.
  (interchange.data.filter (·.pubkey = pubkey)).flatMap (·.signedAttestations)

/-- Whether a file names a key in one of its entries. -/
def namesKey (interchange : Interchange) (pubkey : BLSPubkey) : Bool :=
  interchange.data.any fun entry => decide (entry.pubkey = pubkey)

/-- The entries of a file that name a key of a list, in order, with the chain of the file. -/
def entriesOf (interchange : Interchange) (keys : List BLSPubkey) : Interchange :=
  { interchange with data := interchange.data.filter (·.pubkey ∈ keys) }

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
  -- Condition 2: the least slot of the blocks of the key.
  (blocks.map (·.slot)).min?

/-- The least source epoch of some signed votes, none without a vote. -/
def minSourceEpoch (attestations : List SignedAttestationRecord) : Option Epoch :=
  -- Condition 4: the least source epoch of the votes of the key.
  (attestations.map (·.sourceEpoch)).min?

/-- The least target epoch of some signed votes, none without a vote. -/
def minTargetEpoch (attestations : List SignedAttestationRecord) : Option Epoch :=
  -- Condition 5: the least target epoch of the votes of the key.
  (attestations.map (·.targetEpoch)).min?

/-- Whether a block is a repeat of a recorded block, as its signing root determines. -/
def isRepeatBlock (blocks : List SignedBlockRecord) (slot : Slot) (signingRoot : Root) : Bool :=
  -- Condition 2: a repeat signing, as the signing root determines.
  --
  -- Some record has the slot and the signing root of the block.
  --
  -- A record without a signing root is the repeat of no block.
  --
  -- A record with the root but another slot is not a repeat, since the root commits to the slot.
  blocks.any fun block => block.slot == slot && block.signingRoot == some signingRoot

/-- Whether a vote is a repeat of a recorded vote, as its signing root determines. -/
def isRepeatAttestation (attestations : List SignedAttestationRecord)
    (sourceEpoch targetEpoch : Epoch) (signingRoot : Root) : Bool :=
  -- Condition 5: a repeat signing, as the signing root determines.
  --
  -- Some record has the two epochs and the signing root of the vote.
  --
  -- A record without a signing root is the repeat of no vote.
  --
  -- A record with the root but other epochs is not a repeat, since the root commits to them.
  attestations.any fun attestation =>
    attestation.sourceEpoch == sourceEpoch && attestation.targetEpoch == targetEpoch &&
      attestation.signingRoot == some signingRoot

/-- Whether a recorded block conflicts with a new block of a slot and a signing root. -/
def SignedBlockRecord.conflictsWith (block : SignedBlockRecord) (slot : Slot)
    (signingRoot : Root) : Bool :=
  -- Condition 1: two blocks of one proposer are slashable when they have one slot and differ.
  --
  -- The key fixes the proposer.
  --
  -- A record holds no block, so its signing root stands for the block.
  --
  -- A record without a signing root conflicts with every new block of its slot, as the EIP asks.
  block.slot == slot && block.signingRoot != some signingRoot

/-- Whether a recorded vote is slashable with a new vote of two epochs and a signing root. -/
def SignedAttestationRecord.isSlashableWith (attestation : SignedAttestationRecord)
    (sourceEpoch targetEpoch : Epoch) (signingRoot : Root) : Bool :=
  -- Condition 3, a double vote: two different votes with one target epoch.
  --
  -- A record holds the epochs of a vote and not its data, so its signing root stands for the data.
  --
  -- A record without a signing root is a different vote from every new vote.
  --
  -- The EIP says so for blocks only.
  --
  -- For votes, its Advice for Complete Databases suggests a null root distinct from every root.
  (attestation.targetEpoch == targetEpoch && attestation.signingRoot != some signingRoot) ||
    -- Condition 3, a surround vote: the new vote surrounds the recorded vote.
    --
    -- Its source is strictly lower, and its target strictly higher.
    (sourceEpoch < attestation.sourceEpoch && attestation.targetEpoch < targetEpoch) ||
    -- Condition 3, a surround vote the other way: the recorded vote surrounds the new vote.
    (attestation.sourceEpoch < sourceEpoch && targetEpoch < attestation.targetEpoch)

/-- The second condition: a block is after the least recorded slot, or is a repeat. -/
def checkBlockSlot (blocks : List SignedBlockRecord) (slot : Slot) (signingRoot : Root) :
    Except SlashingProtectionError Unit :=
  match minBlockSlot blocks with
  -- Condition 2: refuse a slot at most the least recorded slot, except for a repeat signing.
  | some minimum =>
    ensure (minimum < slot ∨ isRepeatBlock blocks slot signingRoot)
      (.blockSlotTooLow slot minimum)
  -- Without a recorded block there is no minimum, and the condition holds.
  | none => .ok ()

/-- Whether a key may sign a block, under the first two conditions, given its block records.

It does not check the slot against the clock or the chain. -/
def checkBlockSigning (blocks : List SignedBlockRecord) (slot : Slot) (signingRoot : Root) :
    Except SlashingProtectionError Unit := do
  -- Condition 1: refuse a block slashable with a recorded block.
  ensure (∀ block ∈ blocks, block.conflictsWith slot signingRoot = false) (.slashableBlock slot)
  -- Condition 2.
  checkBlockSlot blocks slot signingRoot

/-- The fourth condition: a vote has a source epoch at least the least recorded one. -/
def checkSourceEpoch (attestations : List SignedAttestationRecord) (sourceEpoch : Epoch) :
    Except SlashingProtectionError Unit :=
  match minSourceEpoch attestations with
  -- Condition 4: refuse a source epoch below the least recorded source epoch.
  | some minimum => ensure (minimum ≤ sourceEpoch) (.sourceEpochTooLow sourceEpoch minimum)
  -- Without a recorded vote there is no minimum, and the condition holds.
  | none => .ok ()

/-- The fifth condition: a vote has a target epoch after the least recorded one, or is a repeat. -/
def checkTargetEpoch (attestations : List SignedAttestationRecord)
    (sourceEpoch targetEpoch : Epoch) (signingRoot : Root) : Except SlashingProtectionError Unit :=
  match minTargetEpoch attestations with
  -- Condition 5: refuse a target epoch at most the least recorded one, except for a repeat signing.
  | some minimum =>
    ensure (minimum < targetEpoch ∨
        isRepeatAttestation attestations sourceEpoch targetEpoch signingRoot)
      (.targetEpochTooLow targetEpoch minimum)
  -- Without a recorded vote there is no minimum, and the condition holds.
  | none => .ok ()

/-- Whether a key may sign a vote, under the last three conditions, given its vote records.

It does not check that the source epoch is at most the target epoch. -/
def checkAttestationSigning (attestations : List SignedAttestationRecord)
    (sourceEpoch targetEpoch : Epoch) (signingRoot : Root) :
    Except SlashingProtectionError Unit := do
  -- Condition 3: refuse a vote slashable with a recorded vote.
  ensure (∀ attestation ∈ attestations,
      attestation.isSlashableWith sourceEpoch targetEpoch signingRoot = false)
    (.slashableAttestation sourceEpoch targetEpoch)
  -- Condition 4.
  checkSourceEpoch attestations sourceEpoch
  -- Condition 5.
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

end Interchange

/-- A slot limit raised to cover one more block. -/
def raiseSlotLimit (limit : Option Slot) (block : SignedBlockRecord) : Option Slot :=
  -- Advice for Minimal Databases: take the maximum slot block.
  some (limit.elim block.slot fun slot => max slot block.slot)

/-- Epoch limits raised to cover one more vote, the source and the target each on its own. -/
def raiseEpochLimits (limits : Option (Epoch × Epoch)) (attestation : SignedAttestationRecord) :
    Option (Epoch × Epoch) :=
  -- Advice for Minimal Databases: take the maximum source and target attestations.
  --
  -- EthLib takes the two maxima on their own, which is at least as strict as any one vote.
  some (limits.elim (attestation.sourceEpoch, attestation.targetEpoch) fun (source, target) =>
    (max source attestation.sourceEpoch, max target attestation.targetEpoch))

/-- The limits of a key raised to cover the blocks and votes of one more of its entries. -/
def InterchangeEntry.raiseLimits (entry : InterchangeEntry)
    (limits : Option Slot × Option (Epoch × Epoch)) : Option Slot × Option (Epoch × Epoch) :=
  (entry.signedBlocks.foldl raiseSlotLimit limits.1,
    entry.signedAttestations.foldl raiseEpochLimits limits.2)

namespace Interchange

/-- The limits of each key in one pass: its greatest slot, and its greatest source and target.

A key without blocks keeps no slot limit, and a key without votes keeps no epoch limits. -/
def limits (interchange : Interchange) :
    Std.TreeMap BLSPubkey (Option Slot × Option (Epoch × Epoch)) :=
  -- Advice for Minimal Databases: the maximum slot, source and target of each validator.
  --
  -- The source and target maxima can come from different votes.
  interchange.data.foldl (init := ∅) fun limits entry =>
    limits.insert entry.pubkey (entry.raiseLimits (limits.getD entry.pubkey (none, none)))

/-- The minimal strategy: one entry per key in byte order, holding its limits without roots. -/
def toMinimal (interchange : Interchange) : Interchange :=
  -- The limits become the least recorded slot and epochs of each key.
  --
  -- A limit without a signing root conflicts with every new message at its slot or target.
  --
  -- So a new block's slot and a new vote's target must exceed their limits.
  --
  -- A new vote's source must be at least its limit.
  { interchange with
    data := interchange.limits.toList.map fun (pubkey, slot, epochs) =>
      { pubkey
        signedBlocks := slot.toList.map fun slot => ⟨slot, none⟩
        signedAttestations := epochs.toList.map fun (source, target) => ⟨source, target, none⟩ } }

/-- The record after importing a file with the minimal strategy of EIP-3076.

It keeps the greatest slot of each key, and its greatest source and target epochs, each on its own.

It does not compare the genesis validators roots of the two; the checked import below does.

[EIP-3076, Advice for Minimal Databases][minimal] recommends keeping these maxima of each key.

[minimal]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3076.md#advice-for-minimal-databases
-/
def importFile (held file : Interchange) : Interchange :=
  -- Advice for Minimal Databases: the maxima of the file, merged with the record held.
  --
  -- Signing roots are discarded, so repeats of imported messages are refused.
  --
  -- The limits also prevent signing in a gap between imported files.
  --
  -- Advice for Complete Databases warns of that gap, against conditions 2, 4 and 5.
  toMinimal { held with data := held.data ++ file.data }

/-- The record after importing a file of the signer's chain, or an error for another chain.

The chain of the signer is that of its record, by its genesis validators root.

A file with another root is refused, and the record is kept as it was.

Otherwise the import follows the minimal strategy, as above.

The [schema of EIP-3076][schema] says that the root serves to uniquely identify the chain.

[schema]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3076.md#L49
-/
def importChecked (held file : Interchange) : Except SlashingProtectionError Interchange := do
  -- Not in the conditions: the file has the genesis validators root of the signer.
  ensure (file.genesisValidatorsRoot = held.genesisValidatorsRoot)
    (.wrongChain held.genesisValidatorsRoot file.genesisValidatorsRoot)
  -- Then the minimal strategy.
  return held.importFile file

end Interchange

end EthLib.Consensus

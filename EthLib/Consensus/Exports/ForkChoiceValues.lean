module

public import EthLib.Base.Exports.PyDerive
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Consensus.Containers.Misc

/-!
# `Exports.ForkChoiceValues`

The steps of a fork choice case and what they read, as Python values.

Each type has its law: reading back the Python value of a value gives that value.

The export needs the law of its result where it is defined, so the laws stay here.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Base
open EthLib.Exports (PyValue ToPy FromPy LawfulPy PlainPy toPy fromPy)

/-- A signed block in SSZ, with the blobs or the columns that the node holds for it. -/
inductive BlockInput where
  /-- A block alone: the node holds no blob, no proof and no column for it. -/
  | plain (block : ByteArray)
  /-- A block, then the blobs and the proofs that the node holds for it. -/
  | withBlobs (block : ByteArray) (blobs proofs : List ByteArray)
  /-- A block, then the columns that the node samples for it, in SSZ.

  No column means that the node cannot get the columns. -/
  | withColumns (block : ByteArray) (columns : List ByteArray)

/-- The SSZ bytes of the block. -/
def BlockInput.block : BlockInput → ByteArray
  | .plain block | .withBlobs block _ _ | .withColumns block _ => block

/-- A block alone is its bytes, and a block with what the node holds is a tuple. -/
instance : ToPy BlockInput := ⟨fun
  | .plain block => .bytes block
  | .withBlobs block blobs proofs => toPy (block, blobs, proofs)
  | .withColumns block columns => toPy (block, columns)⟩

/-- A tuple of three items holds blobs and proofs, and a tuple of two holds columns. -/
instance : FromPy BlockInput := ⟨fun v => match v with
  | .bytes block => .ok (.plain block)
  | .tuple items =>
    if items.size = 3 then
      (fun (block, blobs, proofs) => .withBlobs block blobs proofs) <$>
        fromPy (α := ByteArray × List ByteArray × List ByteArray) v
    else (fun (block, columns) => .withColumns block columns) <$>
      fromPy (α := ByteArray × List ByteArray) v
  | _ => .error "expected the bytes of a block, or a tuple"⟩

instance : LawfulPy BlockInput where
  fromPy_toPy := by
    intro x
    cases x with
    | plain b => rfl
    | withBlobs b bl pr =>
      have h := LawfulPy.fromPy_toPy (α := ByteArray × List ByteArray × List ByteArray) (b, bl, pr)
      show (fun (block, blobs, proofs) => BlockInput.withBlobs block blobs proofs) <$>
        fromPy (α := ByteArray × List ByteArray × List ByteArray)
          (toPy (b, bl, pr)) = _
      rw [h]
      rfl
    | withColumns b c =>
      have h := LawfulPy.fromPy_toPy (α := ByteArray × List ByteArray) (b, c)
      show (fun (block, columns) => BlockInput.withColumns block columns) <$>
        fromPy (α := ByteArray × List ByteArray) (toPy (b, c)) = _
      rw [h]
      rfl

/-- What a read of the store asks for besides the head, the times and the checkpoints. -/
structure ReadRequest where
  /-- Whether to read where the proposer of the slot builds. -/
  proposerHead : Bool
  /-- Whether to read the viable leaves of the filtered tree, each with its weight. -/
  viable : Bool
  /-- The root of a block whose votes of the payload committee to read. -/
  root : Option Root

/-- A read is a tuple of its three parts. -/
instance : ToPy ReadRequest := ⟨fun r => toPy (r.proposerHead, r.viable, r.root)⟩

/-- A read is a tuple of its three parts, or one bool that asks only for the proposer head. -/
instance : FromPy ReadRequest := ⟨fun
  | .false => .ok ⟨false, false, none⟩
  | .true => .ok ⟨true, false, none⟩
  | v => (fun (proposerHead, viable, root) => ⟨proposerHead, viable, root⟩) <$>
    fromPy (α := Bool × Bool × Option Root) v⟩

instance : LawfulPy ReadRequest where
  fromPy_toPy := by
    rintro ⟨a, b, c⟩
    have h := LawfulPy.fromPy_toPy (α := Bool × Bool × Option Root) (a, b, c)
    show (fun (proposerHead, viable, root) => (⟨proposerHead, viable, root⟩ : ReadRequest)) <$>
      fromPy (α := Bool × Bool × Option Root) (toPy (a, b, c)) = _
    rw [h]
    rfl

/-- The verdict of the execution layer on the payload of the next block. -/
structure PayloadVerdict where
  /-- The status, by its Engine API name. -/
  status : String
  /-- The latest valid hash, if the execution layer knows one. -/
  latestValidHash : Option Hash32

/-- A verdict is a pair of its status and its hash. -/
instance : ToPy PayloadVerdict := ⟨fun v => toPy (v.status, v.latestValidHash)⟩

/-- A verdict is a pair of its status and its hash. -/
instance : FromPy PayloadVerdict := ⟨fun v =>
  (fun (status, latestValidHash) => ⟨status, latestValidHash⟩) <$>
    fromPy (α := String × Option Hash32) v⟩

instance : LawfulPy PayloadVerdict where
  fromPy_toPy := by
    rintro ⟨a, b⟩
    have h := LawfulPy.fromPy_toPy (α := String × Option Hash32) (a, b)
    show (fun (status, latestValidHash) => (⟨status, latestValidHash⟩ : PayloadVerdict)) <$>
      fromPy (α := String × Option Hash32) (toPy (a, b)) = _
    rw [h]
    rfl

/-- A step of a fork choice case. -/
inductive ForkChoiceStep where
  /-- The clock moves to a time in seconds. -/
  | tick (seconds : UInt64)
  /-- A signed block arrives with its votes. -/
  | block (input : BlockInput)
  /-- An attestation arrives, in SSZ. -/
  | attestation (data : ByteArray)
  /-- An attester slashing arrives, in SSZ. -/
  | attesterSlashing (data : ByteArray)
  /-- The store is read. -/
  | checks (read : ReadRequest)
  /-- A block of proof of work becomes known, in SSZ, for the merge check of later blocks. -/
  | powBlock (data : ByteArray)
  /-- The verdict of the execution layer on the payload of the next block. -/
  | payload (verdict : PayloadVerdict)
  /-- The fast confirmation of the slot runs. -/
  | fastConfirmation (nothing : Unit)
  /-- From Gloas, a signed envelope arrives, in SSZ. -/
  | executionPayload (data : ByteArray)
  /-- From Gloas, a vote of a member of the payload committee arrives from the wire, in SSZ. -/
  | payloadAttestationMessage (data : ByteArray)

derive_py ForkChoiceStep
derive_py_laws ForkChoiceStep

/-- The head of a store: its slot, its root and the status of its payload. -/
structure HeadRead where
  /-- The slot of the head block. -/
  slot : UInt64
  /-- The root of the head block. -/
  root : Root
  /-- The status of the payload of the head: 0 empty, 1 full, 2 pending. -/
  payloadStatus : UInt8

derive_py HeadRead
derive_py_laws HeadRead

/-- A checkpoint: an epoch and a root. -/
structure CheckpointRead where
  /-- The epoch of the checkpoint. -/
  epoch : UInt64
  /-- The root of the checkpoint. -/
  root : Root

derive_py CheckpointRead
derive_py_laws CheckpointRead

/-- The checkpoint as it crosses to Python. -/
def CheckpointRead.of (checkpoint : Checkpoint) : CheckpointRead :=
  ⟨checkpoint.epoch, checkpoint.root⟩

/-- A viable leaf of the filtered tree, with its weight. -/
structure LeafRead where
  /-- The root of the leaf. -/
  root : Root
  /-- The weight of the leaf. -/
  weight : UInt64
  /-- The status of the payload of the leaf: 0 empty, 1 full, 2 pending. -/
  payloadStatus : UInt8

derive_py LeafRead
derive_py_laws LeafRead

/-- What a read of the store gives.

A part that the read does not ask for is none. -/
structure StoreRead where
  /-- The head of the store. -/
  head : HeadRead
  /-- The time of the store, in milliseconds. -/
  timeMs : UInt64
  /-- The genesis time of the store, in milliseconds. -/
  genesisTimeMs : UInt64
  /-- The justified checkpoint. -/
  justifiedCheckpoint : CheckpointRead
  /-- The finalized checkpoint. -/
  finalizedCheckpoint : CheckpointRead
  /-- The root that the proposer boost favours. -/
  proposerBoostRoot : Root
  /-- The root on which the proposer of the slot builds. -/
  proposerHead : Option Root
  /-- The viable leaves of the filtered tree, each with its weight. -/
  viableForHeadRootsAndWeights : Option (List LeafRead)
  /-- The votes of the payload committee that the payload was on time. -/
  payloadTimelinessVote : Option (List (Option Bool))
  /-- The votes of the payload committee that the data was available. -/
  payloadDataAvailabilityVote : Option (List (Option Bool))

derive_py StoreRead
derive_py_laws StoreRead

/-- What the fast confirmation of a slot gives. -/
structure FastConfirmationRead where
  /-- The justified checkpoint that the node saw at the start of the previous epoch. -/
  previousEpochObservedJustifiedCheckpoint : CheckpointRead
  /-- The justified checkpoint that the node saw at the start of the current epoch. -/
  currentEpochObservedJustifiedCheckpoint : CheckpointRead
  /-- The greatest unrealized justified checkpoint of the previous epoch. -/
  previousEpochGreatestUnrealizedCheckpoint : CheckpointRead
  /-- The head at the start of the previous slot. -/
  previousSlotHead : Root
  /-- The head at the start of the current slot. -/
  currentSlotHead : Root
  /-- The root of the most recent confirmed block. -/
  confirmedRoot : Root
  /-- From Bellatrix, the hash of the safe execution block. -/
  safeExecutionBlockHash : Option Hash32

derive_py FastConfirmationRead
derive_py_laws FastConfirmationRead

/-- What a step gives to read: a read of the store, or a fast confirmation. -/
inductive StepRead where
  /-- A read of the store. -/
  | store (read : StoreRead)
  /-- A fast confirmation. -/
  | fastConfirmation (read : FastConfirmationRead)

/-- Each read crosses as its own `dict`, with no tag. -/
instance : ToPy StepRead := ⟨fun
  | .store read => toPy read
  | .fastConfirmation read => toPy read⟩

/-- A read of the store is the `dict` with a head. -/
instance : FromPy StepRead := ⟨fun v => do
  if ((← v.entries).toList.lookup "head").isSome then .store <$> fromPy v
  else .fastConfirmation <$> fromPy v⟩

instance : LawfulPy StepRead where
  fromPy_toPy := by
    intro x
    cases x with
    | store r =>
      obtain ⟨es, hes, hl⟩ : ∃ es, toPy r = PyValue.dict es ∧
          (es.toList.lookup "head").isSome = true := ⟨_, rfl, by simp [List.lookup]⟩
      have h := LawfulPy.fromPy_toPy r
      show (do
        if ((← (toPy r : PyValue).entries).toList.lookup "head").isSome then
          StepRead.store <$> fromPy (toPy r)
        else StepRead.fastConfirmation <$> fromPy (toPy r)) = _
      rw [hes] at h ⊢
      simp [PyValue.entries, hl, h, bind, Except.bind, Functor.map,
        Except.map]
    | fastConfirmation r =>
      obtain ⟨es, hes, hl⟩ : ∃ es, toPy r = PyValue.dict es ∧
          (es.toList.lookup "head").isSome = false := ⟨_, rfl, by simp [List.lookup]⟩
      have h := LawfulPy.fromPy_toPy r
      show (do
        if ((← (toPy r : PyValue).entries).toList.lookup "head").isSome then
          StepRead.store <$> fromPy (toPy r)
        else StepRead.fastConfirmation <$> fromPy (toPy r)) = _
      rw [hes] at h ⊢
      simp [PyValue.entries, hl, h, bind, Except.bind, Functor.map,
        Except.map]

instance : PlainPy StepRead where
  isPlain_toPy := by
    intro x
    cases x with
    | store r => exact PlainPy.isPlain_toPy r
    | fastConfirmation r => exact PlainPy.isPlain_toPy r

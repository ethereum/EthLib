module

public import EthLib.Execution.Blocks.BlockAccessList
public import EthLib.Execution.State.Tracker

/-!
# `Blocks.AccessListBuilder`

The builder of the block access list of a block, from Glamsterdam on.

Source: [EIP-7928][eip7928], in three sections:

- "Recording Semantics by Change Type";
- "BlockAccessIndex Assignment";
- "Ordering, Uniqueness and Determinism".

The EIP is in Last Call, so its rules may still change.

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#recording-semantics-by-change-type
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State (Account BlockState EMPTY_ACCOUNT StateError TransactionState)

/-- What a block has recorded so far for one account. -/
structure AccountRecord where
  /-- The new value of each written slot, at each position that changed it. -/
  storageChanges : Std.ExtTreeMap Bytes32 (Std.ExtTreeMap UInt32 U256) := ∅
  /-- The slots that the block read. -/
  storageReads : Std.ExtTreeSet Bytes32 := ∅
  /-- The new balance at each position that changed it. -/
  balanceChanges : Std.ExtTreeMap UInt32 U256 := ∅
  /-- The new nonce at each position that changed it. -/
  nonceChanges : Std.ExtTreeMap UInt32 Nat := ∅
  /-- The new code at each position that changed it. -/
  codeChanges : Std.ExtTreeMap UInt32 ByteArray := ∅

/-- The builder of a block access list, while the body of the block runs. -/
structure AccessListBuilder where
  /-- The current position in the body of the block.

  Position 0 holds the system calls before the transactions.

  Position `i + 1` holds the transaction `i`.

  After the `n` transactions, position `n + 1` holds the withdrawals and the system calls. -/
  index : UInt32
  /-- The block state when the current position began. -/
  start : BlockState
  /-- What the block has recorded for each account. -/
  accounts : Std.ExtTreeMap Address AccountRecord

namespace AccessListBuilder

/-- The builder of a block whose body starts from the block state `block`, at position 0. -/
def init (block : BlockState) : AccessListBuilder := ⟨0, block, ∅⟩

/-- Begin the position `index`, from the block state `block` that holds before it. -/
def beginIndex (b : AccessListBuilder) (index : UInt32) (block : BlockState) :
    AccessListBuilder :=
  -- EIP-7928 compares each write with the value just before the current index.
  --
  -- So the position keeps the state before it.
  { b with index, start := block }

/-- The account at an address when the current position began, or the empty account. -/
def startAccount (b : AccessListBuilder) (address : Address) : Account :=
  (TransactionState.ofBlock b.start).getAccount address

/-- The word at a key of the storage of an address when the current position began. -/
def startStorage (b : AccessListBuilder) (address : Address) (key : Bytes32) : U256 :=
  (TransactionState.ofBlock b.start).getStorage address key

/-- Change the record of an account, which joins the list if it is not there yet. -/
def record (b : AccessListBuilder) (address : Address) (f : AccountRecord → AccountRecord) :
    AccessListBuilder :=
  { b with accounts := b.accounts.insert address (f (b.accounts.getD address {})) }

/-- Change the record of an account that the list holds, and leave out any other account. -/
def amend (b : AccessListBuilder) (address : Address) (f : AccountRecord → AccountRecord) :
    AccessListBuilder :=
  { b with accounts := b.accounts.modify address f }

/-- Record the new value of a field at the current position when it changed.

When it did not change, drop any value that the position recorded earlier.

Only a change brings the account into the list. -/
def setField {α : Type} (b : AccessListBuilder) (address : Address) (changed : Bool) (value : α)
    (field : AccountRecord → Std.ExtTreeMap UInt32 α)
    (update : AccountRecord → Std.ExtTreeMap UInt32 α → AccountRecord) : AccessListBuilder :=
  if changed then b.record address fun r => update r ((field r).insert b.index value)
  else b.amend address fun r => update r ((field r).erase b.index)

/-- Drop the value of a slot at a position, and the slot once it has no value left. -/
def dropSlotChange (changes : Std.ExtTreeMap Bytes32 (Std.ExtTreeMap UInt32 U256))
    (key : Bytes32) (index : UInt32) : Std.ExtTreeMap Bytes32 (Std.ExtTreeMap UInt32 U256) :=
  match changes[key]? with
  | none => changes
  | some values =>
    let values := values.erase index
    if values.isEmpty then changes.erase key else changes.insert key values

/-- Record a write of `value` at a key of the storage of an address. -/
def recordStorageWrite (b : AccessListBuilder) (address : Address) (key : Bytes32)
    (value : U256) : AccessListBuilder :=
  -- A write is any change of value: the value after differs from the value before.
  --
  -- The pre-value is the value of the slot at the start of the position.
  if b.startStorage address key ≠ value then
    b.record address fun r =>
      { r with
        storageChanges := r.storageChanges.insert key
          ((r.storageChanges.getD key ∅).insert b.index value) }
  -- A slot written with an unchanged value is a read.
  --
  -- A change that an earlier call recorded at this position is dropped, since the two cancel.
  --
  -- A write without a change must not remove the storage changes of earlier indices.
  else
    b.record address fun r =>
      { r with
        storageChanges := dropSlotChange r.storageChanges key b.index
        storageReads := r.storageReads.insert key }

/-- Record the account `written` that a transaction left at an address.

None stands for a deleted account, which has the fields of the empty account.

The new code comes from the transaction `tx`. -/
def recordAccountWrite (b : AccessListBuilder) (tx : TransactionState) (address : Address)
    (written : Option Account) : Except StateError AccessListBuilder := do
  -- Each written account was accessed, so it joins the list even when none of its fields changed.
  --
  -- An address with no change of state must still be present, with empty lists of changes.
  let b := b.record address id
  let before := b.startAccount address
  let after := written.getD EMPTY_ACCOUNT
  -- A balance equal to the balance before the transaction is not recorded as a change.
  let b := b.setField address (before.balance ≠ after.balance) after.balance
    (·.balanceChanges) fun r m => { r with balanceChanges := m }
  -- Record the nonce after the transaction, when the nonce changed.
  let b := b.setField address (before.nonce ≠ after.nonce) after.nonce
    (·.nonceChanges) fun r m => { r with nonceChanges := m }
  -- Record the runtime code after the transaction, for each deployed or modified contract.
  --
  -- The same rule records the delegation indicator of each successful delegation.
  let codeChanged := before.codeHash ≠ after.codeHash
  let code ← if codeChanged then tx.getCode after.codeHash else pure .empty
  return b.setField address codeChanged code (·.codeChanges) fun r m => { r with codeChanges := m }

/-- Record what a transaction or a system call `tx` did, at the current position.

The call has ended, and its writes have not yet joined the block. -/
def recordTransaction (b : AccessListBuilder) (tx : TransactionState) :
    Except StateError AccessListBuilder := do
  -- Each account the call accessed joins the list, with empty changes if nothing else.
  let b := tx.accountReads.foldl (fun b address => b.record address id) b
  -- A slot that `SLOAD` accessed and that is not written is a read.
  --
  -- A key that is also written with a change leaves the reads when the list is built.
  let b := tx.storageReads.foldl
    (fun b address keys => b.record address fun r =>
      { r with storageReads := r.storageReads.insertMany keys.toList })
    b
  -- Each written account, compared with the state at the start of the position.
  let b ← tx.accountWrites.foldlM (fun b address written => b.recordAccountWrite tx address written)
    b
  -- Each written slot, compared with the state at the start of the position.
  return tx.storageWrites.foldl
    (fun b address slots =>
      slots.foldl (fun b key value => b.recordStorageWrite address key value) b)
    b

end AccessListBuilder

/-- The entry of an account in the list, from its record.

A read key that is also written is left out of the reads.

EIP-2681 bounds a nonce by 2^64 - 1, so it fits its field.

A block that passes its transition keeps that bound when the state before it meets it. -/
def AccountRecord.toChanges (address : Address) (r : AccountRecord) : AccountChanges :=
  -- The changes of each slot hold at least one change.
  let slots := (r.storageChanges.toList.filter fun (_, values) => !values.isEmpty).map
    fun (key, values) =>
      ({ slot := U256.fromBeBytes key
         changes := values.toList.map fun (index, value) => ⟨index, value⟩ } : SlotChanges)
  -- A storage key never appears both among the storage changes and among the storage reads.
  let reads := (r.storageReads.toList.filter fun key => (r.storageChanges.getD key ∅).isEmpty).map
    U256.fromBeBytes
  { address
    -- The storage changes, by ascending storage key.
    storageChanges := slots.mergeSort fun s t => s.slot.toNat ≤ t.slot.toNat
    -- The storage reads, by ascending storage key.
    storageReads := reads.mergeSort fun s t => s.toNat ≤ t.toNat
    -- The other changes, by ascending block access index, the order of the keys of a tree map.
    balanceChanges := r.balanceChanges.toList.map fun (index, balance) => ⟨index, balance⟩
    -- From a state that meets EIP-2681, no nonce wraps in this conversion to 64 bits.
    nonceChanges := r.nonceChanges.toList.map fun (index, nonce) => ⟨index, UInt64.ofNat nonce⟩
    codeChanges := r.codeChanges.toList.map fun (index, code) => ⟨index, code⟩ }

/-- The block access list of the builder, with its accounts sorted by address. -/
def AccessListBuilder.build (b : AccessListBuilder) : BlockAccessList :=
  -- The accounts, in lexicographic order of address.
  (b.accounts.toList.map fun (address, r) => r.toChanges address).mergeSort
    fun x y => BlockAccessList.addressKey x.address ≤ BlockAccessList.addressKey y.address

end EthLib.Execution.Blocks

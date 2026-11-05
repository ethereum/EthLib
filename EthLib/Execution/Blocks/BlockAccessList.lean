module

public import EthLib.Base.Address
public import EthLib.Base.Except
public import EthLib.Base.Hash32
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Serialization.Rlp.Codec

/-!
# `Blocks.BlockAccessList`

The block access list of a block, from Glamsterdam on.

It names every account that the block touches, and each change that the block makes to its state.

[EIP-7928](https://eips.ethereum.org/EIPS/eip-7928#rlp-data-structures) defines it.

The EIP is in Last Call, so its rules may still change.

The list is not part of the block body.

The header holds the Keccak-256 hash of its RLP form instead.

A change records the position in the block at which the value holds:

- 0 before the transactions;
- `i + 1` after the transaction `i`;
- `n + 1` after the last of `n` transactions.

Each number in the RLP form is a scalar with no leading zero byte, as in a header.

The checks here read the list alone: its order, its uniqueness and its size.

Whether the list matches the execution of the block is a rule of the block.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp

/-- The new value of a storage slot at a position in the block. -/
structure StorageChange where
  /-- The position in the block. -/
  index : UInt32
  /-- The value of the slot after that position. -/
  value : U256
  deriving DecidableEq, Repr

/-- The balance of an account after a position in the block. -/
structure BalanceChange where
  /-- The position in the block. -/
  index : UInt32
  /-- The balance after that position, in wei. -/
  balance : U256
  deriving DecidableEq, Repr

/-- The nonce of an account after a position in the block. -/
structure NonceChange where
  /-- The position in the block. -/
  index : UInt32
  /-- The nonce after that position. -/
  nonce : UInt64
  deriving DecidableEq, Repr

/-- The code of an account after a position in the block. -/
structure CodeChange where
  /-- The position in the block. -/
  index : UInt32
  /-- The code after that position. -/
  code : ByteArray
  deriving DecidableEq

/-- The changes of one storage slot of an account. -/
structure SlotChanges where
  /-- The key of the slot. -/
  slot : U256
  /-- Its new values, by position in the block. -/
  changes : List StorageChange
  deriving DecidableEq, Repr

/-- An account that the block touches, and its changes, field by field. -/
structure AccountChanges where
  /-- The address of the account. -/
  address : Address
  /-- The slots that the block writes, with their new values. -/
  storageChanges : List SlotChanges
  /-- The keys of the slots that the block reads and does not change. -/
  storageReads : List U256
  /-- The new balances. -/
  balanceChanges : List BalanceChange
  /-- The new nonces. -/
  nonceChanges : List NonceChange
  /-- The new code. -/
  codeChanges : List CodeChange
  deriving DecidableEq

/-- The block access list: one entry for each account that the block touches. -/
abbrev BlockAccessList := List AccountChanges

/-! ## The RLP form

Each change is the list of its position and its value, and an account is the list of its six fields.
-/

namespace StorageChange

/-- The item `[index, value]`. -/
def toItem (c : StorageChange) : Item := .list [Codec.toItem c.index, Codec.toItem c.value]

/-- The change that an item `[index, value]` holds. -/
def ofItem (item : Item) : Except RlpError StorageChange := do
  let items ← item.fields 2
  let (index, items) ← Item.readField (α := UInt32) 2 items
  let (value, _) ← Item.readField (α := U256) 2 items
  return ⟨index, value⟩

end StorageChange

instance : Codec StorageChange := ⟨StorageChange.toItem, StorageChange.ofItem⟩

namespace BalanceChange

/-- The item `[index, balance]`. -/
def toItem (c : BalanceChange) : Item := .list [Codec.toItem c.index, Codec.toItem c.balance]

/-- The change that an item `[index, balance]` holds. -/
def ofItem (item : Item) : Except RlpError BalanceChange := do
  let items ← item.fields 2
  let (index, items) ← Item.readField (α := UInt32) 2 items
  let (balance, _) ← Item.readField (α := U256) 2 items
  return ⟨index, balance⟩

end BalanceChange

instance : Codec BalanceChange := ⟨BalanceChange.toItem, BalanceChange.ofItem⟩

namespace NonceChange

/-- The item `[index, nonce]`. -/
def toItem (c : NonceChange) : Item := .list [Codec.toItem c.index, Codec.toItem c.nonce]

/-- The change that an item `[index, nonce]` holds. -/
def ofItem (item : Item) : Except RlpError NonceChange := do
  let items ← item.fields 2
  let (index, items) ← Item.readField (α := UInt32) 2 items
  let (nonce, _) ← Item.readField (α := UInt64) 2 items
  return ⟨index, nonce⟩

end NonceChange

instance : Codec NonceChange := ⟨NonceChange.toItem, NonceChange.ofItem⟩

namespace CodeChange

/-- The item `[index, code]`. -/
def toItem (c : CodeChange) : Item := .list [Codec.toItem c.index, Codec.toItem c.code]

/-- The change that an item `[index, code]` holds. -/
def ofItem (item : Item) : Except RlpError CodeChange := do
  let items ← item.fields 2
  let (index, items) ← Item.readField (α := UInt32) 2 items
  let (code, _) ← Item.readField (α := ByteArray) 2 items
  return ⟨index, code⟩

end CodeChange

instance : Codec CodeChange := ⟨CodeChange.toItem, CodeChange.ofItem⟩

namespace SlotChanges

/-- The item `[slot, changes]`. -/
def toItem (s : SlotChanges) : Item := .list [Codec.toItem s.slot, Codec.toItem s.changes]

/-- The slot changes that an item `[slot, changes]` holds. -/
def ofItem (item : Item) : Except RlpError SlotChanges := do
  let items ← item.fields 2
  let (slot, items) ← Item.readField (α := U256) 2 items
  let (changes, _) ← Item.readField (α := List StorageChange) 2 items
  return ⟨slot, changes⟩

end SlotChanges

instance : Codec SlotChanges := ⟨SlotChanges.toItem, SlotChanges.ofItem⟩

namespace AccountChanges

/-- The item of an account: its address, then its five lists of changes, in order. -/
def toItem (a : AccountChanges) : Item :=
  .list [Codec.toItem a.address, Codec.toItem a.storageChanges, Codec.toItem a.storageReads,
    Codec.toItem a.balanceChanges, Codec.toItem a.nonceChanges, Codec.toItem a.codeChanges]

/-- The account that an item of six fields holds. -/
def ofItem (item : Item) : Except RlpError AccountChanges := do
  let items ← item.fields 6
  let (address, items) ← Item.readField (α := Address) 6 items
  let (storageChanges, items) ← Item.readField (α := List SlotChanges) 6 items
  let (storageReads, items) ← Item.readField (α := List U256) 6 items
  let (balanceChanges, items) ← Item.readField (α := List BalanceChange) 6 items
  let (nonceChanges, items) ← Item.readField (α := List NonceChange) 6 items
  let (codeChanges, _) ← Item.readField (α := List CodeChange) 6 items
  return ⟨address, storageChanges, storageReads, balanceChanges, nonceChanges, codeChanges⟩

end AccountChanges

instance : Codec AccountChanges := ⟨AccountChanges.toItem, AccountChanges.ofItem⟩

namespace BlockAccessList

open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The hash of a block access list: the Keccak-256 hash of its RLP form.

The header holds it from Glamsterdam on.

The empty list has the RLP form `0xc0`.

It fails only when a field has `2^64` bytes or more, since RLP cannot encode it. -/
def hash (bal : BlockAccessList) : Except RlpError Hash32 := do
  return keccak256 (← Codec.encode bal)

/-! ## The checks of the list alone -/

/-- Whether each number of a list is below the next one. -/
def ascending : List Nat → Bool
  | a :: b :: rest => a < b && ascending (b :: rest)
  | _ => true

/-- An address as a number, so that numbers order addresses as their bytes do. -/
def addressKey (address : Address) : Nat := bytesToNat address.toList

/-- The gas that each item of the list stands for.

The items are the accounts, and the distinct storage keys of each account.

A block may have at most its gas limit divided by this cost as items. -/
def ITEM_COST : Nat := 2000

/-- Why a block access list breaks a rule of its form. -/
inductive Error where
  /-- An account does not come after the one before it, by address. -/
  | accountsNotAscending (address : Address)
  /-- A written slot of an account does not come after the one before it, by key. -/
  | slotsNotAscending (address : Address)
  /-- A written slot of an account has no change. -/
  | slotWithoutChange (address : Address) (slot : U256)
  /-- The changes of a slot are not in strictly ascending order of position. -/
  | storageChangesNotAscending (address : Address) (slot : U256)
  /-- The read keys of an account are not in strictly ascending order. -/
  | readsNotAscending (address : Address)
  /-- A key of an account is both read and written. -/
  | readAndWritten (address : Address) (slot : U256)
  /-- The balance changes of an account are not in strictly ascending order of position. -/
  | balanceChangesNotAscending (address : Address)
  /-- The nonce changes of an account are not in strictly ascending order of position. -/
  | nonceChangesNotAscending (address : Address)
  /-- The code changes of an account are not in strictly ascending order of position. -/
  | codeChangesNotAscending (address : Address)
  /-- The list has more items than the gas limit allows. -/
  | tooManyItems (items limit : Nat)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 401, above the codes of the other errors of a block.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Error.code : Error → UInt32
  | .accountsNotAscending _ => 401
  | .slotsNotAscending _ => 402
  | .slotWithoutChange .. => 403
  | .storageChangesNotAscending .. => 404
  | .readsNotAscending _ => 405
  | .readAndWritten .. => 406
  | .balanceChangesNotAscending _ => 407
  | .nonceChangesNotAscending _ => 408
  | .codeChangesNotAscending _ => 409
  | .tooManyItems .. => 410

/-- Check the order of the changes of one account.

Each list is in strictly ascending order, so no slot, key or position appears twice.

Each written slot has a change, and no key is both read and written. -/
def checkAccount (a : AccountChanges) : Except Error Unit := do
  let address := a.address
  let slots := a.storageChanges.map (·.slot.toNat)
  ensure (ascending slots) (.slotsNotAscending address)
  a.storageChanges.forM fun s => do
    ensure (!s.changes.isEmpty) (.slotWithoutChange address s.slot)
    ensure (ascending (s.changes.map (·.index.toNat))) (.storageChangesNotAscending address s.slot)
  ensure (ascending (a.storageReads.map (·.toNat))) (.readsNotAscending address)
  a.storageReads.forM fun r => ensure (!slots.contains r.toNat) (.readAndWritten address r)
  ensure (ascending (a.balanceChanges.map (·.index.toNat))) (.balanceChangesNotAscending address)
  ensure (ascending (a.nonceChanges.map (·.index.toNat))) (.nonceChangesNotAscending address)
  ensure (ascending (a.codeChanges.map (·.index.toNat))) (.codeChangesNotAscending address)

/-- Check that each account comes after the one before it, by address.

The error names the first account that does not. -/
def checkAddresses : List AccountChanges → Except Error Unit
  | a :: b :: rest =>
    if addressKey a.address < addressKey b.address then checkAddresses (b :: rest)
    else .error (.accountsNotAscending b.address)
  | _ => pure ()

/-- The items of a list: its accounts, and the written and read keys of each.

Once the checks of each account pass, no key of an account appears twice.

So this counts the accounts and the distinct storage keys of each account, as EIP-7928 does. -/
def itemCount (bal : BlockAccessList) : Nat :=
  (bal.map fun a => 1 + a.storageChanges.length + a.storageReads.length).sum

/-- Check a block access list alone, in a block with the gas limit `gasLimit`.

The order and uniqueness rules are in [EIP-7928][order].

Accounts come in strictly ascending order of address, so each appears once.

The [size rule][size] allows at most `gasLimit / 2000` items.

[order]: https://eips.ethereum.org/EIPS/eip-7928#ordering-uniqueness-and-determinism
[size]: https://eips.ethereum.org/EIPS/eip-7928#block-access-list-size-constraint -/
def check (bal : BlockAccessList) (gasLimit : Nat) : Except Error Unit := do
  bal.forM checkAccount
  checkAddresses bal
  let limit := gasLimit / ITEM_COST
  ensure (itemCount bal ≤ limit) (.tooManyItems (itemCount bal) limit)

end BlockAccessList

end EthLib.Execution.Blocks

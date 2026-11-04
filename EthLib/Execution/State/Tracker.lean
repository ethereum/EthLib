module

public import EthLib.Base.Fork
public import EthLib.Execution.State.Root
public import Std.Data.ExtTreeSet

/-!
# `State.Tracker`

The changes that a block and a transaction make to the state, kept apart from the state.

A block reads the state before the block, then the writes of the block so far.

A transaction reads its own writes first, then those of its block.

When the transaction ends, its writes move into its block.

A snapshot of the writes of a transaction restores them when a call fails.

Transient storage lives for one transaction, as [EIP-1153][eip1153] specifies.

From Paris, a change that leaves an account empty deletes it.

[EIP-7523][eip7523] forbids an empty account after the Merge.

From Spurious Dragon to Paris, an empty account stays until the end of its transaction.

Then [EIP-161][eip161] deletes it if the transaction touched it.

Before Spurious Dragon, an empty account stays.

[eip1153]: https://eips.ethereum.org/EIPS/eip-1153#specification
[eip7523]: https://eips.ethereum.org/EIPS/eip-7523#specification
[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base

/-- Storage of many accounts: a map from each address to its keys and words. -/
abbrev StorageMap := Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)

/-- The word that a storage map holds at an address and a key, if it holds one. -/
def StorageMap.slot (storage : StorageMap) (address : Address) (key : Bytes32) : Option U256 :=
  storage[address]?.bind fun slots => slots[key]?

/-- Why a change to the state fails. -/
inductive StateError where
  /-- A storage write to an address with no account. -/
  | noAccount (address : Address)
  /-- A code hash whose code the state does not hold. -/
  | missingCode (codeHash : Hash32)
  /-- A balance smaller than the amount that leaves it. -/
  | insufficientBalance (address : Address)
  /-- A balance that would reach 2^256. -/
  | balanceOverflow (address : Address)
  deriving DecidableEq, Repr

/-! ## The state before a block -/

/-- The account at an address, or none if the address has no account. -/
def State.getAccountOptional (state : State) (address : Address) : Option Account :=
  state.accounts[address]?

/-- The word at a key of the storage of an address, or zero if none is set. -/
def State.getStorage (state : State) (address : Address) (key : Bytes32) : U256 :=
  (StorageMap.slot state.storage address key).getD 0

/-- The code with a code hash.

The empty code needs no entry, and any other missing code is an error. -/
def State.getCode (state : State) (codeHash : Hash32) : Except StateError ByteArray :=
  if codeHash = EMPTY_CODE_HASH then
    .ok .empty
  else
    match state.code[codeHash]? with
    | some code => .ok code
    | none => .error (.missingCode codeHash)

/-! ## The block and the transaction -/

/-- The writes of a block so far, on top of the state before the block. -/
structure BlockState where
  /-- The state before the block. -/
  preState : State
  /-- The account written at each address, or none for a deleted account. -/
  accountWrites : Std.ExtTreeMap Address (Option Account)
  /-- The words written in the storage of each address. -/
  storageWrites : StorageMap
  /-- The code written with each code hash. -/
  codeWrites : Std.ExtTreeMap Hash32 ByteArray
  /-- The addresses whose earlier storage the block wiped. -/
  storageClears : Std.ExtTreeSet Address

/-- The writes of one transaction, on top of the writes of its block. -/
structure TransactionState where
  /-- The block of the transaction. -/
  parent : BlockState
  /-- The account written at each address, or none for a deleted account. -/
  accountWrites : Std.ExtTreeMap Address (Option Account)
  /-- The words written in the storage of each address. -/
  storageWrites : StorageMap
  /-- The code written with each code hash. -/
  codeWrites : Std.ExtTreeMap Hash32 ByteArray
  /-- The addresses of the accounts that the transaction created.

  A rollback keeps them. -/
  createdAccounts : Std.ExtTreeSet Address
  /-- The addresses whose earlier storage the transaction wiped. -/
  storageClears : Std.ExtTreeSet Address
  /-- The transient storage of each address. -/
  transientStorage : StorageMap

/-- A transaction with no write yet, in a block. -/
def TransactionState.ofBlock (block : BlockState) : TransactionState :=
  ⟨block, ∅, ∅, ∅, ∅, ∅, ∅⟩

namespace TransactionState

/-! ## Reads -/

/-- The account at an address, or none if the address has no account.

The transaction's writes come first, then the block's, then the state before the block. -/
def getAccountOptional (tx : TransactionState) (address : Address) : Option Account :=
  match tx.accountWrites[address]? with
  | some account => account
  | none =>
    match tx.parent.accountWrites[address]? with
    | some account => account
    | none => tx.parent.preState.getAccountOptional address

/-- The account at an address, or the empty account if the address has no account. -/
def getAccount (tx : TransactionState) (address : Address) : Account :=
  (tx.getAccountOptional address).getD EMPTY_ACCOUNT

/-- The code with a code hash, from the writes first. -/
def getCode (tx : TransactionState) (codeHash : Hash32) : Except StateError ByteArray :=
  if codeHash = EMPTY_CODE_HASH then
    .ok .empty
  else
    match tx.codeWrites[codeHash]? with
    | some code => .ok code
    | none =>
      match tx.parent.codeWrites[codeHash]? with
      | some code => .ok code
      | none => tx.parent.preState.getCode codeHash

/-- The word at a key of the storage of an address, or zero if none is set.

A wipe of the storage hides every earlier word. -/
def getStorage (tx : TransactionState) (address : Address) (key : Bytes32) : U256 :=
  match tx.storageWrites.slot address key with
  | some value => value
  | none =>
    if address ∈ tx.storageClears then 0 else
    match tx.parent.storageWrites.slot address key with
    | some value => value
    | none =>
      if address ∈ tx.parent.storageClears then 0 else tx.parent.preState.getStorage address key

/-- The word at a key before the transaction began.

It is zero for an account that the transaction created.

[EIP-2200](https://eips.ethereum.org/EIPS/eip-2200#specification) prices a storage write by it. -/
def getStorageOriginal (tx : TransactionState) (address : Address) (key : Bytes32) : U256 :=
  if address ∈ tx.createdAccounts then 0 else
  match tx.parent.storageWrites.slot address key with
  | some value => value
  | none =>
    if address ∈ tx.parent.storageClears then 0 else tx.parent.preState.getStorage address key

/-- The word at a key of the transient storage of an address, or zero if none is set. -/
def getTransientStorage (tx : TransactionState) (address : Address) (key : Bytes32) : U256 :=
  (tx.transientStorage.slot address key).getD 0

/-- Whether the address has an account. -/
def accountExists (tx : TransactionState) (address : Address) : Bool :=
  (tx.getAccountOptional address).isSome

/-- Whether a contract may be deployed at the address: its account has nonce 0 and no code. -/
def accountDeployable (tx : TransactionState) (address : Address) : Bool :=
  let account := tx.getAccount address
  account.nonce = 0 && account.codeHash = EMPTY_CODE_HASH

/-- Whether the address has an account with nonce 0, no code and balance 0. -/
def accountExistsAndIsEmpty (tx : TransactionState) (address : Address) : Bool :=
  match tx.getAccountOptional address with
  | some account => account.nonce = 0 && account.codeHash = EMPTY_CODE_HASH && account.balance = 0
  | none => false

/-- Whether the address has an account that is not the empty account. -/
def isAccountAlive (tx : TransactionState) (address : Address) : Bool :=
  match tx.getAccountOptional address with
  | some account => account != EMPTY_ACCOUNT
  | none => false

/-! ## Writes -/

/-- Set the account at an address, or delete it with none.

Deleting an account keeps its storage. -/
def setAccount (tx : TransactionState) (address : Address) (account : Option Account) :
    TransactionState :=
  { tx with accountWrites := tx.accountWrites.insert address account }

/-- Set the word at a key of the storage of an address.

The address must have an account. -/
def setStorage (tx : TransactionState) (address : Address) (key : Bytes32) (value : U256) :
    Except StateError TransactionState :=
  if (tx.getAccountOptional address).isNone then
    .error (.noAccount address)
  else
    .ok { tx with
      storageWrites := tx.storageWrites.insert address
        ((tx.storageWrites.getD address ∅).insert key value) }

/-- Wipe the storage of an address: drop its writes, and hide every earlier word. -/
def destroyStorage (tx : TransactionState) (address : Address) : TransactionState :=
  { tx with
    storageWrites := tx.storageWrites.erase address
    storageClears := tx.storageClears.insert address }

/-- Delete the account at an address, with its storage. -/
def destroyAccount (tx : TransactionState) (address : Address) : TransactionState :=
  (tx.destroyStorage address).setAccount address none

/-- Record that the transaction created the account at an address. -/
def markAccountCreated (tx : TransactionState) (address : Address) : TransactionState :=
  { tx with createdAccounts := tx.createdAccounts.insert address }

/-- Set the word at a key of the transient storage of an address.

The word zero removes the key. -/
def setTransientStorage (tx : TransactionState) (address : Address) (key : Bytes32)
    (value : U256) : TransactionState :=
  let slots := tx.transientStorage.getD address ∅
  { tx with
    transientStorage := tx.transientStorage.insert address
      (if value = 0 then slots.erase key else slots.insert key value) }

/-- Change the account at an address by `f`, which may fail.

An address with no account starts from the empty account.

From Paris, a change that leaves the account empty deletes it. -/
def modifyState (fork : Fork) (tx : TransactionState) (address : Address)
    (f : Account → Except StateError Account) : Except StateError TransactionState := do
  let tx := tx.setAccount address (some (← f (tx.getAccount address)))
  if fork ≥ .paris && tx.accountExistsAndIsEmpty address then
    return tx.destroyAccount address
  else
    return tx

/-- Move `amount` wei from the sender to the recipient.

The sender must hold the amount, and the recipient's balance must stay below 2^256. -/
def moveEther (fork : Fork) (tx : TransactionState) (sender recipient : Address) (amount : U256) :
    Except StateError TransactionState := do
  let tx ← tx.modifyState fork sender fun account =>
    if account.balance < amount then
      .error (.insufficientBalance sender)
    else
      .ok { account with balance := account.balance - amount }
  tx.modifyState fork recipient fun account =>
    if account.balance.toNat + amount.toNat < 2 ^ 256 then
      .ok { account with balance := account.balance + amount }
    else
      .error (.balanceOverflow recipient)

/-- Add newly created ether to the balance of an address, which must stay below 2^256. -/
def createEther (fork : Fork) (tx : TransactionState) (address : Address) (amount : U256) :
    Except StateError TransactionState :=
  tx.modifyState fork address fun account =>
    if account.balance.toNat + amount.toNat < 2 ^ 256 then
      .ok { account with balance := account.balance + amount }
    else
      .error (.balanceOverflow address)

/-- Set the balance of an address. -/
def setAccountBalance (fork : Fork) (tx : TransactionState) (address : Address) (amount : U256) :
    Except StateError TransactionState :=
  tx.modifyState fork address fun account => .ok { account with balance := amount }

/-- Add one to the nonce of an address. -/
def incrementNonce (fork : Fork) (tx : TransactionState) (address : Address) :
    Except StateError TransactionState :=
  tx.modifyState fork address fun account => .ok { account with nonce := account.nonce + 1 }

/-- Set the code of an address, and keep the code under its Keccak-256 hash. -/
def setCode (fork : Fork) (tx : TransactionState) (address : Address) (code : ByteArray) :
    Except StateError TransactionState :=
  let codeHash : Hash32 := Cryptography.Hash.Keccak.keccak256 code
  let tx := if codeHash = EMPTY_CODE_HASH then tx else
    { tx with codeWrites := tx.codeWrites.insert codeHash code }
  tx.modifyState fork address fun account => .ok { account with codeHash := codeHash }

/-- Give an address with no account the empty account.

Before Paris, a transaction touches accounts in this way. -/
def touchAccount (tx : TransactionState) (address : Address) : TransactionState :=
  if tx.accountExists address then tx else tx.setAccount address (some EMPTY_ACCOUNT)

/-- Delete each touched account that is empty, as EIP-161 asks from Spurious Dragon.

Before Spurious Dragon, nothing is deleted. -/
def destroyTouchedEmptyAccounts (fork : Fork) (tx : TransactionState) (touched : List Address) :
    TransactionState :=
  if fork < .spuriousDragon then tx else
  touched.foldl
    (fun tx address => if tx.accountExistsAndIsEmpty address then tx.destroyAccount address else tx)
    tx

/-! ## Rollback and the end of a transaction -/

/-- Restore the writes of a snapshot after a failed call.

The accounts that the transaction created stay recorded. -/
def restoreTxState (tx snapshot : TransactionState) : TransactionState :=
  { snapshot with parent := tx.parent, createdAccounts := tx.createdAccounts }

/-- The words of `slots` written over those of `base`. -/
def writeSlots (base slots : Std.ExtTreeMap Bytes32 U256) : Std.ExtTreeMap Bytes32 U256 :=
  slots.foldl (fun acc key value => acc.insert key value) base

/-- Move the writes of a transaction into its block, and start the next transaction.

A wipe of the transaction drops the block's writes to that storage first.

The next transaction has no write, so its transient storage is empty. -/
def incorporateTxIntoBlock (tx : TransactionState) : TransactionState :=
  let block := tx.parent
  let storageWrites := tx.storageClears.foldl (fun acc address => acc.erase address)
    block.storageWrites
  ofBlock {
    preState := block.preState
    accountWrites := tx.accountWrites.foldl (fun acc address account => acc.insert address account)
      block.accountWrites
    storageWrites := tx.storageWrites.foldl
      (fun acc address slots => acc.insert address (writeSlots (acc.getD address ∅) slots))
      storageWrites
    codeWrites := tx.codeWrites.foldl (fun acc codeHash code => acc.insert codeHash code)
      block.codeWrites
    storageClears := tx.storageClears.foldl (fun acc address => acc.insert address)
      block.storageClears }

end TransactionState

end EthLib.Execution.State

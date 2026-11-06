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

A contract deploys only at an address with no nonce, no code and no word in its storage.

[EIP-7610][eip7610] adds the storage to the conditions of EIP-684.

Transient storage lives for one transaction, as [EIP-1153][eip1153] specifies.

From Paris, a change that leaves an account empty deletes it.

[EIP-7523][eip7523] forbids an empty account after the Merge.

From Spurious Dragon to Paris, an empty account stays until the end of its transaction.

Then [EIP-161][eip161] deletes it if the transaction touched it.

Before Spurious Dragon, an empty account stays.

A transaction also records the accounts and the storage keys it reads.

From Glamsterdam, the block access list of [EIP-7928][eip7928] holds them.

It holds them even when the call that read them reverts, so a rollback keeps them.

From Glamsterdam, [EIP-8246][eip8246] clears an account that SELFDESTRUCT marked.

That clear keeps the balance.

[eip1153]: https://eips.ethereum.org/EIPS/eip-1153#specification
[eip7523]: https://eips.ethereum.org/EIPS/eip-7523#specification
[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
[eip7610]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7610.md#specification
[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
[eip8246]: https://eips.ethereum.org/EIPS/eip-8246#specification
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

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 101, above every code of an error of a state given as bytes.

A new constructor takes a new code, so that each code keeps its meaning. -/
def StateError.code : StateError → UInt32
  | .noAccount _ => 101
  | .missingCode _ => 102
  | .insufficientBalance _ => 103
  | .balanceOverflow _ => 104

/-! ## The balance steps of a move of ether -/

/-- Take `amount` wei from the account at an address, which must hold it. -/
def Account.debit (address : Address) (amount : U256) (account : Account) :
    Except StateError Account :=
  if account.balance < amount then
    .error (.insufficientBalance address)
  else
    .ok { account with balance := account.balance - amount }

/-- Add `amount` wei to the account at an address, whose balance must stay below 2^256. -/
def Account.credit (address : Address) (amount : U256) (account : Account) :
    Except StateError Account :=
  if account.balance.toNat + amount.toNat < 2 ^ 256 then
    .ok { account with balance := account.balance + amount }
  else
    .error (.balanceOverflow address)

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
  /-- The addresses whose account the transaction read.

  A rollback keeps them. -/
  accountReads : Std.ExtTreeSet Address
  /-- The storage keys that the transaction read, at each address.

  A rollback keeps them. -/
  storageReads : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)

/-- A transaction with no write yet, in a block. -/
def TransactionState.ofBlock (block : BlockState) : TransactionState :=
  ⟨block, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅⟩

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

/-- The account at an address before the transaction, or none if it had no account.

The block's writes come first, then the state before the block. -/
def getPreStateAccountOptional (tx : TransactionState) (address : Address) : Option Account :=
  match tx.parent.accountWrites[address]? with
  | some account => account
  | none => tx.parent.preState.getAccountOptional address

/-- The account at an address before the transaction, or the empty account. -/
def getPreStateAccount (tx : TransactionState) (address : Address) : Account :=
  (tx.getPreStateAccountOptional address).getD EMPTY_ACCOUNT

/-- The word at a key of the transient storage of an address, or zero if none is set. -/
def getTransientStorage (tx : TransactionState) (address : Address) (key : Bytes32) : U256 :=
  (tx.transientStorage.slot address key).getD 0

/-- Whether the address has an account. -/
def accountExists (tx : TransactionState) (address : Address) : Bool :=
  (tx.getAccountOptional address).isSome

/-- Whether the storage of the address holds a word other than zero.

A key can only hold a word if some layer that the address's storage shows has it.

A wipe of the storage in a layer hides the layers below. -/
def accountHasStorage (tx : TransactionState) (address : Address) : Bool :=
  let keys (storage : StorageMap) := (storage.getD address ∅).keys
  let preKeys := keys tx.parent.preState.storage
  let parentKeys := keys tx.parent.storageWrites ++
    if address ∈ tx.parent.storageClears then [] else preKeys
  let txKeys := keys tx.storageWrites ++ if address ∈ tx.storageClears then [] else parentKeys
  txKeys.any fun key => tx.getStorage address key != 0

/-- Whether a contract may be deployed at the address.

Its account must have nonce 0 and no code, and its storage must hold only zeros.

[EIP-684](https://eips.ethereum.org/EIPS/eip-684#specification) asks for the nonce and the code.

[EIP-7610][eip7610] asks for the storage, at every fork. -/
def accountDeployable (tx : TransactionState) (address : Address) : Bool :=
  let account := tx.getAccount address
  account.nonce = 0 && account.codeHash = EMPTY_CODE_HASH && !tx.accountHasStorage address

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

/-! ## The record of reads -/

/-- Record a read of the account at an address. -/
def recordAccountRead (tx : TransactionState) (address : Address) : TransactionState :=
  { tx with accountReads := tx.accountReads.insert address }

/-- Record a read of a key of the storage of an address. -/
def recordStorageRead (tx : TransactionState) (address : Address) (key : Bytes32) :
    TransactionState :=
  { tx with
    storageReads := tx.storageReads.insert address ((tx.storageReads.getD address ∅).insert key) }

/-- The state `tx` with the reads of `other` in place of its own.

A call that stops keeps the reads that it made before it stopped. -/
def withReadsOf (tx other : TransactionState) : TransactionState :=
  { tx with accountReads := other.accountReads, storageReads := other.storageReads }

/-! ## Writes -/

/-- Set the account at an address, or delete it with none.

Deleting an account keeps its storage. -/
def setAccount (tx : TransactionState) (address : Address) (account : Option Account) :
    TransactionState :=
  { tx with accountWrites := tx.accountWrites.insert address account }

/-- Set the word at a key of the storage of an address.

The address must have an account, which the write reads. -/
def setStorage (tx : TransactionState) (address : Address) (key : Bytes32) (value : U256) :
    Except StateError TransactionState :=
  if (tx.getAccountOptional address).isNone then
    .error (.noAccount address)
  else
    let tx := tx.recordAccountRead address
    .ok { tx with
      storageWrites := tx.storageWrites.insert address
        ((tx.storageWrites.getD address ∅).insert key value) }

/-- Wipe the storage of an address: drop its writes, and hide every earlier word.

The keys it wrote become reads, so a wiped slot still counts as accessed. -/
def destroyStorage (tx : TransactionState) (address : Address) : TransactionState :=
  let written := (tx.storageWrites.getD address ∅).keys
  { tx with
    storageWrites := tx.storageWrites.erase address
    storageClears := tx.storageClears.insert address
    storageReads := tx.storageReads.insert address
      ((tx.storageReads.getD address ∅).insertMany written) }

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

The change reads the account first.

An address with no account starts from the empty account.

From Paris, a change that leaves the account empty deletes it. -/
def modifyState (fork : Fork) (tx : TransactionState) (address : Address)
    (f : Account → Except StateError Account) : Except StateError TransactionState := do
  let tx := tx.recordAccountRead address
  let tx := tx.setAccount address (some (← f (tx.getAccount address)))
  if fork ≥ .paris && tx.accountExistsAndIsEmpty address then
    return tx.destroyAccount address
  else
    return tx

/-- Move `amount` wei from the sender to the recipient.

The sender must hold the amount, and the recipient's balance must stay below 2^256. -/
def moveEther (fork : Fork) (tx : TransactionState) (sender recipient : Address) (amount : U256) :
    Except StateError TransactionState := do
  let tx ← tx.modifyState fork sender (Account.debit sender amount)
  tx.modifyState fork recipient (Account.credit recipient amount)

/-- Add newly created ether to the balance of an address, which must stay below 2^256. -/
def createEther (fork : Fork) (tx : TransactionState) (address : Address) (amount : U256) :
    Except StateError TransactionState :=
  tx.modifyState fork address (Account.credit address amount)

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

/-- Clear the nonce, the code and the storage of an address, and keep its balance.

From Glamsterdam, the end of a transaction does this to each account that SELFDESTRUCT marked.

From Paris, an account that this leaves empty is deleted. -/
def clearAccountPreservingBalance (fork : Fork) (tx : TransactionState) (address : Address) :
    Except StateError TransactionState :=
  (tx.destroyStorage address).modifyState fork address fun account =>
    .ok { account with nonce := 0, codeHash := EMPTY_CODE_HASH }

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

The accounts that the transaction created stay recorded, and so do its reads. -/
def restoreTxState (tx snapshot : TransactionState) : TransactionState :=
  { snapshot with
    parent := tx.parent
    createdAccounts := tx.createdAccounts
    accountReads := tx.accountReads
    storageReads := tx.storageReads }

/-- The words of `slots` written over those of `base`. -/
def writeSlots (base slots : Std.ExtTreeMap Bytes32 U256) : Std.ExtTreeMap Bytes32 U256 :=
  slots.foldl (fun acc key value => acc.insert key value) base

/-- Move the writes of a transaction into its block, and start the next transaction.

A wipe of the transaction drops the block's writes to that storage first.

The next transaction has no write and no read, so its transient storage is empty. -/
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

/-! ## The state after a block -/

namespace BlockState

/-- The words of `slots` written over those of `base`, where the word zero removes its key. -/
def applySlots (base slots : Std.ExtTreeMap Bytes32 U256) : Std.ExtTreeMap Bytes32 U256 :=
  slots.foldl (fun acc key value => if value = 0 then acc.erase key else acc.insert key value) base

/-- The state after the block: the state before it, with every write of the block.

A wipe drops the earlier storage of its address first.

A deleted account leaves the state, and the code of each write joins the code of the state.

A key with the word zero leaves the storage, and so does an address with no key left. -/
def applyChanges (block : BlockState) : State :=
  let pre := block.preState
  let storage := block.storageClears.foldl (fun acc address => acc.erase address) pre.storage
  { accounts := block.accountWrites.foldl
      (fun acc address account =>
        match account with
        | some account => acc.insert address account
        | none => acc.erase address)
      pre.accounts
    storage := block.storageWrites.foldl
      (fun acc address slots =>
        let merged := applySlots (acc.getD address ∅) slots
        if merged.isEmpty then acc.erase address else acc.insert address merged)
      storage
    code := block.codeWrites.foldl (fun acc codeHash code => acc.insert codeHash code) pre.code }

end BlockState

end EthLib.Execution.State

module

public import EthLib.Base.Fork
public import EthLib.Execution.State.Root
public import Std.Data.ExtTreeSet

/-!
# `State.Tracker`

The changes that a block and a transaction make to the state, kept apart from the state.

The state is `sigma` of the [Yellow Paper][yp], §4.1, held as layers of writes.

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

A transaction also records the accounts and the storage keys it reads.

From Glamsterdam, the block access list of [EIP-7928][eip7928] holds them.

It holds them even when the call that read them reverts, so a rollback keeps them.

From Glamsterdam, [EIP-8246][eip8246] clears an account that SELFDESTRUCT marked.

That clear keeps the balance.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip1153]: https://eips.ethereum.org/EIPS/eip-1153#specification
[eip7523]: https://eips.ethereum.org/EIPS/eip-7523#specification
[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
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
  -- A balance below `v` fails: the Yellow Paper leaves that check to the callers of §8.
  if account.balance < amount then
    .error (.insufficientBalance address)
  else
    -- Yellow Paper §8: `sigma_1[s]_b = sigma[s]_b - v`.
    .ok { account with balance := account.balance - amount }

/-- Add `amount` wei to the account at an address, whose balance must stay below 2^256. -/
def Account.credit (address : Address) (amount : U256) (account : Account) :
    Except StateError Account :=
  -- §4.1 requires `sigma[a]_b` in `N_256`, so a sum of at least `2^256` fails.
  if account.balance.toNat + amount.toNat < 2 ^ 256 then
    -- Yellow Paper §8: `sigma_1[r]_b = sigma[r]_b + v`.
    .ok { account with balance := account.balance + amount }
  else
    .error (.balanceOverflow address)

/-! ## The state before a block -/

/-- The account at an address, or none if the address has no account. -/
def State.getAccountOptional (state : State) (address : Address) : Option Account :=
  -- `sigma[a]`, with none for `sigma[a] = ∅`.
  state.accounts[address]?

/-- The word at a key of the storage of an address, or zero if none is set. -/
def State.getStorage (state : State) (address : Address) (key : Bytes32) : U256 :=
  (StorageMap.slot state.storage address key).getD 0

/-- The code with a code hash.

The empty code needs no entry, and any other missing code is an error. -/
def State.getCode (state : State) (codeHash : Hash32) : Except StateError ByteArray :=
  -- `KEC(())` is the hash of the empty code, which the state does not store.
  if codeHash = EMPTY_CODE_HASH then
    .ok .empty
  else
    -- Any other hash names the code `b` with `KEC(b)` equal to it, which the state must hold.
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
  -- A write of the transaction, where none stands for a deleted account.
  match tx.accountWrites[address]? with
  | some account => account
  | none =>
    -- Else a write of the block so far.
    match tx.parent.accountWrites[address]? with
    | some account => account
    -- Else `sigma[a]` in the state before the block.
    | none => tx.parent.preState.getAccountOptional address

/-- The account at an address, or the empty account if the address has no account. -/
def getAccount (tx : TransactionState) (address : Address) : Account :=
  -- `sigma[a] = ∅` reads as the account with nonce 0, balance 0 and no code.
  (tx.getAccountOptional address).getD EMPTY_ACCOUNT

/-- The code with a code hash, from the writes first. -/
def getCode (tx : TransactionState) (codeHash : Hash32) : Except StateError ByteArray :=
  -- `KEC(())` is the hash of the empty code, which no layer stores.
  if codeHash = EMPTY_CODE_HASH then
    .ok .empty
  else
    -- The code that the transaction wrote, then the block, then the state before the block.
    match tx.codeWrites[codeHash]? with
    | some code => .ok code
    | none =>
      match tx.parent.codeWrites[codeHash]? with
      | some code => .ok code
      | none => tx.parent.preState.getCode codeHash

/-- The word at a key of the storage of an address, or zero if none is set.

A wipe of the storage hides every earlier word. -/
def getStorage (tx : TransactionState) (address : Address) (key : Bytes32) : U256 :=
  -- A word that the transaction wrote at the key.
  match tx.storageWrites.slot address key with
  | some value => value
  | none =>
    -- Else 0, if the transaction wiped the storage of the address.
    if address ∈ tx.storageClears then 0 else
    -- Else a word that the block wrote, or 0 after a wipe of the block.
    match tx.parent.storageWrites.slot address key with
    | some value => value
    | none =>
      -- Else the word of the state before the block.
      if address ∈ tx.parent.storageClears then 0 else tx.parent.preState.getStorage address key

/-- The word at a key before the transaction began.

It is zero for an account that the transaction created.

[EIP-2200](https://eips.ethereum.org/EIPS/eip-2200#specification) prices a storage write by it. -/
def getStorageOriginal (tx : TransactionState) (address : Address) (key : Bytes32) : U256 :=
  -- The original value of EIP-2200, as EIP-1283 defines it: the value if the transaction reverts.
  --
  -- The storage of an account that the transaction created was empty before it.
  if address ∈ tx.createdAccounts then 0 else
  -- Else the word after the earlier transactions of the block, which skips the writes of this one.
  match tx.parent.storageWrites.slot address key with
  | some value => value
  | none =>
    if address ∈ tx.parent.storageClears then 0 else tx.parent.preState.getStorage address key

/-- The account at an address before the transaction, or none if it had no account.

The block's writes come first, then the state before the block. -/
def getPreStateAccountOptional (tx : TransactionState) (address : Address) : Option Account :=
  -- A write of the block so far, else `sigma[a]` before the block, past the transaction's writes.
  match tx.parent.accountWrites[address]? with
  | some account => account
  | none => tx.parent.preState.getAccountOptional address

/-- The account at an address before the transaction, or the empty account. -/
def getPreStateAccount (tx : TransactionState) (address : Address) : Account :=
  (tx.getPreStateAccountOptional address).getD EMPTY_ACCOUNT

/-- The word at a key of the transient storage of an address, or zero if none is set. -/
def getTransientStorage (tx : TransactionState) (address : Address) (key : Bytes32) : U256 :=
  -- EIP-1153: the word at a key of the transient storage, 0 for a key never written.
  (tx.transientStorage.slot address key).getD 0

/-- Whether the address has an account. -/
def accountExists (tx : TransactionState) (address : Address) : Bool :=
  -- `sigma[a] ≠ ∅`.
  (tx.getAccountOptional address).isSome

/-- Whether the storage of the address holds a word other than zero.

It reads every key that the transaction, the block or the state before the block holds. -/
def accountHasStorage (tx : TransactionState) (address : Address) : Bool :=
  -- Every key that some layer holds, since a key in none of them reads 0.
  let keys := (tx.storageWrites.getD address ∅).keys ++
    (tx.parent.storageWrites.getD address ∅).keys ++
    (tx.parent.preState.storage.getD address ∅).keys
  -- A key may hold 0 at the top layer, after a write of 0 or a wipe, so each key is read again.
  keys.any fun key => tx.getStorage address key != 0

/-- Whether a contract may be deployed at the address.

Its account must have nonce 0 and no code, by [EIP-684][eip684].

Its storage must be empty, by [EIP-7610][eip7610], at every fork.

[eip684]: https://eips.ethereum.org/EIPS/eip-684#specification
[eip7610]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7610.md#specification -/
def accountDeployable (tx : TransactionState) (address : Address) : Bool :=
  let account := tx.getAccount address
  -- EIP-684: a zero nonce and an empty code.
  --
  -- EIP-7610 adds an empty storage.
  account.nonce = 0 && account.codeHash = EMPTY_CODE_HASH && !tx.accountHasStorage address

/-- Whether the address has an account with nonce 0, no code and balance 0. -/
def accountExistsAndIsEmpty (tx : TransactionState) (address : Address) : Bool :=
  match tx.getAccountOptional address with
  -- §4.1: `EMPTY(sigma, a)` is `sigma[a]_c = KEC(()) ∧ sigma[a]_n = 0 ∧ sigma[a]_b = 0`.
  | some account => account.nonce = 0 && account.codeHash = EMPTY_CODE_HASH && account.balance = 0
  -- `sigma[a] = ∅` is dead but not empty.
  | none => false

/-- Whether the address has an account that is not the empty account. -/
def isAccountAlive (tx : TransactionState) (address : Address) : Bool :=
  match tx.getAccountOptional address with
  -- Not `DEAD(sigma, a)`: the account exists, and `EMPTY(sigma, a)` fails.
  | some account => account != EMPTY_ACCOUNT
  | none => false

/-! ## The record of reads -/

/-- Record a read of the account at an address. -/
def recordAccountRead (tx : TransactionState) (address : Address) : TransactionState :=
  -- EIP-7928: each address that the transaction accesses enters the block access list.
  { tx with accountReads := tx.accountReads.insert address }

/-- Record a read of a key of the storage of an address. -/
def recordStorageRead (tx : TransactionState) (address : Address) (key : Bytes32) :
    TransactionState :=
  -- EIP-7928: each key read at the address is a storage read, at most once per account.
  { tx with
    storageReads := tx.storageReads.insert address ((tx.storageReads.getD address ∅).insert key) }

/-- The state `tx` with the reads of `other` in place of its own.

A call that stops keeps the reads that it made before it stopped. -/
def withReadsOf (tx other : TransactionState) : TransactionState :=
  -- EIP-7928: a reverted call discards its changes, but its accessed addresses and read keys stay.
  { tx with accountReads := other.accountReads, storageReads := other.storageReads }

/-! ## Writes -/

/-- Set the account at an address, or delete it with none.

Deleting an account keeps its storage. -/
def setAccount (tx : TransactionState) (address : Address) (account : Option Account) :
    TransactionState :=
  -- `sigma'[a]`, or `sigma'[a] = ∅` with none; the storage is a separate layer, so it stays.
  { tx with accountWrites := tx.accountWrites.insert address account }

/-- Set the word at a key of the storage of an address.

The address must have an account, which the write reads. -/
def setStorage (tx : TransactionState) (address : Address) (key : Bytes32) (value : U256) :
    Except StateError TransactionState :=
  -- Storage belongs to an account, so `sigma[a] = ∅` fails.
  if (tx.getAccountOptional address).isNone then
    .error (.noAccount address)
  else
    let tx := tx.recordAccountRead address
    -- `sigma'[a]_s[k] = v`, written over the earlier words of the transaction.
    .ok { tx with
      storageWrites := tx.storageWrites.insert address
        ((tx.storageWrites.getD address ∅).insert key value) }

/-- Wipe the storage of an address: drop its writes, and hide every earlier word.

The keys it wrote become reads, so a wiped slot still counts as accessed. -/
def destroyStorage (tx : TransactionState) (address : Address) : TransactionState :=
  let written := (tx.storageWrites.getD address ∅).keys
  { tx with
    -- `sigma'[a]_s = TRIE(∅)`: the writes go, and the wipe hides the words of the lower layers.
    storageWrites := tx.storageWrites.erase address
    storageClears := tx.storageClears.insert address
    -- EIP-7928: the keys it wrote count as storage reads, as for a self-destructed account.
    storageReads := tx.storageReads.insert address
      ((tx.storageReads.getD address ∅).insertMany written) }

/-- Delete the account at an address, with its storage. -/
def destroyAccount (tx : TransactionState) (address : Address) : TransactionState :=
  -- `sigma'[a] = ∅`, the storage of the account included.
  (tx.destroyStorage address).setAccount address none

/-- Record that the transaction created the account at an address. -/
def markAccountCreated (tx : TransactionState) (address : Address) : TransactionState :=
  -- EIP-6780 asks whether the transaction created the account.
  --
  -- The storage of such an account was empty before the transaction, so its original values are 0.
  { tx with createdAccounts := tx.createdAccounts.insert address }

/-- Set the word at a key of the transient storage of an address.

The word zero removes the key. -/
def setTransientStorage (tx : TransactionState) (address : Address) (key : Bytes32)
    (value : U256) : TransactionState :=
  let slots := tx.transientStorage.getD address ∅
  -- EIP-1153: the word `v` at key `k` of the address.
  --
  -- A key at 0 reads as a key never written, so it is dropped.
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
  -- `sigma'[a] = f(sigma[a])`, where `sigma[a] = ∅` reads as the empty account.
  let tx := tx.setAccount address (some (← f (tx.getAccount address)))
  -- EIP-161 deletes a touched empty account at the end of the transaction.
  --
  -- From Paris, EIP-7523 forbids empty accounts, so the deletion happens at once.
  if fork ≥ .paris && tx.accountExistsAndIsEmpty address then
    return tx.destroyAccount address
  else
    return tx

/-- Move `amount` wei from the sender to the recipient.

The sender must hold the amount, and the recipient's balance must stay below 2^256. -/
def moveEther (fork : Fork) (tx : TransactionState) (sender recipient : Address) (amount : U256) :
    Except StateError TransactionState := do
  -- Yellow Paper §8: `sigma_1[r]_b = sigma[r]_b + v` and `sigma_1[s]_b = sigma[s]_b - v`.
  --
  -- The debit comes first, so the balance check runs before the credit.
  --
  -- The source excludes `s = r`; here the debit and the credit cancel, once the check passes.
  let tx ← tx.modifyState fork sender (Account.debit sender amount)
  tx.modifyState fork recipient (Account.credit recipient amount)

/-- Add newly created ether to the balance of an address, which must stay below 2^256. -/
def createEther (fork : Fork) (tx : TransactionState) (address : Address) (amount : U256) :
    Except StateError TransactionState :=
  -- `sigma'[a]_b = sigma[a]_b + v`, with no account debited.
  tx.modifyState fork address (Account.credit address amount)

/-- Set the balance of an address. -/
def setAccountBalance (fork : Fork) (tx : TransactionState) (address : Address) (amount : U256) :
    Except StateError TransactionState :=
  -- `sigma'[a]_b = v`.
  tx.modifyState fork address fun account => .ok { account with balance := amount }

/-- Add one to the nonce of an address. -/
def incrementNonce (fork : Fork) (tx : TransactionState) (address : Address) :
    Except StateError TransactionState :=
  -- `sigma'[a]_n = sigma[a]_n + 1`.
  tx.modifyState fork address fun account => .ok { account with nonce := account.nonce + 1 }

/-- Set the code of an address, and keep the code under its Keccak-256 hash. -/
def setCode (fork : Fork) (tx : TransactionState) (address : Address) (code : ByteArray) :
    Except StateError TransactionState :=
  -- Yellow Paper §4.1: the code `b` is kept under `KEC(b)`.
  let codeHash : Hash32 := Cryptography.Hash.Keccak.keccak256 code
  -- The empty code needs no entry, since every read knows `KEC(())`.
  let tx := if codeHash = EMPTY_CODE_HASH then tx else
    { tx with codeWrites := tx.codeWrites.insert codeHash code }
  -- `sigma'[a]_c = KEC(b)`.
  tx.modifyState fork address fun account => .ok { account with codeHash := codeHash }

/-- Clear the nonce, the code and the storage of an address, and keep its balance.

From Glamsterdam, the end of a transaction does this to each account that SELFDESTRUCT marked.

From Paris, an account that this leaves empty is deleted. -/
def clearAccountPreservingBalance (fork : Fork) (tx : TransactionState) (address : Address) :
    Except StateError TransactionState :=
  -- EIP-8246, step 2.4: all storage is cleared.
  --
  -- Steps 2.1 to 2.3: the nonce becomes 0, the balance stays, and the code is cleared.
  --
  -- Its second note: a balance of 0 leaves an empty account, which EIP-161 deletes.
  (tx.destroyStorage address).modifyState fork address fun account =>
    .ok { account with nonce := 0, codeHash := EMPTY_CODE_HASH }

/-- Give an address with no account the empty account.

Before Paris, a transaction touches accounts in this way. -/
def touchAccount (tx : TransactionState) (address : Address) : TransactionState :=
  -- Yellow Paper §8 creates an absent recipient only for `v ≠ 0`, as `(0, v, TRIE(∅), KEC(()))`.
  --
  -- Here the empty account is created whatever `v` is.
  --
  -- From Spurious Dragon, EIP-161 deletes it at the end of the transaction if it is still empty.
  if tx.accountExists address then tx else tx.setAccount address (some EMPTY_ACCOUNT)

/-- Delete each touched account that is empty, as EIP-161 asks from Spurious Dragon.

Before Spurious Dragon, nothing is deleted. -/
def destroyTouchedEmptyAccounts (fork : Fork) (tx : TransactionState) (touched : List Address) :
    TransactionState :=
  -- EIP-161 starts at Spurious Dragon.
  if fork < .spuriousDragon then tx else
  -- Yellow Paper §6.2: `sigma'[i] = ∅` for each `i` in `A_t` with `DEAD(sigma*, i)`.
  --
  -- An `i` with `sigma*[i] = ∅` stays absent, so only the empty accounts change.
  touched.foldl
    (fun tx address => if tx.accountExistsAndIsEmpty address then tx.destroyAccount address else tx)
    tx

/-! ## Rollback and the end of a transaction -/

/-- Restore the writes of a snapshot after a failed call.

The accounts that the transaction created stay recorded, and so do its reads. -/
def restoreTxState (tx snapshot : TransactionState) : TransactionState :=
  -- The writes of the snapshot, with the transient storage: EIP-1153 reverts it with the call.
  { snapshot with
    parent := tx.parent
    -- The created accounts outlive a revert; EIP-6780 does not address a reverted creation.
    createdAccounts := tx.createdAccounts
    -- EIP-7928: the accessed addresses and the read keys of a reverted call stay.
    accountReads := tx.accountReads
    storageReads := tx.storageReads }

/-- The words of `slots` written over those of `base`. -/
def writeSlots (base slots : Std.ExtTreeMap Bytes32 U256) : Std.ExtTreeMap Bytes32 U256 :=
  -- A word of 0 stays as a write, so that it still hides the word of the state before the block.
  slots.foldl (fun acc key value => acc.insert key value) base

/-- Move the writes of a transaction into its block, and start the next transaction.

A wipe of the transaction drops the block's writes to that storage first.

The next transaction has no write and no read, so its transient storage is empty. -/
def incorporateTxIntoBlock (tx : TransactionState) : TransactionState :=
  let block := tx.parent
  -- A wipe of the transaction drops the earlier words that the block wrote at its address.
  let storageWrites := tx.storageClears.foldl (fun acc address => acc.erase address)
    block.storageWrites
  -- The next transaction starts with no write, no read and, by EIP-1153, no transient storage.
  ofBlock {
    preState := block.preState
    -- Each write of the transaction replaces the write of the block at its address or key.
    accountWrites := tx.accountWrites.foldl (fun acc address account => acc.insert address account)
      block.accountWrites
    storageWrites := tx.storageWrites.foldl
      (fun acc address slots => acc.insert address (writeSlots (acc.getD address ∅) slots))
      storageWrites
    codeWrites := tx.codeWrites.foldl (fun acc codeHash code => acc.insert codeHash code)
      block.codeWrites
    -- The wipes join those of the block, to hide the state before the block.
    storageClears := tx.storageClears.foldl (fun acc address => acc.insert address)
      block.storageClears }

end TransactionState

/-! ## The state after a block -/

namespace BlockState

/-- The words of `slots` written over those of `base`, where the word zero removes its key. -/
def applySlots (base slots : Std.ExtTreeMap Bytes32 U256) : Std.ExtTreeMap Bytes32 U256 :=
  -- A key at 0 leaves the storage, since every location reads 0 until written (Yellow Paper §9.1).
  slots.foldl (fun acc key value => if value = 0 then acc.erase key else acc.insert key value) base

/-- The state after the block: the state before it, with every write of the block.

A wipe drops the earlier storage of its address first.

A deleted account leaves the state, and the code of each write joins the code of the state.

A key with the word zero leaves the storage, and so does an address with no key left. -/
def applyChanges (block : BlockState) : State :=
  let pre := block.preState
  -- First each wipe empties the storage of its address.
  let storage := block.storageClears.foldl (fun acc address => acc.erase address) pre.storage
  -- Each written account replaces `sigma[a]`, and a deleted one makes `sigma[a] = ∅`.
  { accounts := block.accountWrites.foldl
      (fun acc address account =>
        match account with
        | some account => acc.insert address account
        | none => acc.erase address)
      pre.accounts
    -- Then the words of the block, and an address with no key left has the empty storage.
    storage := block.storageWrites.foldl
      (fun acc address slots =>
        let merged := applySlots (acc.getD address ∅) slots
        if merged.isEmpty then acc.erase address else acc.insert address merged)
      storage
    code := block.codeWrites.foldl (fun acc codeHash code => acc.insert codeHash code) pre.code }

end BlockState

end EthLib.Execution.State

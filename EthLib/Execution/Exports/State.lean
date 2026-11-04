module

public import EthLib.Base.Exports
public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Blocks.DaoFork
public import EthLib.Execution.Blocks.Rewards
public import EthLib.Execution.State.Root
public import EthLib.Execution.State.Errors

/-!
# `Exports.State`

C-ABI exports for the state root, callable from the Python C extension.

A state crosses the boundary as RLP bytes: a list of accounts.

Each account is the list of its address, nonce, balance, code and storage.

The storage is a list of pairs of a 32-byte key and a word.

The code hash of an account is the Keccak-256 hash of its code.

A malformed input, or an address given twice, comes back as the code and the message of its error.

A failed change to the state has a code from 101.

A fork name crosses the boundary as the name of its case in Lean, such as `shapella`.

An unknown fork, a fork before Shapella, or a block that does not decode, has code 0.

So does Hegotá, which is not yet specified.
-/

public section

namespace EthLib.Execution.State.Exports

open EthLib.Exports (Result forkUpTo)

open EthLib.Base
open EthLib.Execution.State
open EthLib.Serialization.Rlp

/-- One account of the input: its address, nonce, balance, code and storage. -/
structure Entry where
  /-- The address of the account. -/
  address : Address
  /-- The nonce of the account. -/
  nonce : Nat
  /-- The balance of the account. -/
  balance : U256
  /-- The code of the account. -/
  code : ByteArray
  /-- The storage of the account, as pairs of a key and a word. -/
  storage : List (Bytes32 × U256)

/-- A key and a word: a list of exactly two items. -/
def ofSlotItem (item : Item) : Except RlpError (Bytes32 × U256) := do
  match ← item.fields 2 with
  | [key, value] => return (← Codec.ofItem key, ← Codec.ofItem value)
  | items => .error (.wrongFieldCount 2 items.length)

/-- An account of the input: a list of exactly five items. -/
def ofEntryItem (item : Item) : Except RlpError Entry := do
  match ← item.fields 5 with
  | [address, nonce, balance, code, storage] =>
    return ⟨← Codec.ofItem address, ← Codec.ofItem nonce, ← Codec.ofItem balance,
      ← Codec.ofItem code, ← (← storage.toItems).mapM ofSlotItem⟩
  | items => .error (.wrongFieldCount 5 items.length)

/-- The state that the accounts of the input hold, or an error for an address given twice. -/
def ofEntries (entries : List Entry) : Except StateInputError State :=
  entries.foldlM (init := ⟨∅, ∅, ∅⟩) fun state entry => do
    if entry.address ∈ state.accounts then
      throw .repeatedAddress
    let codeHash := Cryptography.Hash.Keccak.keccak256 entry.code
    return {
      accounts := state.accounts.insert entry.address ⟨entry.nonce, entry.balance, codeHash⟩
      storage := state.storage.insert entry.address (.ofList entry.storage)
      code := state.code.insert codeHash entry.code }

/-- The state that `input` encodes. -/
def ofInput (input : ByteArray) : Except StateInputError State := do
  let item ← (decode input).mapError .notAnItem
  let items ← item.toItems.mapError .notAList
  let entries ← (items.mapM ofEntryItem).mapError .badAccount
  ofEntries entries

/-- The 32-byte state root of a state, with Keccak-256, or the code and message of its error. -/
def rootOf (state : State) : Result ByteArray :=
  match stateRoot Cryptography.Hash.Keccak.keccak256 state with
  | .ok root => return ⟨root.toArray⟩
  | .error e => throw ((StateInputError.noRoot e).code, (StateInputError.noRoot e).message)

/-- The 32-byte state root, with Keccak-256, of the state that `input` encodes. -/
@[export eth_state_root]
def stateRootExport (input : ByteArray) : Result ByteArray := do
  rootOf (← (ofInput input).mapError fun e => (e.code, e.message))

/-- The state root after the withdrawals of a block, from the state that `input` encodes.

The block is decoded at the fork, which must be Shapella or later. -/
@[export eth_state_withdrawals_root]
def withdrawalsRootExport (fork input block : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  let pre ← (ofInput input).mapError fun e => (e.code, e.message)
  let b : Blocks.Block fork Item ← (Codec.decode block).mapError
    fun e => (0, s!"block rejected: {reprStr e}")
  if h : .shapella ≤ fork then
    let post ← (Blocks.processWithdrawals fork ⟨pre, ∅, ∅, ∅, ∅⟩ (b.withdrawals h)).mapError
      fun e => (e.code, s!"withdrawals failed: {reprStr e}")
    rootOf post.applyChanges
  else throw (0, "the fork is before Shapella")

/-- The state root after the DAO Fork moves the ether of its accounts, from the state of `input`. -/
@[export eth_state_dao_fork_root]
def daoForkRootExport (input : ByteArray) : Result ByteArray := do
  let pre ← (ofInput input).mapError fun e => (e.code, e.message)
  let tx ← (Blocks.applyDaoFork .daoFork (.ofBlock ⟨pre, ∅, ∅, ∅, ∅⟩)).mapError
    fun e => (e.code, s!"the DAO Fork failed: {reprStr e}")
  rootOf tx.incorporateTxIntoBlock.parent.applyChanges

/-- The state root after the mining rewards of a block, from the state that `input` encodes.

The block is decoded at the fork; from Paris on it pays no reward. -/
@[export eth_state_rewards_root]
def rewardsRootExport (fork input block : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  let pre ← (ofInput input).mapError fun e => (e.code, e.message)
  let b : Blocks.Block fork Item ← (Codec.decode block).mapError
    fun e => (0, s!"block rejected: {reprStr e}")
  let ommers := b.ommers.map fun o => (o.coinbase, o.number)
  let tx ← (Blocks.payRewards fork (.ofBlock ⟨pre, ∅, ∅, ∅, ∅⟩) b.header.coinbase b.header.number
    ommers).mapError fun e => (e.code, s!"rewards failed: {reprStr e}")
  rootOf tx.incorporateTxIntoBlock.parent.applyChanges

end EthLib.Execution.State.Exports

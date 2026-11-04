module

public import EthLib.Execution.State.Root

/-!
# `Exports.State`

C-ABI exports for the state root, callable from the Python C extension.

A state crosses the boundary as RLP bytes: a list of accounts.

Each account is the list of its address, nonce, balance, code and storage.

The storage is a list of pairs of a 32-byte key and a word.

The code hash of an account is the Keccak-256 hash of its code.

A malformed input, or an address given twice, is an `IO` error, which Python raises.
-/

public section

namespace EthLib.Execution.State.Exports

open EthLib.Base
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
def ofEntries (entries : List Entry) : Except String State :=
  entries.foldlM (init := ⟨∅, ∅, ∅⟩) fun state entry => do
    if entry.address ∈ state.accounts then
      throw "an address is given twice"
    let codeHash := Cryptography.Hash.Keccak.keccak256 entry.code
    return {
      accounts := state.accounts.insert entry.address ⟨entry.nonce, entry.balance, codeHash⟩
      storage := state.storage.insert entry.address (.ofList entry.storage)
      code := state.code.insert codeHash entry.code }

/-- The 32-byte state root, with Keccak-256, of the state that `input` encodes. -/
@[export eth_state_root]
def stateRootExport (input : ByteArray) : IO ByteArray := do
  let .ok item := decode input | throw (IO.userError "state is not one RLP item")
  let .ok items := item.toItems | throw (IO.userError "state is not an RLP list")
  let .ok entries := items.mapM ofEntryItem
    | throw (IO.userError "an account is not a list of address, nonce, balance, code and storage")
  let state ← IO.ofExcept (ofEntries entries)
  let .ok root := stateRoot Cryptography.Hash.Keccak.keccak256 state
    | throw (IO.userError "state has no root")
  return ⟨root.toArray⟩

end EthLib.Execution.State.Exports

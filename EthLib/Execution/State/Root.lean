module

public import EthLib.Execution.State.Account
public import EthLib.Execution.Trie.Root
public import Std.Data.ExtTreeMap

/-!
# `State.Root`

The state of every account, and the roots that commit to it.

Source: section 4.1 of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`][yp].

The storage of an account maps 32-byte keys to words.

A key with the word zero is absent from the storage.

The storage root is the root of a secured trie.

There, each key with a nonzero word holds the RLP encoding of the word.

The state root is the root of a secured trie too.

There, each address holds the RLP encoding of its account with its storage root.

The hash is an argument, and Ethereum passes Keccak-256.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Serialization.Rlp

/-- The state between two transactions: the accounts, their storage and their code.

Two states with the same entries are equal, whatever order the entries were set in. -/
structure State where
  /-- The account at each address that has one. -/
  accounts : Std.ExtTreeMap Address Account
  /-- The storage of each address, from 32-byte keys to words. -/
  storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)
  /-- The code with each code hash. -/
  code : Std.ExtTreeMap Hash32 ByteArray

/-- The entries of the storage trie: each key with a nonzero word, and the encoding of the word.

They come in the order of the keys. -/
def storageEntries (storage : Std.ExtTreeMap Bytes32 U256) :
    Except RlpError (List (ByteArray × ByteArray)) :=
  (storage.filter fun _ value => value != 0).toList.mapM fun (key, value) => do
    return (⟨key.toArray⟩, ← Codec.encode value)

/-- The storage root: the root of the secured trie of the storage entries. -/
def storageRoot (hash : ByteArray → Hash32) (storage : Std.ExtTreeMap Bytes32 U256) :
    Except TrieError Hash32 := do
  root hash ⟨true, ← (storageEntries storage).mapError .rlp⟩

/-- The entries of the state trie: each address, and the encoding of its account and storage root.

An address with no storage has the storage root of the empty storage.

They come in the order of the addresses. -/
def stateEntries (hash : ByteArray → Hash32) (state : State) :
    Except TrieError (List (ByteArray × ByteArray)) :=
  state.accounts.toList.mapM fun (address, account) => do
    let storageHash ← storageRoot hash (state.storage.getD address ∅)
    return (⟨address.toArray⟩, ← (encodeAccount account storageHash).mapError .rlp)

/-- The state root: the root of the secured trie of the state entries. -/
def stateRoot (hash : ByteArray → Hash32) (state : State) : Except TrieError Hash32 := do
  root hash ⟨true, ← stateEntries hash state⟩

end EthLib.Execution.State

module

public import EthLib.Base.Hash32
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Serialization.Rlp.Codec

/-!
# `State.Account`

The state of one account, and its RLP form.

Source: section 4.1 of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`][yp].

An account holds a nonce, a balance and the hash of its code.

Its storage is kept apart, so the RLP form takes the root of the storage as an argument.

That form is the list of the nonce, the balance, the storage root and the code hash.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base
open EthLib.Serialization.Rlp

/-- The state of an account, without its storage. -/
structure Account where
  /-- The number of transactions that the account sent, or of contracts that it created. -/
  nonce : Nat
  /-- The ether that the account holds, in wei. -/
  balance : U256
  /-- The Keccak-256 hash of the code of the account. -/
  codeHash : Hash32
  deriving DecidableEq, Repr

/-- The Keccak-256 hash of the empty byte string, the code hash of an account with no code. -/
def EMPTY_CODE_HASH : Hash32 := Cryptography.Hash.Keccak.keccak256 .empty

/-- The account with nonce 0, balance 0 and no code. -/
def EMPTY_ACCOUNT : Account := ⟨0, 0, EMPTY_CODE_HASH⟩

/-- The RLP item of an account with the root of its storage. -/
def Account.toItem (account : Account) (storageRoot : Hash32) : Item :=
  .list [Codec.toItem account.nonce, Codec.toItem account.balance, Codec.toItem storageRoot,
    Codec.toItem account.codeHash]

/-- The account and the storage root that an item holds.

The item must be a list of exactly four fields, each of which holds a value of its type. -/
def Account.ofItem (item : Item) : Except RlpError (Account × Hash32) := do
  match ← item.fields 4 with
  | [nonce, balance, storageRoot, codeHash] =>
    return (⟨← Codec.ofItem nonce, ← Codec.ofItem balance, ← Codec.ofItem codeHash⟩,
      ← Codec.ofItem storageRoot)
  | items => .error (.wrongFieldCount 4 items.length)

/-- The RLP encoding of an account with its storage root: its value in the state trie. -/
def encodeAccount (account : Account) (storageRoot : Hash32) : Except RlpError ByteArray :=
  encode (account.toItem storageRoot)

/-- The account and the storage root that `input` encodes.

It fails unless `input` is exactly the encoding of one item, and that item holds them. -/
def decodeAccount (input : ByteArray) : Except RlpError (Account × Hash32) := do
  Account.ofItem (← decode input)

end EthLib.Execution.State

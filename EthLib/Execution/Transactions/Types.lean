module

public import EthLib.Base.Address
public import EthLib.Base.Fork
public import EthLib.Serialization.Rlp.Item

/-!
# `Transactions.Types`

The five kinds of transaction, and the fork that adds each kind.

A transaction is legacy, or it is typed as [EIP-2718](https://eips.ethereum.org/EIPS/eip-2718) asks.

Section 4.3 of the Yellow Paper, Shanghai version, bounds each integer field below 2^256.

Source: [`Paper.tex` at `efc5f9a`][yp].

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Serialization.Rlp (RlpError)

/-- An entry of an access list: an account, and storage slots of that account.

[EIP-2930](https://eips.ethereum.org/EIPS/eip-2930#specification) adds access lists. -/
structure Access where
  /-- The account that the transaction accesses. -/
  account : Address
  /-- The storage slots of the account that the transaction accesses. -/
  slots : List Bytes32
  deriving DecidableEq, Repr

/-- The signed consent of an account to run the code of another address.

[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702#set-code-transaction) bounds each field. -/
structure Authorization where
  /-- The chain of the authorization, or 0 for every chain. -/
  chainId : U256
  /-- The address whose code the account runs. -/
  address : Address
  /-- The nonce of the account that signs. -/
  nonce : UInt64
  /-- The parity of `y` of the signature point. -/
  yParity : UInt8
  /-- The first integer of the signature. -/
  r : U256
  /-- The second integer of the signature. -/
  s : U256
  deriving DecidableEq, Repr

/-- A legacy transaction, the only kind before Berlin.

Section 4.3 of the Yellow Paper lists its nine fields.

From Spurious Dragon, the recovery id can also carry the chain.

[EIP-155](https://eips.ethereum.org/EIPS/eip-155#specification) defines that form. -/
structure LegacyTransaction where
  /-- The number of transactions that the sender sent before. -/
  nonce : U256
  /-- The price in wei of one unit of gas. -/
  gasPrice : U256
  /-- The most gas that the transaction can use. -/
  gas : U256
  /-- The recipient, or none for a contract creation. -/
  to : Option Address
  /-- The wei that the transaction sends. -/
  value : U256
  /-- The call data, or the init code of a contract creation. -/
  data : ByteArray
  /-- The recovery id of the signature, with the chain from Spurious Dragon. -/
  v : U256
  /-- The first integer of the signature. -/
  r : U256
  /-- The second integer of the signature. -/
  s : U256
  deriving DecidableEq

/-- A transaction of type 1, with a chain and an access list.

[EIP-2930](https://eips.ethereum.org/EIPS/eip-2930#specification) adds it at Berlin. -/
structure AccessListTransaction where
  /-- The chain of the transaction. -/
  chainId : U256
  /-- The number of transactions that the sender sent before. -/
  nonce : U256
  /-- The price in wei of one unit of gas. -/
  gasPrice : U256
  /-- The most gas that the transaction can use. -/
  gas : U256
  /-- The recipient, or none for a contract creation. -/
  to : Option Address
  /-- The wei that the transaction sends. -/
  value : U256
  /-- The call data, or the init code of a contract creation. -/
  data : ByteArray
  /-- The accounts and storage slots that the transaction accesses first. -/
  accessList : List Access
  /-- The parity of `y` of the signature point. -/
  yParity : U256
  /-- The first integer of the signature. -/
  r : U256
  /-- The second integer of the signature. -/
  s : U256
  deriving DecidableEq

/-- A transaction of type 2, with a priority fee and a maximum fee per unit of gas.

[EIP-1559](https://eips.ethereum.org/EIPS/eip-1559#specification) adds it at London. -/
structure FeeMarketTransaction where
  /-- The chain of the transaction. -/
  chainId : U256
  /-- The number of transactions that the sender sent before. -/
  nonce : U256
  /-- The most wei per unit of gas that goes to the fee recipient of the block. -/
  maxPriorityFeePerGas : U256
  /-- The most wei per unit of gas that the sender pays, base fee included. -/
  maxFeePerGas : U256
  /-- The most gas that the transaction can use. -/
  gas : U256
  /-- The recipient, or none for a contract creation. -/
  to : Option Address
  /-- The wei that the transaction sends. -/
  value : U256
  /-- The call data, or the init code of a contract creation. -/
  data : ByteArray
  /-- The accounts and storage slots that the transaction accesses first. -/
  accessList : List Access
  /-- The parity of `y` of the signature point. -/
  yParity : U256
  /-- The first integer of the signature. -/
  r : U256
  /-- The second integer of the signature. -/
  s : U256
  deriving DecidableEq

/-- A transaction of type 3, which carries blobs.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#blob-transaction) adds it at Dencun.

It always has a recipient, so it never creates a contract. -/
structure BlobTransaction where
  /-- The chain of the transaction. -/
  chainId : U256
  /-- The number of transactions that the sender sent before. -/
  nonce : U256
  /-- The most wei per unit of gas that goes to the fee recipient of the block. -/
  maxPriorityFeePerGas : U256
  /-- The most wei per unit of gas that the sender pays, base fee included. -/
  maxFeePerGas : U256
  /-- The most gas that the transaction can use. -/
  gas : U256
  /-- The recipient. -/
  to : Address
  /-- The wei that the transaction sends. -/
  value : U256
  /-- The call data. -/
  data : ByteArray
  /-- The accounts and storage slots that the transaction accesses first. -/
  accessList : List Access
  /-- The most wei per unit of blob gas that the sender pays. -/
  maxFeePerBlobGas : U256
  /-- The versioned hash of each blob. -/
  blobVersionedHashes : List Bytes32
  /-- The parity of `y` of the signature point. -/
  yParity : U256
  /-- The first integer of the signature. -/
  r : U256
  /-- The second integer of the signature. -/
  s : U256
  deriving DecidableEq

/-- A transaction of type 4, which sets the code of accounts.

[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702#set-code-transaction) adds it at Pectra.

It always has a recipient, so it never creates a contract. -/
structure SetCodeTransaction where
  /-- The chain of the transaction. -/
  chainId : U256
  /-- The number of transactions that the sender sent before. -/
  nonce : U256
  /-- The most wei per unit of gas that goes to the fee recipient of the block. -/
  maxPriorityFeePerGas : U256
  /-- The most wei per unit of gas that the sender pays, base fee included. -/
  maxFeePerGas : U256
  /-- The most gas that the transaction can use. -/
  gas : U256
  /-- The recipient. -/
  to : Address
  /-- The wei that the transaction sends. -/
  value : U256
  /-- The call data. -/
  data : ByteArray
  /-- The accounts and storage slots that the transaction accesses first. -/
  accessList : List Access
  /-- The authorizations, in the order in which they apply. -/
  authorizations : List Authorization
  /-- The parity of `y` of the signature point. -/
  yParity : U256
  /-- The first integer of the signature. -/
  r : U256
  /-- The second integer of the signature. -/
  s : U256
  deriving DecidableEq

/-- A transaction of one of the five kinds. -/
inductive Transaction where
  /-- A legacy transaction. -/
  | legacy (tx : LegacyTransaction)
  /-- A transaction of type 1. -/
  | accessList (tx : AccessListTransaction)
  /-- A transaction of type 2. -/
  | feeMarket (tx : FeeMarketTransaction)
  /-- A transaction of type 3. -/
  | blob (tx : BlobTransaction)
  /-- A transaction of type 4. -/
  | setCode (tx : SetCodeTransaction)
  deriving DecidableEq

namespace Transaction

/-- The type of a transaction: 0 for a legacy transaction, else its EIP-2718 type. -/
def type : Transaction → UInt8
  | .legacy _ => 0
  | .accessList _ => 1
  | .feeMarket _ => 2
  | .blob _ => 3
  | .setCode _ => 4

/-- The fork that adds the kind of a transaction. -/
def fork : Transaction → Fork
  | .legacy _ => .frontier
  | .accessList _ => .berlin
  | .feeMarket _ => .london
  | .blob _ => .dencun
  | .setCode _ => .pectra

end Transaction

/-- The fork that adds the typed transactions of type `type`, or none for a type that no fork has.

The type is the first byte of a typed transaction. -/
def typeFork (type : UInt8) : Option Fork :=
  if type = 1 then some .berlin
  else if type = 2 then some .london
  else if type = 3 then some .dencun
  else if type = 4 then some .pectra
  else none

/-- Why a transaction is not valid. -/
inductive TransactionError where
  /-- The input is empty, so it holds no transaction. -/
  | emptyTransaction
  /-- The first byte names a type of transaction that the fork does not have. -/
  | unsupportedType (type : UInt8)
  /-- The RLP of the transaction holds no value of its kind. -/
  | decoding (error : RlpError)
  /-- The fields that a signature covers have no RLP encoding, since a payload is too long. -/
  | encoding (error : RlpError)
  /-- The signature names no sender: a value is out of range, or no public key comes back. -/
  | invalidSignature
  deriving DecidableEq, Repr

end EthLib.Execution.Transactions

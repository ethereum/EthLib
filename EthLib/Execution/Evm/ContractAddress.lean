module

public import EthLib.Base.Address
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Serialization.Rlp.Codec

/-!
# `Evm.ContractAddress`

The address of a contract that CREATE or CREATE2 makes.

The address is the last 20 bytes of the Keccak-256 hash of a preimage.

CREATE hashes the RLP list of the sender and its nonce before the creation.

CREATE2 hashes the byte `0xff`, the sender, a 32-byte salt and the hash of the init code.

So the preimage of CREATE2 always has 85 bytes.

Section 7, Contract Creation, of the Yellow Paper, Shanghai version, defines both.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[EIP-1014][eip1014] adds CREATE2.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip1014]: https://eips.ethereum.org/EIPS/eip-1014#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address U256)
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The address in a Keccak-256 hash: its last 20 bytes. -/
def addressOfHash (hash : Vector UInt8 32) : Address :=
  hash.drop 12

/-- The preimage of the address of CREATE: the RLP list of the sender and its nonce.

The encoding fails only for a nonce of `2^(8 * 2^64)` or more. -/
def createPreimage (sender : Address) (nonce : Nat) : Except RlpError ByteArray :=
  encode (.list [Codec.toItem sender, Codec.toItem nonce])

/-- The address of the contract that the sender makes with CREATE, at its nonce. -/
def createAddress (sender : Address) (nonce : Nat) : Except RlpError Address := do
  return addressOfHash (keccak256 (← createPreimage sender nonce))

/-- The preimage of the address of CREATE2: `0xff`, the sender, the salt, the hash of the code. -/
def create2Preimage (sender : Address) (salt : U256) (initCodeHash : Vector UInt8 32) :
    ByteArray :=
  ⟨#[0xff]⟩ ++ ⟨sender.toArray⟩ ++ ⟨(U256.toBeBytes salt).toArray⟩ ++ ⟨initCodeHash.toArray⟩

/-- The address of the contract that the sender makes with CREATE2, from a salt and init code. -/
def create2Address (sender : Address) (salt : U256) (initCode : ByteArray) : Address :=
  addressOfHash (keccak256 (create2Preimage sender salt (keccak256 initCode)))

end EthLib.Execution.Evm

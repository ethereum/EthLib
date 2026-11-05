module

public import EthLib.Base.Fork
public import EthLib.Base.U256
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.Blocks.Log

/-!
# `Evm.Call.TransferLog`

From Glamsterdam, every move of ether to another account writes a log, by EIP-7708.

The log has the form of the `Transfer` event of ERC-20, and comes from the system address.

Its topics are the hash of the event signature, then the sender and the recipient as words.

Its data is the amount in wei, as a big-endian word.

A move of 0 wei, or from an account to itself, writes no log.

The value of a transaction, of CALL, of a creation and of SELFDESTRUCT each moves ether.

A frame that fails drops its logs, so its transfer log goes with them.

Source: [EIP-7708][eip7708], in Last Call.

[eip7708]: https://eips.ethereum.org/EIPS/eip-7708#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork Hash32 U256 toAddressMasked)
open EthLib.Execution.Blocks (Log)
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The system address `0xff…fe`, from EIP-4788.

System calls come from it, and the transfer logs of EIP-7708 name it as their address. -/
def SYSTEM_ADDRESS : Address :=
  toAddressMasked (BitVec.ofNat 256 0xfffffffffffffffffffffffffffffffffffffffe)

/-- The first topic of a transfer log: the Keccak-256 hash of `Transfer(address,address,uint256)`.

EIP-7708 gives it as `0xddf2…b3ef`. -/
def TRANSFER_TOPIC : Hash32 :=
  keccak256 "Transfer(address,address,uint256)".toUTF8

/-- The log of a move of `amount` wei from `sender` to `recipient`, by EIP-7708.

Each address fills a word, with zeros in front. -/
def transferLog (sender recipient : Address) (amount : U256) : Log where
  address := SYSTEM_ADDRESS
  topics := [TRANSFER_TOPIC, U256.toBeBytes sender.toU256, U256.toBeBytes recipient.toU256]
  data := ⟨(U256.toBeBytes amount).toArray⟩

/-- The logs at fork `fork` after a move of `amount` wei from `sender` to `recipient`.

From Glamsterdam, a move of a positive amount to another account gives one transfer log.

Otherwise, and at every earlier fork, the logs are as they were. -/
def pushTransferLog (fork : Fork) (logs : Array Log) (sender recipient : Address)
    (amount : U256) : Array Log :=
  if fork ≥ .glamsterdam ∧ amount ≠ 0 ∧ sender ≠ recipient then
    logs.push (transferLog sender recipient amount)
  else logs

end EthLib.Execution.Evm

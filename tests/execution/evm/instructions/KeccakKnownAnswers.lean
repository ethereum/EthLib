import EthLib.Execution.Evm.Instructions.Keccak

/-!
# Known answers for `keccak256Word`

Each check runs the adapter on one input and compares the word with the Keccak team's digest, read as a big-endian integer.

The digests are those of `ShortMsgKAT_256.txt` that `EthLib.Cryptography.Proofs.Hash.Keccak256` already checks in the kernel.

- The empty message.
- The one byte `0xCC`.
-/

open EthLib.Execution.Evm.Instructions

#guard keccak256Word ByteArray.empty
  = 0xC5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470#256

#guard keccak256Word (ByteArray.mk #[0xCC])
  = 0xEEAD6DBFC7340A56CAEDC044696A168870549A6A7F6F56961E84A54BD9970B8A#256

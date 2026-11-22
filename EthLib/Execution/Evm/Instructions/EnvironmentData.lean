module

public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step
public import EthLib.Execution.Fees.BlobBaseFee

/-!
# `Evm.Instructions.EnvironmentData`

The instructions that push a value of the message, the transaction or the block.

Each one pays a fixed price, pushes one word and moves to the next opcode.

The number, gas limit, difficulty, base fee and blob base fee of a block have no upper bound.

No source says what to push when one is `2^256` or more, and EIP-7516 is silent for the blob fee.

So such an instruction aborts the execution, which then has no outcome.

The step comments write `{I_H}_x` for the field `x` of the header of the block.

An address becomes a word through its low 20 bytes, and a hash is read big-endian.

BLOCKHASH and BLOBHASH push 0 for a block or a blob out of their range.

From Paris, the opcode of DIFFICULTY pushes the randomness of the beacon chain instead.

Appendix H.2 of the Yellow Paper, Shanghai version, defines these instructions up to Shanghai.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

The EIPs that add or change an instruction define it:

- [EIP-1344][eip1344], CHAINID
- [EIP-3198][eip3198], BASEFEE
- [EIP-4399][eip4399], PREVRANDAO in place of DIFFICULTY
- [EIP-4844][eip4844], BLOBHASH
- [EIP-7516][eip7516], BLOBBASEFEE
- [EIP-7843][eip7843], SLOTNUM

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip1344]: https://eips.ethereum.org/EIPS/eip-1344#specification
[eip3198]: https://eips.ethereum.org/EIPS/eip-3198#specification
[eip4399]: https://eips.ethereum.org/EIPS/eip-4399#specification
[eip4844]: https://eips.ethereum.org/EIPS/eip-4844#opcode-to-get-versioned-hashes
[eip7516]: https://eips.ethereum.org/EIPS/eip-7516#specification
[eip7843]: https://eips.ethereum.org/EIPS/eip-7843#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork Hash32 U256)
open EthLib.Execution.Fees.BlobBaseFee (blobSchedule getBaseFeePerBlobGas)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The hash of block `n`, for a block of number `current` with the hashes before it.

It is 0 unless the block is one of the 256 blocks before the current one.

The last hash is the parent's, so block `current - k` has the `k`-th hash from the end.

A list too short to hold that hash gives 0 too.

No list is too short inside the window on a chain whose recent blocks are linked.

They must also number at least 255, or the number of the last block when that is fewer. -/
def blockHash (hashes : List Hash32) (current n : Nat) : U256 :=
  if n < current ∧ current ≤ n + 256 then
    match hashes.reverse[current - n - 1]? with
    | some hash => U256.fromBeBytes hash
    | none => 0
  else 0

/-- BLOCKHASH: replace a block number with the hash of that block. -/
def blockhashStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (number, evm) ← popWord evm
  let evm ← chargeGas evm OPCODE_BLOCKHASH
  let block := evm.message.blockEnv
  let evm ← pushWord evm (blockHash block.blockHashes block.number number.toNat)
  return advance evm

/-- The versioned hash at `index` in a list, read as a word, or 0 past the end. -/
def blobHash (hashes : List Hash32) (index : U256) : U256 :=
  match hashes[index.toNat]? with
  | some hash => U256.fromBeBytes hash
  | none => 0

/-- BLOBHASH: replace an index with the versioned hash of that blob of the transaction. -/
def blobhashStep (h : .dencun ≤ fork) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  let (index, evm) ← popWord evm
  let evm ← chargeGas evm OPCODE_BLOBHASH
  let evm ← pushWord evm (blobHash (evm.message.txEnv.blobVersionedHashes h) index)
  return advance evm

/-- The instruction of an opcode that pushes a value of the environment, at fork `fork`.

Other opcodes give none, and so does an opcode before the fork that adds it. -/
def environmentStep (fork : Fork) : Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  -- ADDRESS: `mu'_s[0] = I_a`.
  | .address =>
    some (readFrame OPCODE_ADDRESS fun evm => evm.message.currentTarget.toU256)
  -- ORIGIN: `mu'_s[0] = I_o`.
  | .origin => some (readFrame OPCODE_ORIGIN fun evm => evm.message.txEnv.origin.toU256)
  -- CALLER: `mu'_s[0] = I_s`.
  | .caller => some (readFrame OPCODE_CALLER fun evm => evm.message.caller.toU256)
  -- CALLVALUE: `mu'_s[0] = I_v`.
  | .callvalue => some (readFrame OPCODE_CALLVALUE fun evm => evm.message.value)
  -- GASPRICE: `mu'_s[0] = I_p`, the effective gas price, which the fee fields bound below `2^256`.
  | .gasprice => some (readNumber OPCODE_GASPRICE fun evm => evm.message.txEnv.gasPrice)
  | .blockhash => some blockhashStep
  -- COINBASE: `mu'_s[0] = {I_H}_c`.
  | .coinbase =>
    some (readFrame OPCODE_COINBASE fun evm => evm.message.blockEnv.coinbase.toU256)
  -- TIMESTAMP: `mu'_s[0] = {I_H}_s`, which the header holds below `2^256`.
  | .timestamp => some (readFrame OPCODE_TIMESTAMP fun evm => evm.message.blockEnv.timestamp)
  -- NUMBER: `mu'_s[0] = {I_H}_i`, which has no bound.
  | .number => some (readNumber OPCODE_NUMBER fun evm => evm.message.blockEnv.number)
  | .prevrandao =>
    if h : .paris ≤ fork then
      -- PREVRANDAO: `mu'_s[0] = {I_H}_a`, read big-endian.
      some (readFrame OPCODE_PREVRANDAO fun evm =>
        U256.fromBeBytes (evm.message.blockEnv.prevRandao h))
    else
      -- DIFFICULTY: `mu'_s[0] = {I_H}_d` before Paris, which has no bound.
      some (readNumber OPCODE_PREVRANDAO fun evm => evm.message.blockEnv.difficulty)
  -- GASLIMIT: `mu'_s[0] = {I_H}_l`, which has no bound.
  | .gaslimit => some (readNumber OPCODE_GASLIMIT fun evm => evm.message.blockEnv.gasLimit)
  | .chainid =>
    if .istanbul ≤ fork then
      -- CHAINID: `mu'_s[0] = beta`, which EthLib holds in 64 bits.
      some (readFrame OPCODE_CHAINID fun evm => BitVec.ofNat 256 evm.message.blockEnv.chainId.toNat)
    else none
  | .basefee =>
    if h : .london ≤ fork then
      -- BASEFEE: `mu'_s[0] = {I_H}_f`, which has no bound.
      some (readNumber OPCODE_BASEFEE fun evm => evm.message.blockEnv.baseFeePerGas h)
    else none
  | .blobhash => if h : .dencun ≤ fork then some (blobhashStep h) else none
  | .blobbasefee =>
    if h : .dencun ≤ fork then
      -- BLOBBASEFEE: `get_blob_gasprice(header)` of EIP-7516, which has no bound.
      --
      -- It reaches `2^256` at an excess blob gas of about 177.4457 times the update fraction.
      --
      -- With the mainnet schedule of Dencun, that is an excess of 592398316.
      some (readNumber OPCODE_BLOBBASEFEE fun evm => evm.message.blockEnv.blobBaseFee h)
    else none
  | .slotnum =>
    if h : .glamsterdam ≤ fork then
      -- SLOTNUM: the slot number of EIP-7843, a 64-bit number.
      some (readFrame OPCODE_SLOTNUM fun evm =>
        BitVec.ofNat 256 (evm.message.blockEnv.slotNumber h).toNat)
    else none
  | _ => none

end EthLib.Execution.Evm

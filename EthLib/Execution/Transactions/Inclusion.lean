module

public import EthLib.Execution.Evm.Delegation
public import EthLib.Execution.Transactions.Settlement

/-!
# `Transactions.Inclusion`

The rules that a transaction must pass to enter a block, against the block and the state.

The rules alone need no state, and these rules add what the block and the state decide.

- The gas limit fits in the gas that the block has left.
- From Glamsterdam, the execution gas fits in the execution gas that the block has left.
- From Glamsterdam, the gas limit also fits in the state gas that the block has left.
- From Dencun, the blob gas fits in the blob gas that the block has left.
- From London, the maximum fee per gas covers the base fee of the block.
- From Dencun, the maximum fee per blob gas covers the base fee per blob gas.
- The nonce is the nonce of the sender.
- The sender holds the most that the transaction can cost, with the value it sends.
- The sender has no code, and from Pectra it may have a delegation indicator.

The checks run in the order that decides which error a transaction gets.

Section 6.2 of the Yellow Paper, Shanghai version, states the rules on gas, nonce and balance.

Source: [`Paper.tex` at `efc5f9a`][yp].

The EIPs that add a rule:

- [EIP-1559][eip1559], the base fee
- [EIP-3607][eip3607], the sender without code, at every fork
- [EIP-4844][eip4844], the blob gas and its fee
- [EIP-7702][eip7702], the sender with a delegation indicator
- [EIP-8037][eip8037], the execution gas and the state gas that the block has left

These rules hold up to Glamsterdam, which changes only the rule on the gas of the block.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
[eip3607]: https://eips.ethereum.org/EIPS/eip-3607#specification
[eip4844]: https://eips.ethereum.org/EIPS/eip-4844#execution-layer-validation
[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#transaction-origination
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-validation
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm (BlockEnvironment isValidDelegation)
open EthLib.Execution.Evm.GasCosts (TX_MAX_GAS_LIMIT)
open EthLib.Execution.State (EMPTY_CODE_HASH TransactionState)
open EthLib.Execution.Fees.BlobBaseFee

/-! ## The fees that a transaction offers -/

namespace Transaction

/-- The most wei per blob gas that a transaction pays, or 0 for a transaction without blobs. -/
def maxFeePerBlobGas : Transaction → Nat
  | .blob tx => tx.maxFeePerBlobGas.toNat
  | _ => 0

/-- The most that the gas and the blobs of a transaction can cost, at its maximum fees. -/
def maxGasFee (tx : Transaction) : Nat :=
  tx.gas.toNat * tx.maxFeePerGas + calculateTotalBlobGas tx * tx.maxFeePerBlobGas

end Transaction

/-- The most blob gas of a block at `fork`: the most blobs times the blob gas of one blob.

The most blobs come from the blob schedule of the block.

A block before Dencun has no blobs. -/
def maxBlobGasPerBlock {fork : Fork} (env : BlockEnvironment fork) : Nat :=
  if h : .dencun ≤ fork then GAS_PER_BLOB * (env.blobSchedule h).max else 0

/-- The gas of a transaction that must fit in the execution gas that its block has left, at `fork`.

It is the gas limit, capped from Glamsterdam at `2^24`, the most execution gas of a transaction. -/
def executionCapacity (fork : Fork) (tx : Transaction) : Nat :=
  if fork ≥ .glamsterdam then min TX_MAX_GAS_LIMIT tx.gas.toNat else tx.gas.toNat

/-! ## The rules -/

/-- Why a transaction cannot enter its block. -/
inductive InclusionError where
  /-- The transaction fails a rule that needs no state. -/
  | transaction (error : TransactionError)
  /-- The gas `gas` of the transaction is above the gas `available` that the block has left.

  From Glamsterdam it is either the execution gas or the state gas. -/
  | gasAllowanceExceeded (gas available : Nat)
  /-- The blob gas `blobGas` is above the blob gas `available` that the block has left. -/
  | blobGasLimitExceeded (blobGas available : Nat)
  /-- The most wei per gas `maxFee` is below the base fee `baseFee` of the block. -/
  | insufficientMaxFeePerGas (maxFee baseFee : Nat)
  /-- The most wei per blob gas `maxFee` is below the base fee per blob gas `blobGasPrice`. -/
  | insufficientMaxFeePerBlobGas (maxFee blobGasPrice : Nat)
  /-- The nonce `nonce` is below the nonce `expected` of the sender. -/
  | nonceTooLow (expected nonce : Nat)
  /-- The nonce `nonce` is above the nonce `expected` of the sender. -/
  | nonceTooHigh (expected nonce : Nat)
  /-- The balance `balance` of the sender is below the most `cost` that the transaction costs. -/
  | insufficientBalance (balance cost : Nat)
  /-- The sender has code, and that code is not a delegation indicator that the fork allows. -/
  | senderNotEoa
  /-- The state does not hold the code of the sender, whose hash is `codeHash`. -/
  | missingCode (codeHash : Hash32)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

A rule that needs no state keeps the code of its error.

The other codes start at 201, above every code of a transaction error and of its network form.

A new constructor takes a new code, so that each code keeps its meaning. -/
def InclusionError.code : InclusionError → UInt32
  | .transaction error => error.code
  | .gasAllowanceExceeded .. => 201
  | .blobGasLimitExceeded .. => 202
  | .insufficientMaxFeePerGas .. => 203
  | .insufficientMaxFeePerBlobGas .. => 204
  | .nonceTooLow .. => 205
  | .nonceTooHigh .. => 206
  | .insufficientBalance .. => 207
  | .senderNotEoa => 208
  | .missingCode _ => 209

/-- What a transaction that may enter its block brings to its run. -/
structure Included where
  /-- The sender that the signature names. -/
  sender : Address
  /-- The intrinsic gas of the transaction. -/
  intrinsicGas : Nat
  /-- The price per gas that the sender pays. -/
  gasPrice : Nat
  /-- The blob gas of the transaction. -/
  blobGasUsed : Nat
  deriving DecidableEq, Repr

/-- Fail with `error` when `condition` holds. -/
def failIf (condition : Bool) (error : InclusionError) : Except InclusionError Unit :=
  if condition then .error error else .ok ()

/-- Check that a transaction may enter its block at `fork`, on the chain `chainId`.

The block has used the gas `used` before it, and `state` is the state.

The chain and the sender come first, then the rules that need no state.

Then come the rules of the block, and last those of the sender. -/
def checkInclusion {fork : Fork} (chainId : UInt64) (env : BlockEnvironment fork)
    (used : BlockGas) (state : TransactionState) (tx : Transaction) :
    Except InclusionError Included := do
  (checkChainId fork chainId tx).mapError .transaction
  let sender ← (recoverSender fork tx).mapError .transaction
  let intrinsic ← (validateTransaction fork sender tx).mapError .transaction
  let available := env.gasLimit - used.execution
  let gas := executionCapacity fork tx
  failIf (available < gas) (.gasAllowanceExceeded gas available)
  let stateAvailable := env.gasLimit - used.state
  failIf (fork ≥ .glamsterdam ∧ stateAvailable < tx.gas.toNat)
    (.gasAllowanceExceeded tx.gas.toNat stateAvailable)
  let blobGas := calculateTotalBlobGas tx
  let blobAvailable := maxBlobGasPerBlock env - used.blob
  failIf (blobAvailable < blobGas) (.blobGasLimitExceeded blobGas blobAvailable)
  let baseFee := baseFeeOf env
  failIf (tx.maxFeePerGas < baseFee) (.insufficientMaxFeePerGas tx.maxFeePerGas baseFee)
  (checkContents fork tx).mapError .transaction
  let blobGasPrice := blobGasPriceOf env
  failIf (0 < blobGas ∧ tx.maxFeePerBlobGas < blobGasPrice)
    (.insufficientMaxFeePerBlobGas tx.maxFeePerBlobGas blobGasPrice)
  let account := state.getAccount sender
  failIf (tx.nonce.toNat < account.nonce) (.nonceTooLow account.nonce tx.nonce.toNat)
  failIf (account.nonce < tx.nonce.toNat) (.nonceTooHigh account.nonce tx.nonce.toNat)
  let cost := tx.maxGasFee + tx.value.toNat
  failIf (account.balance.toNat < cost) (.insufficientBalance account.balance.toNat cost)
  let code ← (state.getCode account.codeHash).mapError fun _ => .missingCode account.codeHash
  failIf (account.codeHash ≠ EMPTY_CODE_HASH ∧ !(fork ≥ .pectra ∧ isValidDelegation code))
    .senderNotEoa
  return ⟨sender, intrinsic, effectiveGasPrice baseFee tx, blobGas⟩

end EthLib.Execution.Transactions

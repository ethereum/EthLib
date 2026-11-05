module

public import EthLib.Execution.Evm.Environment
public import EthLib.Execution.Fees.BlobGas
public import EthLib.Execution.State.Tracker
public import EthLib.Execution.Transactions.Validity

/-!
# `Transactions.Settlement`

What a transaction pays for its gas, before it runs and after.

Before it runs, the sender buys the whole gas limit at the price per gas of the transaction.

From Dencun, the sender also pays the fee of its blobs.

After it runs, a part of the gas used comes back through the refund counter.

The refund is at most half of the gas used, and from London at most a fifth.

From Pectra, the gas used is never below the call data floor.

The sender gets back the gas left at the same price.

The beneficiary of the block gets the gas used times the priority fee per gas.

The base fee per gas of each unit used is burned.

Before London, there is no base fee, so the beneficiary gets the whole price.

Section 6.2 of the Yellow Paper, Berlin version, defines the refund and the payments.

Source: [`Paper.tex` at `beacfbd`][yp-berlin].

The EIPs that change them:

- [EIP-1559][eip1559], the price per gas, the priority fee and the burn
- [EIP-3529][eip3529], the refund of at most a fifth
- [EIP-4844][eip4844], the fee of the blobs
- [EIP-7623][eip7623], the call data floor

These rules hold up to BPO5, which keeps the rules of BPO2.

Glamsterdam changes the gas used of a block and the floor, by EIP-7778 and EIP-7976.

[yp-berlin]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[eip1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
[eip3529]: https://eips.ethereum.org/EIPS/eip-3529#specification
[eip4844]: https://eips.ethereum.org/EIPS/eip-4844#gas-accounting
[eip7623]: https://eips.ethereum.org/EIPS/eip-7623#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm (BlockEnvironment)
open EthLib.Execution.State (StateError TransactionState)
open EthLib.Execution.Fees.BlobBaseFee

/-! ## The prices that the block sets -/

/-- The base fee per gas of a block at `fork`, or 0 before London, which has none. -/
def baseFeeOf {fork : Fork} (env : BlockEnvironment fork) : Nat :=
  if h : .london ≤ fork then env.baseFeePerGas h else 0

/-- The base fee per blob gas of a block at `fork`, or 0 before Dencun, which has no blobs. -/
def blobGasPriceOf {fork : Fork} (env : BlockEnvironment fork) : Nat :=
  if h : .dencun ≤ fork then
    getBaseFeePerBlobGas (blobSchedule fork h) (env.excessBlobGas h).toNat
  else 0

/-! ## The price per gas -/

/-- The most wei per gas that a transaction pays: its gas price, or its maximum fee. -/
def Transaction.maxFeePerGas : Transaction → Nat
  | .legacy tx => tx.gasPrice.toNat
  | .accessList tx => tx.gasPrice.toNat
  | .feeMarket tx => tx.maxFeePerGas.toNat
  | .blob tx => tx.maxFeePerGas.toNat
  | .setCode tx => tx.maxFeePerGas.toNat

/-- The price per gas that a transaction pays, at a base fee per gas of `baseFee`.

A transaction with a gas price pays that price.

A transaction with a maximum fee pays the base fee plus its priority fee.

That priority fee is capped, so that the price stays within a maximum fee that covers the base fee.

A maximum fee below the base fee gives the base fee, and the checks of the block reject it.

[EIP-1559](https://eips.ethereum.org/EIPS/eip-1559#specification) defines it. -/
def effectiveGasPrice (baseFee : Nat) : Transaction → Nat
  | .legacy tx => tx.gasPrice.toNat
  | .accessList tx => tx.gasPrice.toNat
  | .feeMarket tx => feeMarket tx.maxPriorityFeePerGas.toNat tx.maxFeePerGas.toNat
  | .blob tx => feeMarket tx.maxPriorityFeePerGas.toNat tx.maxFeePerGas.toNat
  | .setCode tx => feeMarket tx.maxPriorityFeePerGas.toNat tx.maxFeePerGas.toNat
where
  /-- The base fee plus the priority fee, capped so that the sum stays within the maximum fee. -/
  feeMarket (maxPriorityFee maxFee : Nat) : Nat :=
    min maxPriorityFee (maxFee - baseFee) + baseFee

/-! ## The gas used -/

/-- The quotient that caps the refund: 2, and 5 from London.

[EIP-3529](https://eips.ethereum.org/EIPS/eip-3529#specification) raises it. -/
def maxRefundQuotient (fork : Fork) : Nat :=
  if fork ≥ .london then 5 else 2

/-- The gas that comes back from the refund counter, for `used` gas used before the refund.

It is the counter, at most the gas used divided by the quotient of the fork. -/
def gasRefund (fork : Fork) (used refundCounter : Nat) : Nat :=
  min (used / maxRefundQuotient fork) refundCounter

/-- The gas that a transaction uses at `fork`, from the gas left and the refund counter.

It is the gas limit minus the gas left, minus the refund.

From Pectra, it is at least the call data floor. -/
def gasUsed (fork : Fork) (tx : Transaction) (gasLeft refundCounter : Nat) : Nat :=
  let used := tx.gas.toNat - gasLeft
  let afterRefund := used - gasRefund fork used refundCounter
  if fork ≥ .pectra then max afterRefund (calldataFloor tx.data) else afterRefund

/-! ## The payments -/

/-- Where the wei of the gas limit of a transaction go, once it has run. -/
structure Settlement where
  /-- The gas that the transaction used. -/
  gasUsed : Nat
  /-- The wei that the sender gets back, for the gas that it did not use. -/
  senderRefund : Nat
  /-- The wei that the beneficiary of the block gets, for the priority fee. -/
  priorityFee : Nat
  /-- The wei that are burned, for the base fee. -/
  burned : Nat
  deriving DecidableEq, Repr

/-- Where the wei of a transaction go at `fork` and at a base fee per gas of `baseFee`. -/
def settlement (fork : Fork) (baseFee : Nat) (tx : Transaction) (gasLeft refundCounter : Nat) :
    Settlement :=
  let used := gasUsed fork tx gasLeft refundCounter
  let price := effectiveGasPrice baseFee tx
  { gasUsed := used
    senderRefund := (tx.gas.toNat - used) * price
    priorityFee := used * (price - baseFee)
    burned := used * baseFee }

/-! ## The changes to the state -/

/-- Add `amount` wei to the balance of an address, which must stay below 2^256. -/
def creditEther (fork : Fork) (state : TransactionState) (address : Address) (amount : Nat) :
    Except StateError TransactionState :=
  if amount < 2 ^ 256 then state.createEther fork address (BitVec.ofNat 256 amount)
  else .error (.balanceOverflow address)

/-- Buy the gas of a transaction at `fork`: add one to the nonce of the sender, and take the fee.

The fee is the gas limit times the price per gas, plus the fee of the blobs.

It fails if the sender does not hold the fee.

This is only the deduction: the checks of the block ask for the balance at the maximum fees. -/
def buyGas {fork : Fork} (env : BlockEnvironment fork) (state : TransactionState)
    (sender : Address) (tx : Transaction) : Except StateError TransactionState := do
  let fee := tx.gas.toNat * effectiveGasPrice (baseFeeOf env) tx +
    calculateTotalBlobGas tx * blobGasPriceOf env
  let state ← state.incrementNonce fork sender
  state.modifyState fork sender fun account =>
    if fee ≤ account.balance.toNat then
      .ok { account with balance := BitVec.ofNat 256 (account.balance.toNat - fee) }
    else .error (.insufficientBalance sender)

/-- Pay the priority fee `fee` to the beneficiary `coinbase` at `fork`.

From Spurious Dragon to Paris, a fee of 0 to a beneficiary with balance 0 creates no account.

That fee still touches the beneficiary, so an empty beneficiary is deleted.

[EIP-161](https://eips.ethereum.org/EIPS/eip-161#specification) gives this example of a touch.

From Paris, a change that leaves an account empty deletes it anyway. -/
def payBeneficiary (fork : Fork) (state : TransactionState) (coinbase : Address) (fee : Nat) :
    Except StateError TransactionState :=
  if fork ≥ .spuriousDragon ∧ fork < .paris ∧ (state.getAccount coinbase).balance.toNat + fee = 0
  then
    .ok (if state.accountExistsAndIsEmpty coinbase then state.destroyAccount coinbase else state)
  else creditEther fork state coinbase fee

/-- Settle the gas of a transaction at `fork`, once it has run.

The sender gets back its refund, then the beneficiary gets the priority fee.

It returns the state and the gas used. -/
def settleGas {fork : Fork} (env : BlockEnvironment fork) (state : TransactionState)
    (sender : Address) (tx : Transaction) (gasLeft refundCounter : Nat) :
    Except StateError (TransactionState × Nat) := do
  let s := settlement fork (baseFeeOf env) tx gasLeft refundCounter
  let state ← creditEther fork state sender s.senderRefund
  let state ← payBeneficiary fork state env.coinbase s.priorityFee
  return (state, s.gasUsed)

end EthLib.Execution.Transactions

module

public import EthLib.Execution.Evm.Environment
public import EthLib.Execution.Transactions.BlobGas
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

The step comments write the equations of the paper in ASCII.

The prices `p` and `f` and the cap of a fifth are in the [Shanghai version][yp-shanghai].

Only `ethereum/execution-specs` spells out the steps of the later EIPs in one place.

The step comments quote `process_transaction` in [Osaka's `fork.py`][es-osaka].

They quote `process_transaction` in [Amsterdam's `fork.py`][es-amsterdam].

They quote `allocate_evm_gas` and `settle_transaction_gas` in [Amsterdam's `vm/gas.py`][es-gas].

They quote the payment of the beneficiary in [Spurious Dragon's `fork.py`][es-spurious].

The EIPs that change them:

- [EIP-1559][eip1559], the price per gas, the priority fee and the burn
- [EIP-3529][eip3529], the refund of at most a fifth
- [EIP-4844][eip4844], the fee of the blobs
- [EIP-7623][eip7623], the call data floor

From Glamsterdam, the gas past the intrinsic gas splits into execution gas and state gas.

The execution gas and the intrinsic gas together stay within `2^24`.

The rest of the gas fills a reservoir of state gas, which comes back to the sender unused.

A block then counts two kinds of gas: execution gas and state gas.

It counts the execution gas before the refund, and never below the call data floor.

The gas used in the header of the block is the larger of the two counts.

The sender still pays the gas used after the refund, and the receipts count that gas.

The EIPs of Glamsterdam that change them:

- [EIP-7778][eip7778], the gas of a block before the refund
- [EIP-8037][eip8037], the state gas, its reservoir and the two counts of a block

[yp-berlin]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[yp-shanghai]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[es-osaka]: https://github.com/ethereum/execution-specs/blob/391d8a05d5cb182542ac7e7330c858b6ee03f990/src/ethereum/forks/osaka/fork.py
[es-amsterdam]: https://github.com/ethereum/execution-specs/blob/391d8a05d5cb182542ac7e7330c858b6ee03f990/src/ethereum/forks/amsterdam/fork.py
[es-spurious]: https://github.com/ethereum/execution-specs/blob/391d8a05d5cb182542ac7e7330c858b6ee03f990/src/ethereum/forks/spurious_dragon/fork.py
[es-gas]: https://github.com/ethereum/execution-specs/blob/391d8a05d5cb182542ac7e7330c858b6ee03f990/src/ethereum/forks/amsterdam/vm/gas.py
[eip1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
[eip3529]: https://eips.ethereum.org/EIPS/eip-3529#specification
[eip4844]: https://eips.ethereum.org/EIPS/eip-4844#gas-accounting
[eip7623]: https://eips.ethereum.org/EIPS/eip-7623#specification
[eip7778]: https://eips.ethereum.org/EIPS/eip-7778#specification
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#multidimensional-metering-for-state-creation-costs
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm (BlockEnvironment)
open EthLib.Execution.Evm.GasCosts (TX_MAX_GAS_LIMIT)
open EthLib.Execution.State (StateError TransactionState)
open EthLib.Execution.Fees.BlobBaseFee

/-! ## The prices that the block sets -/

/-- The base fee per gas of a block at `fork`, or 0 before London, which has none. -/
def baseFeeOf {fork : Fork} (env : BlockEnvironment fork) : Nat :=
  -- `H_f` from London; before it, a price of 0 gives the beneficiary the whole price.
  if h : .london ≤ fork then env.baseFeePerGas h else 0

/-- The base fee per blob gas of a block at `fork`, or 0 before Dencun, which has no blobs. -/
def blobGasPriceOf {fork : Fork} (env : BlockEnvironment fork) : Nat :=
  if h : .dencun ≤ fork then env.blobBaseFee h else 0

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
  -- `p = T_p` if `T_x = 0 or T_x = 1`.
  | .legacy tx => tx.gasPrice.toNat
  | .accessList tx => tx.gasPrice.toNat
  -- `p = f + H_f` if `T_x = 2`.
  --
  -- Blob and set code transactions, of EIP-4844 and EIP-7702, price like `T_x = 2`.
  | .feeMarket tx => feeMarket tx.maxPriorityFeePerGas.toNat tx.maxFeePerGas.toNat
  | .blob tx => feeMarket tx.maxPriorityFeePerGas.toNat tx.maxFeePerGas.toNat
  | .setCode tx => feeMarket tx.maxPriorityFeePerGas.toNat tx.maxFeePerGas.toNat
where
  /-- The base fee plus the priority fee, capped so that the sum stays within the maximum fee. -/
  feeMarket (maxPriorityFee maxFee : Nat) : Nat :=
    -- `p = f + H_f`, with `f = min(T_f, T_m - H_f)`.
    --
    -- A maximum fee below the base fee makes `T_m - H_f` stop at 0 here.
    min maxPriorityFee (maxFee - baseFee) + baseFee

/-- The base fee per gas at which a transaction pays for its gas, in a block at `fork`.

It is the base fee of the block.

A simulation can lower it to 0 for a transaction with a maximum fee per gas of 0. -/
def paidBaseFee {fork : Fork} (env : BlockEnvironment fork) (tx : Transaction)
    (lifted : LiftedRules := {}) : Nat :=
  if lifted.zeroFee && tx.maxFeePerGas == 0 then 0 else baseFeeOf env

/-! ## The gas of the run -/

/-- The gas that a transaction gives to its first frame. -/
structure GasAllocation where
  /-- The execution gas of the frame. -/
  execution : Nat
  /-- The state gas reservoir of the frame, empty before Glamsterdam. -/
  reservoir : Nat
  deriving DecidableEq, Repr

/-- Split the gas of a transaction past its intrinsic gas `intrinsic`, at `fork`.

Before Glamsterdam, all of it is execution gas.

From Glamsterdam, the execution gas is at most `2^24` minus the intrinsic gas.

The rest of the gas goes to the state gas reservoir.

A simulation can lift that cap, so that all the gas past the intrinsic gas is execution gas.

[EIP-8037][eip8037] defines the split.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-level-gas-accounting-reservoir-model -/
def allocateGas (fork : Fork) (tx : Transaction) (intrinsic : Nat) (lifted : LiftedRules := {}) :
    GasAllocation :=
  -- `evm_gas = tx_gas - Uint(intrinsic.execution)`, the Yellow Paper's `g = T_g - g_0`.
  let evmGas := tx.gas.toNat - intrinsic
  if fork ≥ .glamsterdam then
    -- A simulation can lift the cap of `TX_MAX_GAS_LIMIT`: all of `evm_gas` is execution gas.
    if lifted.gasCap then ⟨evmGas, 0⟩
    else
      -- `execution_gas_budget = GasCosts.TX_MAX_GAS_LIMIT - intrinsic.execution`.
      --
      -- `execution_gas = ExecutionGas(min(execution_gas_budget, evm_gas))`.
      let execution := min (TX_MAX_GAS_LIMIT - intrinsic) evmGas
      -- `state_gas_reservoir = StateGas(evm_gas - execution_gas)`.
      ⟨execution, evmGas - execution⟩
  -- Before Glamsterdam: Osaka's `gas = tx.gas - intrinsic.regular`, with no reservoir.
  else ⟨evmGas, 0⟩

/-! ## The gas used -/

/-- The quotient that caps the refund: 2, and 5 from London.

[EIP-3529](https://eips.ethereum.org/EIPS/eip-3529#specification) raises it. -/
def maxRefundQuotient (fork : Fork) : Nat :=
  if fork ≥ .london then 5 else 2

/-- The gas that comes back from the refund counter, for `used` gas used before the refund.

It is the counter, at most the gas used divided by the quotient of the fork. -/
def gasRefund (fork : Fork) (used refundCounter : Nat) : Nat :=
  -- `min(floor((T_g - g') / 5), A_r)`; before London the divisor is 2 and the counter `A'_r`.
  min (used / maxRefundQuotient fork) refundCounter

/-- The gas that a transaction uses at `fork`, from the gas left and the refund counter.

From Pectra, it is at least the call data floor.

From Glamsterdam, the gas left holds the execution gas left and the state gas reservoir left. -/
def gasUsed (fork : Fork) (sender : Address) (tx : Transaction) (gasLeft refundCounter : Nat) :
    Nat :=
  -- `tx_gas_used_before_refund = tx.gas - tx_output.gas_left`, the Yellow Paper's `T_g - g'`.
  --
  -- From Glamsterdam the gas left also holds `state_gas_left`, which Amsterdam subtracts apart.
  let used := tx.gas.toNat - gasLeft
  -- `tx_gas_used_after_refund = tx_gas_used_before_refund - tx_gas_refund`, so `T_g - g*`.
  let afterRefund := used - gasRefund fork used refundCounter
  -- From Pectra, the floor of EIP-7623 applies.
  --
  -- `tx_gas_used_after_refund = max(tx_gas_used_after_refund, intrinsic.calldata_floor)`.
  if fork ≥ .pectra then max afterRefund (calldataFloor fork sender tx) else afterRefund

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

/-- The priority fee of a transaction that used `used` gas, at the base fee `baseFee`, in wei.

It is the gas used times the price per gas above the base fee. -/
def priorityFeeOf (baseFee used : Nat) (tx : Transaction) : Nat :=
  -- `priority_fee_per_gas = effective_gas_price - block_env.base_fee_per_gas`.
  --
  -- `transaction_fee = tx_gas_used_after_refund * priority_fee_per_gas`.
  --
  -- That is the Shanghai paper's `(T_g - g*) f`.
  used * (effectiveGasPrice baseFee tx - baseFee)

/-- Where the wei of a transaction from `sender` go at `fork` and at a base fee of `baseFee`. -/
def settlement (fork : Fork) (baseFee : Nat) (sender : Address) (tx : Transaction)
    (gasLeft refundCounter : Nat) : Settlement :=
  let used := gasUsed fork sender tx gasLeft refundCounter
  let price := effectiveGasPrice baseFee tx
  { gasUsed := used
    -- `tx_gas_left = tx.gas - tx_gas_used_after_refund`.
    --
    -- `gas_refund_amount = tx_gas_left * effective_gas_price`, the Shanghai paper's `g* p`.
    senderRefund := (tx.gas.toNat - used) * price
    priorityFee := priorityFeeOf baseFee used tx
    -- The base fee of the gas used, which the paper credits to no account.
    burned := used * baseFee }

/-! ## The gas of the block -/

/-- The gas that a block counts, for some of its transactions or for one. -/
structure BlockGas where
  /-- The gas of the transactions, which from Glamsterdam is their execution gas. -/
  execution : Nat
  /-- The state gas of the transactions, 0 before Glamsterdam. -/
  state : Nat
  /-- The blob gas of the transactions. -/
  blob : Nat
  deriving DecidableEq, Repr

namespace BlockGas

/-- The counts of a block before its first transaction. -/
def zero : BlockGas := ⟨0, 0, 0⟩

/-- The counts of two parts of a block together. -/
def add (a b : BlockGas) : BlockGas :=
  ⟨a.execution + b.execution, a.state + b.state, a.blob + b.blob⟩

/-- The counts of some parts of a block together. -/
def sum (parts : List BlockGas) : BlockGas :=
  parts.foldr add zero

/-- The gas used in the header of a block: the larger of the execution gas and the state gas.

Before Glamsterdam the state gas is 0, so it is the gas of the transactions.

[EIP-8037][eip8037] defines it.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#block-level-gas-accounting -/
def gasUsed (counts : BlockGas) : Nat :=
  -- EIP-8037 sets the `gas_used` of the header to the larger count.
  --
  -- `max(block_output.block_execution_gas_used, block_output.block_state_gas_used)`.
  max counts.execution counts.state

end BlockGas

/-- The gas that a transaction from `sender` adds to the counts of its block at `fork`.

The run hands back the gas left `gasLeft`, the refund counter and the net state gas used.

From Glamsterdam the gas left includes the state gas reservoir left.

Before Glamsterdam, the block counts the gas that the transaction uses.

From Glamsterdam, the block counts the state gas used, and a negative amount counts as 0.

It counts as execution gas the gas used before the refund, minus that state gas.

That execution gas is never below the call data floor.

[EIP-7778][eip7778] stops the refund from lowering the gas of a block.

[EIP-8037][eip8037] splits that gas into the two counts.

[eip7778]: https://eips.ethereum.org/EIPS/eip-7778#specification
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#integration-with-eip-7778 -/
def transactionBlockGas (fork : Fork) (sender : Address) (tx : Transaction)
    (gasLeft refundCounter : Nat) (stateGasUsed : Int) : BlockGas :=
  if fork ≥ .glamsterdam then
    -- `settled_state_gas_used = StateGas(Uint(max(0, state_gas_used)))`.
    let state := stateGasUsed.toNat
    -- `max(gas_used_before_refund - settled_state_gas_used, calldata_floor)`.
    --
    -- The gas left here already holds `state_gas_left`, which the source subtracts on its own.
    ⟨max (tx.gas.toNat - gasLeft - state) (calldataFloor fork sender tx), state,
      -- `block_output.blob_gas_used += calculate_total_blob_gas(tx)`.
      calculateTotalBlobGas tx⟩
  -- `block_output.block_gas_used += tx_gas_used_after_refund`, then the blob gas.
  else ⟨gasUsed fork sender tx gasLeft refundCounter, 0, calculateTotalBlobGas tx⟩

/-! ## The changes to the state -/

/-- Add `amount` wei to the balance of an address, which must stay below 2^256. -/
def creditEther (fork : Fork) (state : TransactionState) (address : Address) (amount : Nat) :
    Except StateError TransactionState :=
  if amount < 2 ^ 256 then state.createEther fork address (BitVec.ofNat 256 amount)
  else .error (.balanceOverflow address)

/-- Buy the gas of a transaction at `fork`: add one to the nonce of the sender, and take the fee.

The fee is the gas limit times the price per gas, plus the fee of the blobs.

It fails if the sender does not hold the fee.

This is only the deduction: the checks of the block ask for the balance at the maximum fees.

A simulation can charge a transaction with a maximum fee per gas of 0 at a base fee of 0. -/
def buyGas {fork : Fork} (env : BlockEnvironment fork) (state : TransactionState)
    (sender : Address) (tx : Transaction) (lifted : LiftedRules := {}) :
    Except StateError TransactionState := do
  -- `effective_gas_fee = tx.gas * effective_gas_price`, plus `blob_gas_fee`.
  --
  -- `blob_gas_fee = calculate_data_fee(block_env.excess_blob_gas, tx)`, 0 without blobs.
  --
  -- A simulation can charge a maximum fee per gas of 0 at a base fee of 0.
  let fee := tx.gas.toNat * effectiveGasPrice (paidBaseFee env tx lifted) tx +
    calculateTotalBlobGas tx * blobGasPriceOf env
  -- `increment_nonce(tx_state, sender)`.
  let state ← state.incrementNonce fork sender
  -- `Uint(sender_account.balance) - effective_gas_fee - blob_gas_fee`, the balance after the fee.
  --
  -- The checks of the block make this hold; a short balance is an error here.
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
  -- From Spurious Dragon to Paris: `if coinbase_balance_after_mining_fee != 0` credits the fee.
  --
  -- `elif account_exists_and_is_empty(tx_state, block_env.coinbase)`, the account is destroyed.
  --
  -- Otherwise, `create_ether(tx_state, block_env.coinbase, U256(transaction_fee))`.
  if fork ≥ .spuriousDragon ∧ fork < .paris ∧ (state.getAccount coinbase).balance.toNat + fee = 0
  then
    .ok (if state.accountExistsAndIsEmpty coinbase then state.destroyAccount coinbase else state)
  else creditEther fork state coinbase fee

/-- Settle the gas of a transaction at `fork`, once it has run.

The sender gets back its refund, then the beneficiary gets the priority fee.

From Glamsterdam the gas left includes the state gas reservoir left, so the sender gets it back.

A simulation can charge a transaction with a maximum fee per gas of 0 at a base fee of 0.

It returns the state and the gas used. -/
def settleGas {fork : Fork} (env : BlockEnvironment fork) (state : TransactionState)
    (sender : Address) (tx : Transaction) (gasLeft refundCounter : Nat)
    (lifted : LiftedRules := {}) : Except StateError (TransactionState × Nat) := do
  -- A simulation can charge a maximum fee per gas of 0 at a base fee of 0.
  let s := settlement fork (paidBaseFee env tx lifted) sender tx gasLeft refundCounter
  -- `create_ether(tx_state, sender, U256(gas_refund_amount))`.
  let state ← creditEther fork state sender s.senderRefund
  -- `create_ether(tx_state, block_env.coinbase, U256(transaction_fee))`.
  let state ← payBeneficiary fork state env.coinbase s.priorityFee
  return (state, s.gasUsed)

end EthLib.Execution.Transactions

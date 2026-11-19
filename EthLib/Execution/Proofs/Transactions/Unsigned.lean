module

public import EthLib.Execution.Transactions.Process

/-!
# Proofs: a transaction without its signature

A simulation runs each call as a transaction with a signature of 0, and gives its sender.

With the sender given, the check of a transaction does not read its signature.

Nor does its run, so a signed transaction runs as its form without a signature.

A simulation lifts the cap at `2^32 - 1` on the gas limit from Glamsterdam.

That changes nothing below the cap.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)

/-- Dropping the signature keeps the type. -/
theorem Transaction.type_unsigned (tx : Transaction) : tx.unsigned.type = tx.type := by
  cases tx <;> rfl

/-- With the sender given, the check of a transaction does not read its signature. -/
theorem checkInclusion_unsigned {fork : Fork} (chainId : UInt64) (env : BlockEnvironment fork)
    (used : BlockGas) (state : TransactionState) (tx : Transaction) (sender : Address)
    (lifted : LiftedRules) :
    checkInclusion chainId env used state tx.unsigned (some sender) lifted =
      checkInclusion chainId env used state tx (some sender) lifted := by
  cases tx <;> rfl

/-- The run of a transaction does not read its signature. -/
theorem processTransaction_unsigned {fork : Fork} (env : BlockEnvironment fork)
    (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) :
    processTransaction env block included tx.unsigned precompiles lifted =
      processTransaction env block included tx precompiles lifted := by
  cases tx <;> rfl

/-- Below the cap at `2^32 - 1`, lifting it leaves the validity rules unchanged. -/
private theorem validateTransaction_totalGasCap {fork : Fork} {sender : Address} {tx : Transaction}
    (h : tx.gas.toNat ≤ GasCosts.TX_MAX_TOTAL_GAS_LIMIT) :
    validateTransaction fork sender tx { totalGasCap := true } =
      validateTransaction fork sender tx := by
  simp only [validateTransaction, h, ensure]
  rfl

/-- Below the cap at `2^32 - 1`, lifting it leaves the check of a transaction unchanged. -/
theorem checkInclusion_totalGasCap {fork : Fork} {chainId : UInt64} {env : BlockEnvironment fork}
    {used : BlockGas} {state : TransactionState} {tx : Transaction} {known : Option Address}
    (h : tx.gas.toNat ≤ GasCosts.TX_MAX_TOTAL_GAS_LIMIT) :
    checkInclusion chainId env used state tx known { totalGasCap := true } =
      checkInclusion chainId env used state tx known := by
  simp only [checkInclusion, validateTransaction_totalGasCap h]
  rfl

/-- Lifting the cap at `2^32 - 1` leaves the run of a transaction unchanged. -/
theorem processTransaction_totalGasCap {fork : Fork} (env : BlockEnvironment fork)
    (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) :
    processTransaction env block included tx precompiles { totalGasCap := true } =
      processTransaction env block included tx precompiles := by
  rfl

end EthLib.Execution.Transactions

module

public import EthLib.Execution.Proofs.Transactions.Inclusion
public import EthLib.Execution.Evm.Call.MessageCall

/-!
# Proofs: what the simulation overrides change

By default, a call runs the precompile at the address of its code.

A known sender that the signature names changes the check only by skipping the rule on its code.

That rule says the sender has no code, or from Pectra only a delegation indicator.

So a sender that the signature names, and that passes that rule, gives the same check.

Without a price that a simulation sets, the excess blob gas gives the base fee per blob gas.

Without the gas caps lifted, the gas of a transaction keeps the caps of Glamsterdam.

With the nonce check skipped, a sender at the nonce limit still fails.

Lifting them makes all the gas past the intrinsic gas execution gas.

Unless a simulation lowers its base fee, a transaction pays at the base fee of its block.

Once it does, a transaction with a fee cap of 0 pays at a base fee of 0.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (TransactionState)

/-- With the default map, a message calls the precompile at the address of its code, if any. -/
theorem precompileAddress_of_default {fork : Fork} {message : Message fork}
    (h : message.txEnv.precompiles = some) :
    precompileAddress fork message =
      message.codeAddress.bind fun address =>
        if Precompiles.isPrecompile fork address.toU256.toNat then some address.toU256.toNat
        else none := by
  unfold precompileAddress
  rw [h]
  cases message.codeAddress <;> rfl

/-- For a sender that passes the rule on its code, the check gives the same result signed or not.
-/
theorem checkSender_unsigned {fork : Fork} {state : TransactionState} {sender : Address}
    {tx : Transaction}
    (hCode : ∃ code, state.getCode (state.getAccount sender).codeHash = .ok code ∧
      ((state.getAccount sender).codeHash = State.EMPTY_CODE_HASH ∨
        (fork ≥ .pectra ∧ Evm.isValidDelegation code = true))) :
    checkSender fork state sender tx false = checkSender fork state sender tx := by
  obtain ⟨code, hc, hr⟩ := hCode
  have hRule : (do
      let code ← (state.getCode (state.getAccount sender).codeHash).mapError fun _ =>
        InclusionError.missingCode (state.getAccount sender).codeHash
      failIf (decide ((state.getAccount sender).codeHash ≠ State.EMPTY_CODE_HASH ∧
        !(fork ≥ .pectra ∧ isValidDelegation code))) .senderNotEoa) =
      (pure () : Except InclusionError Unit) := by
    rw [hc]
    rcases hr with hr | ⟨hp, hd⟩
    · simp [Except.mapError, failIf, hr]; rfl
    · simp [Except.mapError, failIf, hp, hd, bind, Except.bind]; rfl
  simp only [checkSender, Bool.false_eq_true, ↓reduceIte, hRule]

/-- The check of a transaction gives the same result with its sender given or recovered.

The signature must name that sender and the chain, and the sender must pass the rule on its code.
-/
theorem checkInclusion_of_knownSender {fork : Fork} {chainId : UInt64}
    {env : BlockEnvironment fork} {used : BlockGas} {state : TransactionState}
    {tx : Transaction} {sender : Address} (hChain : checkChainId fork chainId tx = .ok ())
    (hSender : recoverSender fork tx = .ok sender)
    (hCode : ∃ code, state.getCode (state.getAccount sender).codeHash = .ok code ∧
      ((state.getAccount sender).codeHash = State.EMPTY_CODE_HASH ∨
        (fork ≥ .pectra ∧ Evm.isValidDelegation code = true))) :
    checkInclusion chainId env used state tx (some sender) =
      checkInclusion chainId env used state tx := by
  unfold checkInclusion
  by_cases hg : fork ≥ .glamsterdam <;>
    simp [hg, bind, Except.bind, pure, Except.pure, hChain, hSender, Except.mapError,
      checkSender_unsigned hCode]

/-- Without a price that a simulation sets, the excess blob gas gives the base fee per blob gas. -/
theorem blobBaseFee_of_none {fork : Fork} {env : BlockEnvironment fork} (hd : .dencun ≤ fork)
    (h : env.blobGasPrice = none) :
    env.blobBaseFee hd =
      Fees.BlobBaseFee.getBaseFeePerBlobGas (env.blobSchedule hd) (env.excessBlobGas hd).toNat := by
  simp [BlockEnvironment.blobBaseFee, h]

/-- Without the gas caps lifted, the gas that must fit in the block is capped from Glamsterdam. -/
theorem executionCapacity_default (fork : Fork) (tx : Transaction) {lifted : LiftedRules}
    (h : lifted.gasCap = false) :
    executionCapacity fork tx lifted =
      if fork ≥ .glamsterdam then min GasCosts.TX_MAX_GAS_LIMIT tx.gas.toNat else tx.gas.toNat := by
  simp [executionCapacity, h]

/-- With the cap lifted, the whole gas limit must fit in the block. -/
theorem executionCapacity_of_gasCap (fork : Fork) (tx : Transaction) {lifted : LiftedRules}
    (h : lifted.gasCap = true) : executionCapacity fork tx lifted = tx.gas.toNat := by
  simp [executionCapacity, h]

/-- Without the gas caps lifted, the execution gas is capped from Glamsterdam. -/
theorem allocateGas_default (fork : Fork) (tx : Transaction) (intrinsic : Nat)
    {lifted : LiftedRules} (h : lifted.gasCap = false) :
    allocateGas fork tx intrinsic lifted =
      if fork ≥ .glamsterdam then
        let execution := min (GasCosts.TX_MAX_GAS_LIMIT - intrinsic) (tx.gas.toNat - intrinsic)
        ⟨execution, tx.gas.toNat - intrinsic - execution⟩
      else ⟨tx.gas.toNat - intrinsic, 0⟩ := by
  simp [allocateGas, h]

/-- With the cap lifted, all the gas past the intrinsic gas is execution gas. -/
theorem allocateGas_of_gasCap (fork : Fork) (tx : Transaction) (intrinsic : Nat)
    {lifted : LiftedRules} (h : lifted.gasCap = true) :
    allocateGas fork tx intrinsic lifted = ⟨tx.gas.toNat - intrinsic, 0⟩ := by
  simp [allocateGas, h]

/-- Unless a simulation lowers its base fee, a transaction pays at the base fee of its block. -/
theorem paidBaseFee_default {fork : Fork} (env : BlockEnvironment fork) (tx : Transaction)
    {lifted : LiftedRules} (h : lifted.zeroFee = false) :
    paidBaseFee env tx lifted = baseFeeOf env := by
  simp [paidBaseFee, h]

/-- Once a simulation lowers it, a transaction with a fee cap of 0 pays at a base fee of 0. -/
theorem paidBaseFee_of_zeroFee {fork : Fork} (env : BlockEnvironment fork) {tx : Transaction}
    {lifted : LiftedRules} (h : lifted.zeroFee = true) (hFee : tx.maxFeePerGas = 0) :
    paidBaseFee env tx lifted = 0 := by
  simp [paidBaseFee, h, hFee]

/-- With the nonce check skipped, a sender at the nonce limit of EIP-2681 still fails. -/
theorem checkSender_of_skipNonce {fork : Fork} {state : TransactionState} {sender : Address}
    {tx : Transaction} {signed : Bool} (h : (state.getAccount sender).nonce = 2 ^ 64 - 1) :
    checkSender fork state sender tx signed true = .error (.transaction .nonceOverflow) := by
  simp [checkSender, h, failIf, bind, Except.bind]

end EthLib.Execution.Transactions

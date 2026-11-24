module

public import EthLib.Execution.Proofs.Transactions.Inclusion
public import EthLib.Execution.Evm.Call.MessageCall

/-!
# Proofs: what the simulation overrides change

What the checks and the run of a transaction give with each override of a simulation, and without.
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
    -- The rule on its code: the sender has no code, or from Pectra only a delegation indicator.
    (hCode : ∃ code, state.getCode (state.getAccount sender).codeHash = .ok code ∧
      ((state.getAccount sender).codeHash = State.EMPTY_CODE_HASH ∨
        (fork ≥ .pectra ∧ Evm.isValidDelegation code = true))) :
    checkSender fork state sender tx false = checkSender fork state sender tx := by
  obtain ⟨code, hc, hr⟩ := hCode
  have hRule : (do
      let code ← (state.getCode (state.getAccount sender).codeHash).mapError fun _ =>
        InclusionError.missingCode (state.getAccount sender).codeHash
      failIf (decide ((state.getAccount sender).codeHash ≠ State.EMPTY_CODE_HASH ∧
        !(fork ≥ .pectra ∧ isValidDelegation code))) (.senderNotEoa sender)) =
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
    -- The rule on its code: the sender has no code, or from Pectra only a delegation indicator.
    (hCode : ∃ code, state.getCode (state.getAccount sender).codeHash = .ok code ∧
      ((state.getAccount sender).codeHash = State.EMPTY_CODE_HASH ∨
        (fork ≥ .pectra ∧ Evm.isValidDelegation code = true))) :
    checkInclusion chainId env used state tx (some sender) =
      checkInclusion chainId env used state tx := by
  -- A known sender changes the check only by skipping the rule on its code.
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
    checkSender fork state sender tx signed true =
      .error (.transaction (.nonceOverflow (2 ^ 64 - 1))) := by
  simp [checkSender, h, failIf, bind, Except.bind]

/-- With the sender given, the checks of the sender never reject it for its code. -/
private theorem checkSender_unsigned_ne_senderNotEoa {fork : Fork} {state : TransactionState}
    {sender : Address} {tx : Transaction} {skipNonce : Bool} (address : Address) :
    checkSender fork state sender tx false skipNonce ≠ .error (.senderNotEoa address) := by
  unfold checkSender
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
  repeat' split
  all_goals first
    | (rename_i h; unfold failIf at h; split at h <;> cases h <;> simp; done)
    | (unfold failIf; split <;> simp [pure, Except.pure]; done)
    | simp_all [pure, Except.pure]

/-- The check of the gas a transaction takes from its block never rejects a sender for its code.
-/
private theorem checkBlockGas_ne_senderNotEoa {fork : Fork} {env : BlockEnvironment fork}
    {used : BlockGas} {tx : Transaction} {lifted : LiftedRules} (address : Address) :
    checkBlockGas env used tx lifted ≠ .error (.senderNotEoa address) := by
  unfold checkBlockGas
  simp only [bind, Except.bind]
  repeat' split
  all_goals first
    | (rename_i h; unfold failIf at h; split at h <;> cases h <;> simp; done)
    | (unfold failIf; split <;> simp; done)
    | simp_all

/-- With the sender given, as a simulation gives it, no check rejects the sender for its code.

The rule on the code of the sender reads a recovered sender only. -/
theorem checkInclusion_ne_senderNotEoa {fork : Fork} {chainId : UInt64}
    {env : BlockEnvironment fork} {used : BlockGas} {state : TransactionState} {tx : Transaction}
    {sender : Address} {lifted : LiftedRules} (address : Address) :
    checkInclusion chainId env used state tx (some sender) lifted ≠
      .error (.senderNotEoa address) := by
  unfold checkInclusion
  simp only [bind, Except.bind, pure, Except.pure, Option.isNone_some]
  repeat' split
  all_goals first
    | (rename_i h; obtain ⟨_, -, rfl⟩ := EthLib.Base.mapError_eq_error h; nofun)
    | (rename_i h; rintro ⟨⟩; exact checkBlockGas_ne_senderNotEoa address h)
    | (rename_i h; rintro ⟨⟩; exact checkSender_unsigned_ne_senderNotEoa address h)
    | (rename_i h; unfold failIf at h; split at h <;> cases h <;> simp; done)
    | (unfold failIf; split <;> simp [pure, Except.pure]; done)
    | (rename_i h; split at h
       · cases h
       · obtain ⟨_, -, rfl⟩ := EthLib.Base.mapError_eq_error h; nofun)
    | simp_all

end EthLib.Execution.Transactions

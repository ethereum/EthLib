module

public import EthLib.Execution.Proofs.Transactions.Inclusion
public import EthLib.Execution.Evm.Call.MessageCall

/-!
# Proofs: simulation overrides that change nothing

By default, a call runs the precompile at the address of its code.

A known sender that the signature names changes the check only by skipping the rule on its code.

That rule says the sender has no code, or from Pectra only a delegation indicator.

So a sender that the signature names, and that passes that rule, gives the same check.
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

end EthLib.Execution.Transactions

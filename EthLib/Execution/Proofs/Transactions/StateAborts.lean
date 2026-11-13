module

public import EthLib.Execution.Proofs.Evm.Call.StateAborts
public import EthLib.Execution.Proofs.Transactions.NoncesFit
import EthLib.Execution.Proofs.Evm.Call.ContractAddress

/-!
# Proofs: a transaction aborts only with an error of the state

A transaction that creates encodes its sender and nonce to find the address of the new account.

The inclusion check keeps that nonce below `2^64 - 1`, so the encoding succeeds.

Let every nonce of its block be at most `2^64 - 1`.

Its message then aborts only with an error of the state.

From Hegotá on, a transaction aborts because its fork is not yet specified.

So before Hegotá, such a transaction aborts only with an error of the state.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base (Fork)
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)

variable {fork : Fork}

/-! ## Errors that abort only as errors of the state -/

/-- The error aborts only as an error of the state. -/
private def Calm (e : EvmError) : Prop :=
  e.aborts = true → ∃ error, e = .state error

section Meter

variable {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-- The charge of an authorization fails only with a calm error. -/
private theorem calm_chargeAuthorization {done : Delegations Meter} {authority : Base.Address}
    {auth : Authorization} {e : EvmError} (h : chargeAuthorization done authority auth = .error e) :
    Calm e := by
  unfold chargeAuthorization at h
  dsimp only at h
  repeat' first
    | (rcases Base.bind_eq_error h with h | ⟨_, -, h⟩)
    | split at h
  all_goals first
    | cases h
    | (rw [LawfulGasMeter.charge_error h]; nofun)
    | (rw [LawfulGasMeter.chargeState_error h]; nofun)
    | exact fun _ => mapError_state_eq_error h

/-- One authorization fails only with a calm error. -/
private theorem calm_applyAuthorization {chainId : Nat} {done : Delegations Meter}
    {auth : Authorization} {e : EvmError} {read : TransactionState}
    (h : applyAuthorization fork chainId done auth = .error (e, read)) : Calm e := by
  unfold applyAuthorization at h
  dsimp only at h
  repeat' first
    | (rcases Base.bind_eq_error h with h | ⟨_, -, h⟩)
    | split at h
  all_goals first
    | cases h
    | (obtain ⟨e', he', hee⟩ := Base.mapError_eq_error h
       simp only [Function.comp_apply, Prod.mk.injEq] at hee
       first
         | exact fun _ => ⟨e', hee.1.symm⟩
         | (rw [← hee.1]
            unfold payAuthorization at he'
            split at he'
            · rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
              · exact calm_chargeAuthorization he'
              · cases he'
            · cases he'))

/-- A list of authorizations fails only with a calm error. -/
private theorem calm_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start : Delegations Meter} {e : EvmError}
      {read : TransactionState},
      auths.foldlM (applyAuthorization fork chainId) start = .error (e, read) → Calm e
  | [], _, _, _, h => by cases h
  | _ :: _, _, _, _, h => by
    rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact calm_applyAuthorization h
    · exact calm_foldlM_applyAuthorization h

/-- The first frame of a message fails only with a calm error. -/
private theorem calm_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Base.Address} {e : EvmError} {read : TransactionState}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .error (e, read)) : Calm e := by
  unfold prepareFirstFrame at h
  split at h <;> dsimp only at h <;>
  repeat' first
    | (rcases Base.bind_eq_error h with h | ⟨_, -, h⟩)
    | split at h
  all_goals first
    | (cases h; done)
    | (cases h; nofun)
    | exact calm_foldlM_applyAuthorization h
    | (obtain ⟨e', he', hee⟩ := Base.mapError_eq_error h
       simp only [Prod.mk.injEq] at hee
       rw [← hee.1]
       first
         | exact fun _ => ⟨e', rfl⟩
         | (rw [LawfulGasMeter.charge_error he']; nofun)
         | (rw [LawfulGasMeter.chargeState_error he']; nofun))

/-! ## The message and the run of a transaction -/

/-- A transaction message from a state whose nonces fit fails only with an error of the state. -/
theorem processMessageCall_eq_error {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Base.Address} {e : EvmError} (hfit : state.NoncesFit)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .error e) :
    ∃ error, e = .state error := by
  unfold processMessageCall at h
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e', read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · rename_i aborts
      cases h
      exact calm_prepareFirstFrame hprep aborts
    · cases h
  · rw [hprep] at h
    dsimp only at h
    have fit := noncesFit_prepareFirstFrame hprep hfit
    split at h
    · rename_i hnone
      rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · refine processCreateMessage_eq_error fit ?_ h
        rw [prepareFirstFrame_create_nonce hprep hnone]
        decide
      · cases h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact processMessage_eq_error fit h
      · cases h

/-- A run of a transaction on a block whose nonces fit fails only with an error of the state.

The sender must start with a nonce below `2^64 - 1`. -/
private theorem runTransaction_eq_error {env : BlockEnvironment fork} {block : BlockState}
    {included : Included} {tx : Transaction} {e : EvmError}
    (hfit : (TransactionState.ofBlock block).NoncesFit)
    (hsender : ((TransactionState.ofBlock block).getAccount included.sender).nonce < MAX_NONCE)
    (h : runTransaction Meter env block included tx = .error e) : ∃ error, e = .state error := by
  unfold runTransaction at h
  rcases Base.bind_eq_error h with h | ⟨target, -, h⟩
  · unfold messageTarget at h
    split at h
    · cases h
    · obtain ⟨address, ha⟩ := createAddress_ok included.sender
        (Nat.lt_trans hsender (by decide))
      rw [ha] at h
      cases h
  rcases Base.bind_eq_error h with h | ⟨bought, hBought, h⟩
  · exact mapError_state_eq_error h
  have hbought := Base.mapError_ok_iff.mp hBought
  have fitBought : bought.NoncesFit := by
    intro address
    by_cases hs : address = included.sender
    · subst hs
      rw [(buyGas_sender rfl hbought).2.2]
      omega
    · unfold State.TransactionState.getAccount
      rw [(sameOutside_buyGas hbought address (by simpa using hs)).1]
      exact hfit address
  dsimp only at h
  rcases Base.bind_eq_error h with h | ⟨message, -, h⟩
  · unfold transactionMessage at h
    split at h
    · dsimp only at h
      generalize hx : Except.mapError EvmError.state _ = x at h
      cases x with
      | error e' => cases h; exact mapError_state_eq_error hx
      | ok _ => cases h
    · cases h
  rcases Base.bind_eq_error h with h | ⟨output, -, h⟩
  · exact processMessageCall_eq_error fitBought h
  rcases Base.bind_eq_error h with h | ⟨⟨settled, used⟩, -, h⟩
  · exact mapError_state_eq_error h
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · exact mapError_state_eq_error h
  · cases h

end Meter

/-- A transaction that passes its inclusion check fails only with an error of the state.

The fork must be before Hegotá, and every nonce of the block must fit. -/
theorem processTransaction_eq_error {env : BlockEnvironment fork} {block : BlockState}
    {chainId : UInt64} {used : BlockGas} {included : Included} {tx : Transaction}
    {e : EvmError} (before : fork < .hegota)
    (hfit : (TransactionState.ofBlock block).NoncesFit)
    (hcheck : checkInclusion chainId env used (.ofBlock block) tx = .ok included)
    (h : processTransaction env block included tx = .error e) :
    ∃ error, e = .state error := by
  obtain ⟨hvalid, hnonce⟩ : validateTransaction fork included.sender tx =
      .ok included.intrinsicGas ∧
      tx.nonce.toNat = ((TransactionState.ofBlock block).getAccount included.sender).nonce := by
    obtain ⟨-, hv, -, -, -, -, -, -, hn, -⟩ := checkInclusion_ok hcheck
    exact ⟨hv, hn⟩
  have hsender : ((TransactionState.ofBlock block).getAccount included.sender).nonce <
      MAX_NONCE := by
    rw [← hnonce]
    exact (validateTransaction_ok hvalid).2.2.1
  have hhegota : ¬.hegota ≤ fork := Nat.not_le_of_lt before
  unfold processTransaction at h
  simp only [hhegota, ↓reduceIte] at h
  split at h
  · exact runTransaction_eq_error hfit hsender h
  · exact runTransaction_eq_error hfit hsender h

end EthLib.Execution.Transactions

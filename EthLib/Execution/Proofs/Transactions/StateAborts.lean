module

public import EthLib.Execution.Proofs.Transactions.Unfold
public import EthLib.Execution.Proofs.Evm.Call.StateAborts
public import EthLib.Execution.Proofs.Transactions.NoncesFit
import EthLib.Execution.Proofs.Evm.Call.ContractAddress

/-!
# Proofs: a transaction aborts only with an error of the state

Before Hegotá, a transaction aborts only with an error of the state.

Every nonce of its block must be at most `2^64 - 1`.
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

omit [LawfulGasMeter Meter] in
/-- The first frame of a message keeps the block and the transaction of the message. -/
private theorem env_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Base.Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame chainId message state substate auths paid = .ok first) :
    first.message.blockEnv = message.blockEnv ∧ first.message.txEnv = message.txEnv := by
  unfold prepareFirstFrame at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  all_goals
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩

/-! ## The message and the run of a transaction -/

/-- A transaction message from a state whose nonces fit fails only with an error of the state.

The numbers that its environment pushes as words must fit them. -/
theorem processMessageCall_eq_error {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    -- Every nonce of the state is at most `2^64 - 1`.
    {paid : Std.ExtTreeSet Base.Address} {e : EvmError} (hfit : state.NoncesFit)
    (hwords : WordsFit message.blockEnv message.txEnv)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .error e) :
    ∃ error, e = .state error := by
  rw [processMessageCall_unfold] at h
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
    -- The first frame keeps the environment of the message.
    obtain ⟨hblock, htx⟩ := env_prepareFirstFrame hprep
    have words : WordsFit first.message.blockEnv first.message.txEnv := hblock ▸ htx ▸ hwords
    split at h
    · rename_i hnone
      rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · refine processCreateMessage_eq_error fit words ?_ h
        rw [prepareFirstFrame_create_nonce hprep hnone]
        decide
      · cases h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact processMessage_eq_error fit words h
      · cases h

/-- A run of a transaction on a block whose nonces fit fails only with an error of the state.

The sender must start with a nonce below `2^64 - 1`.

The numbers that the block pushes as words must fit them, and so must the gas price. -/
private theorem runTransaction_eq_error {env : BlockEnvironment fork} {block : BlockState}
    {included : Included} {tx : Transaction} {e : EvmError}
    (hfit : (TransactionState.ofBlock block).NoncesFit) (hwords : env.WordsFit)
    (hprice : included.gasPrice < 2 ^ 256)
    (hsender : ((TransactionState.ofBlock block).getAccount included.sender).nonce < MAX_NONCE)
    (h : runTransaction Meter env block included tx = .error e) : ∃ error, e = .state error := by
  rw [runTransaction_unfold] at h
  rcases Base.bind_eq_error h with h | ⟨target, -, h⟩
  · unfold messageTarget at h
    split at h
    · cases h
    -- A transaction that creates encodes its sender and nonce to find the address of its account.
    --
    -- That nonce is below `2^64 - 1`, so the encoding succeeds.
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
  rcases Base.bind_eq_error h with h | ⟨message, hmessage, h⟩
  · unfold transactionMessage at h
    split at h
    · dsimp only at h
      generalize hx : Except.mapError EvmError.state _ = x at h
      cases x with
      | error e' => cases h; exact mapError_state_eq_error hx
      | ok _ => cases h
    · cases h
  rcases Base.bind_eq_error h with h | ⟨output, -, h⟩
  · -- The message has the block environment and the gas price of the transaction.
    have henv : message.blockEnv = env ∧ message.txEnv.gasPrice = included.gasPrice := by
      unfold transactionMessage at hmessage
      split at hmessage
      · obtain ⟨_, -, rfl⟩ := Base.map_ok_iff.mp hmessage
        exact ⟨rfl, rfl⟩
      · cases hmessage
        exact ⟨rfl, rfl⟩
    refine processMessageCall_eq_error fitBought ⟨?_, ?_⟩ h
    · show message.blockEnv.WordsFit
      rw [henv.1]
      exact hwords
    · show message.txEnv.gasPrice < 2 ^ 256
      rw [henv.2]
      exact hprice
  rcases Base.bind_eq_error h with h | ⟨⟨settled, used⟩, -, h⟩
  · exact mapError_state_eq_error h
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · exact mapError_state_eq_error h
  · cases h

end Meter

/-- A transaction that passes its inclusion check fails only with an error of the state.

The fork must be before Hegotá, and every nonce of the block must fit.

The numbers that the block pushes as words must fit them. -/
theorem processTransaction_eq_error {env : BlockEnvironment fork} {block : BlockState}
    {chainId : UInt64} {used : BlockGas} {included : Included} {tx : Transaction}
    {e : EvmError} (before : fork < .hegota)
    (hfit : (TransactionState.ofBlock block).NoncesFit) (hwords : env.WordsFit)
    (hcheck : checkInclusion chainId env used (.ofBlock block) tx = .ok included)
    (h : processTransaction env block included tx = .error e) :
    ∃ error, e = .state error := by
  obtain ⟨hvalid, hnonce⟩ : validateTransaction fork included.sender tx =
      .ok included.intrinsicGas ∧
      tx.nonce.toNat = ((TransactionState.ofBlock block).getAccount included.sender).nonce := by
    obtain ⟨-, hv, -, -, -, -, -, -, hn, -⟩ := checkInclusion_ok hcheck
    exact ⟨hv, hn⟩
  -- The inclusion check keeps the nonce of the sender below `2^64 - 1`.
  have hsender : ((TransactionState.ofBlock block).getAccount included.sender).nonce <
      MAX_NONCE := by
    rw [← hnonce]
    exact (validateTransaction_ok hvalid).2.2.1
  -- The gas price is at most the maximum fee, a word, since that fee covers the base fee.
  have hprice : included.gasPrice < 2 ^ 256 := by
    obtain ⟨-, -, -, -, -, hfee, -, hgas, -⟩ := checkInclusion_ok hcheck
    rw [hgas]
    refine Nat.lt_of_le_of_lt (effectiveGasPrice_le_maxFeePerGas hfee) ?_
    cases tx <;> exact BitVec.isLt _
  -- From Hegotá on, a transaction aborts because its fork is not yet specified.
  have hhegota : ¬.hegota ≤ fork := Nat.not_le_of_lt before
  rw [processTransaction_unfold] at h
  simp only [hhegota, ↓reduceIte] at h
  split at h
  · exact runTransaction_eq_error hfit hwords hprice hsender h
  · exact runTransaction_eq_error hfit hwords hprice hsender h

end EthLib.Execution.Transactions

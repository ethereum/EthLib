module

public import EthLib.Execution.Proofs.Evm.Call.Unmarked
public import EthLib.Execution.Proofs.Transactions.Deletion
public import EthLib.Execution.Proofs.Transactions.Inclusion

/-!
# Proofs: a transaction that runs raises the nonce of its sender

Replay protection rests on one fact: once a transaction runs, its nonce cannot be used again.

The inclusion check asks that the nonce of the transaction equals the nonce of the sender.

The sender buys the gas first, which adds one to its nonce.

The message never lowers a nonce, and the sender is never created or marked for deletion.

A creation needs an address with nonce 0, so it never goes to the sender.

Before Cancun, SELFDESTRUCT marks the account that runs it.

The sender has no code then, by [EIP-3607][e3607], and no frame runs code at its address.

From Cancun, SELFDESTRUCT marks only accounts created in the transaction, by [EIP-6780][e6780].

The settlement of gas keeps every nonce.

At the end, the marked accounts go.

From Glamsterdam, each keeps its balance, but loses its nonce, code and storage.

From Spurious Dragon, the empty touched accounts go too, by [EIP-161][e161].

The sender is neither marked nor empty, so it ends with a nonce above the nonce of the transaction.

From Pectra, the sender may authorize a delegation of itself, which adds one more.

So the nonce is at least the nonce of the transaction plus one, not exactly that.

A failed call whose only authorization is the sender's own, with the next nonce, ends two above.

From Glamsterdam, that needs the first frame of the call to start.

Before Pectra, a transaction holds no authorization, since its type must exist at its fork.

Section 6 of the [Yellow Paper][yp], Shanghai version, gives the nonce check.

Its Section 6.2 gives the gas purchase, which adds one to the nonce of the sender.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[e3607]: https://eips.ethereum.org/EIPS/eip-3607#specification
[e6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
[e161]: https://eips.ethereum.org/EIPS/eip-161#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (EMPTY_CODE_HASH)

variable {fork : Fork} {tx : Transaction}

/-! ## The message -/

section Meter

variable {Meter : Type} [GasMeter Meter]

/-- A creation of a transaction goes to an address with nonce 0.

Before Pectra, a call runs the code of its target. -/
private theorem prepareFirstFrame_nonce_code {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    (message.target = none → (state.getAccount message.currentTarget).nonce = 0) ∧
      (fork < .pectra → ∀ t, message.target = some t →
        first.state.getCode (first.state.getAccount t).codeHash = .ok first.message.code) := by
  unfold prepareFirstFrame at h
  split at h
  · rename_i hnone
    dsimp only at h
    split at h
    · rename_i hdeploy
      refine ⟨fun _ => ?_, fun _ t ht => by simp [hnone] at ht⟩
      have hn := State.TransactionState.nonce_eq_zero_of_accountDeployable hdeploy
      simpa using hn
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target hsome
    refine ⟨fun hn => by simp [hsome] at hn, fun hp t ht => ?_⟩
    rw [hsome] at ht
    cases ht
    dsimp only at h
    obtain ⟨done, -, h⟩ := bind_ok_iff.mp h
    generalize (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = read0 at h
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, hcode, h⟩ := bind_ok_iff.mp h
      have hcode := mapError_ok_iff.mp hcode
      generalize hdel : (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact hcode
      · have hnot : ¬fork ≥ .pectra := Nat.not_le.mpr hp
        simp only [hnot, ↓reduceIte, reduceCtorEq] at hdel

/-- The message of a transaction keeps or raises a nonce above 0, and never marks its account.

A call must run at the address it is sent to.

The account must not be created at the start, and nothing must be marked at the start.

Before Cancun, the account must have no code, and the message no authorization.

Before Cancun, the account still has no code at the end.

That holds whether or not the message ends with an error. -/
theorem processMessageCall_keeps {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {chainId : Nat} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {output : CallOutput} {address : Address}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output)
    (target : ∀ t, message.target = some t → message.currentTarget = t)
    (nonce : 1 ≤ (state.getAccount address).nonce)
    (fresh : address ∉ state.createdAccounts)
    (empty : ∀ marked, marked ∉ substate.accountsToDelete)
    (code : fork < .dencun →
      auths = [] ∧ (state.getAccount address).codeHash = EMPTY_CODE_HASH) :
    (state.getAccount address).nonce ≤ (output.state.getAccount address).nonce ∧
      address ∉ output.accountsToDelete ∧
      (fork < .dencun → (output.state.getAccount address).codeHash = EMPTY_CODE_HASH) := by
  have marks := fun hd : .dencun ≤ fork => accountsToDelete_processMessageCall hd h empty
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      refine ⟨Nat.le_refl _, by simp [CallOutput.ofHalt], fun hd => ?_⟩
      exact (code hd).2
  rename_i first hfirst
  obtain ⟨hcreate, hcode⟩ := prepareFirstFrame_nonce_code hfirst
  have hn := nonceLe_prepareFirstFrame hfirst
  have hc := createdAccounts_prepareFirstFrame hfirst
  obtain ⟨hstart, -, -, hcur⟩ := substate_prepareFirstFrame hfirst
  have nonce1 : 1 ≤ (first.state.getAccount address).nonce := Nat.le_trans nonce (hn address)
  have fresh1 : address ∉ first.state.createdAccounts := hc ▸ fresh
  have plain : fork < .dencun → PlainAccount address first.state := fun hd => by
    obtain ⟨hauths, hhash⟩ := code hd
    subst hauths
    have same := prepareFirstFrame_sameOutside hfirst address (by simp)
    refine ⟨nonce1, fresh1, ?_⟩
    unfold State.TransactionState.getAccount
    rw [same.1]
    exact hhash
  have unmarked0 : address ∉ first.substate.accountsToDelete := hstart ▸ empty address
  split at h
  · rename_i hnone
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    have ne : first.message.currentTarget ≠ address := by
      rw [hcur]
      intro heq
      have := hcreate hnone
      rw [heq] at this
      omega
    have fr := createsFresh_processCreateMessage hrun
    refine ⟨?_, fun mem => ?_, fun hd => ?_⟩
    · rw [state_ofFrame]
      exact Nat.le_trans (hn address) (fr.nonce address)
    · by_cases hd : .dencun ≤ fork
      · have created := marks hd address mem
        rw [state_ofFrame] at created
        rcases fr.fresh address created fresh1 with h0 | h0
        · omega
        · exact ne h0.symm
      · exact unmarked_processCreateMessage hrun ne (plain (Nat.lt_of_not_le hd)) unmarked0
          (accountsToDelete_ofFrame_subset _ _ _ address mem)
    · rw [state_ofFrame]
      exact (PlainAccount.of_createsFresh fr (plain hd) ne.symm).2.2
  · rename_i t hsome
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    have fr := createsFresh_processMessage hrun
    refine ⟨?_, fun mem => ?_, fun hd => ?_⟩
    · rw [state_ofFrame]
      exact Nat.le_trans (hn address) (fr.nonce address)
    · by_cases hd : .dencun ≤ fork
      · have created := marks hd address mem
        rw [state_ofFrame] at created
        rcases fr.fresh address created fresh1 with h0 | h0
        · omega
        · exact h0
      · have hd' := Nat.lt_of_not_le hd
        refine unmarked_processMessage hrun (fun heq => ?_) (plain hd') unmarked0
          (accountsToDelete_ofFrame_subset _ _ _ address mem)
        rw [hcur, target t hsome] at heq
        subst heq
        have hc := hcode (Nat.lt_of_lt_of_le hd' (by decide)) _ hsome
        rw [(plain hd').2.2] at hc
        simp [State.TransactionState.getCode] at hc
        rw [← hc]
        rfl
    · rw [state_ofFrame]
      exact (PlainAccount.of_createsFresh fr (plain hd) id).2.2

end Meter

/-! ## The transaction -/

/-- Before Pectra, a transaction whose type exists at its fork holds no authorization. -/
private theorem authorizations_eq_nil (hfork : tx.fork ≤ fork) (hp : fork < .pectra) :
    tx.authorizations = [] := by
  cases tx with
  | setCode t =>
    simp [Transaction.fork, Transaction.type, typeFork] at hfork
    exact absurd hfork (Nat.not_le.mpr hp)
  | _ => rfl

/-- The gas purchase keeps or raises every nonce, and keeps every code hash. -/
private theorem buyGas_nonce_codeHash {env : BlockEnvironment fork}
    {state state' : State.TransactionState} {sender : Address}
    (h : buyGas env state sender tx = .ok state') (address : Address) :
    (state.getAccount address).nonce ≤ (state'.getAccount address).nonce ∧
      (state'.getAccount address).codeHash = (state.getAccount address).codeHash := by
  by_cases hs : address = sender
  · subst hs
    exact ⟨by rw [(buyGas_sender rfl h).2.2]; omega, (buyGas_keeps h).1⟩
  · have same : state'.getAccount address = state.getAccount address := by
      unfold State.TransactionState.getAccount
      rw [(sameOutside_buyGas h address (by simpa using hs)).1]
    rw [same]
    exact ⟨Nat.le_refl _, rfl⟩

/-- A run of a transaction with any lawful meter buys the gas first.

After that purchase, it keeps or raises every nonce above 0.

Before Cancun, the account must have no code after the purchase, and it has none at the end. -/
private theorem runTransaction_nonce_le {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {block : State.BlockState} {included : Included}
    {out : TransactionOutput} (hauth : fork < .pectra → tx.authorizations = [])
    (h : runTransaction Meter env block included tx = .ok out) :
    ∃ bought, buyGas env (.ofBlock block) included.sender tx = .ok bought ∧
      ∀ address, 1 ≤ (bought.getAccount address).nonce →
        (fork < .dencun → (bought.getAccount address).codeHash = EMPTY_CODE_HASH) →
        (bought.getAccount address).nonce ≤ (out.state.getAccount address).nonce ∧
          (fork < .dencun → (out.state.getAccount address).codeHash = EMPTY_CODE_HASH) := by
  unfold runTransaction at h
  obtain ⟨target, htarget, h⟩ := bind_ok_iff.mp h
  obtain ⟨bought, hbought, h⟩ := bind_ok_iff.mp h
  have hbought := mapError_ok_iff.mp hbought
  obtain ⟨message, hmessage, h⟩ := bind_ok_iff.mp h
  obtain ⟨output, houtput, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨settled, gasUsed⟩, hsettle, h⟩ := bind_ok_iff.mp h
  have hsettle := mapError_ok_iff.mp hsettle
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  have hdeleted := mapError_ok_iff.mp hdeleted
  cases h
  refine ⟨bought, hbought, fun address nonce code => ?_⟩
  dsimp only
  have created : bought.createdAccounts = ∅ := by
    obtain ⟨mid, hmid, hfee⟩ := bind_ok_iff.mp hbought
    rw [State.TransactionState.createdAccounts_modifyState hfee,
      State.TransactionState.createdAccounts_modifyState hmid]
    rfl
  have links := target_transactionMessage hmessage
  have keeps := processMessageCall_keeps (address := address) houtput
    (fun t ht => by
      rw [links.2]
      rw [links.1] at ht
      unfold messageTarget at htarget
      rw [ht] at htarget
      cases htarget
      rfl)
    nonce (by simp [created]) (by simp)
    (fun hd => ⟨hauth (Nat.lt_of_lt_of_le hd (by decide)), code hd⟩)
  have settledNonce := (settleGas_accounts hsettle address).2.1
  have settledCode := (settleGas_accounts hsettle address).2.2.1
  rw [getAccount_deleteAccounts hdeleted (by omega) keeps.2.1]
  exact ⟨by omega, fun hd => settledCode.trans (keeps.2.2 hd)⟩

/-- A transaction that runs buys the gas first.

After that purchase, it keeps or raises every nonce above 0.

Before Cancun, the account must have no code after the purchase, and it has none at the end. -/
private theorem processTransaction_nonce_le_bought {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {out : TransactionOutput}
    (hfork : tx.fork ≤ fork) (h : processTransaction env block included tx = .ok out) :
    ∃ bought, buyGas env (.ofBlock block) included.sender tx = .ok bought ∧
      ∀ address, 1 ≤ (bought.getAccount address).nonce →
        (fork < .dencun → (bought.getAccount address).codeHash = EMPTY_CODE_HASH) →
        (bought.getAccount address).nonce ≤ (out.state.getAccount address).nonce ∧
          (fork < .dencun → (out.state.getAccount address).codeHash = EMPTY_CODE_HASH) := by
  have hauth := authorizations_eq_nil hfork
  by_cases hhegota : .hegota ≤ fork
  · rw [processTransaction_of_hegota_le hhegota] at h
    cases h
  unfold processTransaction at h
  simp only [hhegota, ↓reduceIte] at h
  split at h
  · exact runTransaction_nonce_le hauth h
  · exact runTransaction_nonce_le hauth h

/-- A transaction that runs leaves its sender with a nonce above the nonce of the transaction.

The transaction passes the inclusion check on the state of the block it runs on.

That holds whether or not its message ends with an error.

From Hegotá, no transaction runs yet, so the claim is empty there. -/
theorem processTransaction_nonce_lt {env : BlockEnvironment fork} {block : State.BlockState}
    {chainId : UInt64} {used : BlockGas} {included : Included} {out : TransactionOutput}
    (hcheck : checkInclusion chainId env used (.ofBlock block) tx = .ok included)
    (h : processTransaction env block included tx = .ok out) :
    tx.nonce.toNat < (out.state.getAccount included.sender).nonce := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hnonce, _, _, _, hcodeOf⟩ :=
    checkInclusion_eq_ok_iff.mp hcheck
  obtain ⟨bought, hbought, le⟩ :=
    processTransaction_nonce_le_bought (checkInclusion_fork_le hcheck) h
  have bumped := (buyGas_sender rfl hbought).2.2
  have := (le included.sender (by omega) (fun hd => by
    rw [(buyGas_keeps hbought).1]
    rcases hcodeOf with hempty | ⟨hge, -⟩
    · exact hempty
    · exact absurd hge (Nat.not_le.mpr (Nat.lt_of_lt_of_le hd (by decide))))).1
  omega

/-- A transaction that runs lowers no nonce of any account.

Its type must exist at the fork of the block, which a passing inclusion check gives.

Before Cancun, the account must have no code in the state of the block.

That holds whether or not its message ends with an error.

From Hegotá, no transaction runs yet, so the claim is empty there. -/
theorem processTransaction_nonce_le {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {out : TransactionOutput} {address : Address} (hfork : tx.fork ≤ fork)
    (h : processTransaction env block included tx = .ok out)
    (code : fork < .dencun →
      ((State.TransactionState.ofBlock block).getAccount address).codeHash = EMPTY_CODE_HASH) :
    ((State.TransactionState.ofBlock block).getAccount address).nonce ≤
      (out.state.getAccount address).nonce := by
  by_cases zero : ((State.TransactionState.ofBlock block).getAccount address).nonce = 0
  · omega
  obtain ⟨bought, hbought, le⟩ := processTransaction_nonce_le_bought hfork h
  obtain ⟨hn, hc⟩ := buyGas_nonce_codeHash hbought address
  have := (le address (by omega) (fun hd => hc ▸ code hd)).1
  omega

/-- Before Cancun, a transaction that runs gives no code to an account with a nonce.

The account has no code in the state of the block.

It has a nonce there, or it is the sender, whose nonce the gas purchase raises.

Its type must exist at the fork of the block, which a passing inclusion check gives.

That holds whether or not its message ends with an error. -/
theorem processTransaction_codeHash_of_lt_dencun {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {out : TransactionOutput}
    {address : Address} (hd : fork < .dencun) (hfork : tx.fork ≤ fork)
    (h : processTransaction env block included tx = .ok out)
    (nonce : 1 ≤ ((State.TransactionState.ofBlock block).getAccount address).nonce ∨
      address = included.sender)
    (code : ((State.TransactionState.ofBlock block).getAccount address).codeHash =
      EMPTY_CODE_HASH) :
    (out.state.getAccount address).codeHash = EMPTY_CODE_HASH := by
  obtain ⟨bought, hbought, le⟩ := processTransaction_nonce_le_bought hfork h
  obtain ⟨hn, hc⟩ := buyGas_nonce_codeHash hbought address
  refine (le address ?_ (fun _ => hc ▸ code)).2 hd
  rcases nonce with nonce | rfl
  · omega
  · have := (buyGas_sender rfl hbought).2.2
    omega

/-! ## A sender that authorizes itself -/

/-- A sender that signs its own authorization ends a failed call two nonces above its transaction.

The authorization is the only one of the transaction, and it is in scope.

Its nonce is the nonce of the transaction plus one, since the gas purchase comes first.

From Glamsterdam, the first frame of the call must start. -/
theorem processTransaction_selfAuthorization_of_error {env : BlockEnvironment fork}
    {block : State.BlockState} {chainId : UInt64} {used : BlockGas} {included : Included}
    {out : TransactionOutput} {auth : Authorization}
    (hcheck : checkInclusion chainId env used (.ofBlock block) tx = .ok included)
    (h : processTransaction env block included tx = .ok out) (failed : out.error.isSome = true)
    (hstarts : .glamsterdam ≤ fork → ¬FirstFrameHalts StateGasMeter tx env block included)
    (hauths : tx.authorizations = [auth])
    (hscope : authorizationInScope env.chainId.toNat auth = true)
    (hrecover : recoverAuthority auth = some included.sender)
    (hnonce : auth.nonce.toNat = tx.nonce.toNat + 1) :
    (out.state.getAccount included.sender).nonce = tx.nonce.toNat + 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsender, _, code, hcode, hkind⟩ :=
    checkInclusion_eq_ok_iff.mp hcheck
  have hdelegable : (code.size = 0 || isValidDelegation code) = true := by
    rcases hkind with hempty | ⟨-, hvalid⟩
    · rw [hempty] at hcode
      simp only [State.TransactionState.getCode, ↓reduceIte, Except.ok.injEq] at hcode
      subst hcode
      rfl
    · simp [hvalid]
  have hn := (processTransaction_authority_of_error h failed hstarts hcode hdelegable).1
  have haccepted : acceptedBy env.chainId.toNat included.sender (tx.nonce.toNat + 1) [auth] =
      [auth] := by
    simp [acceptedBy, hscope, hrecover, hnonce]
  simp only [↓reduceIte, hauths, ← hsender] at hn
  simp only [haccepted, List.length_singleton] at hn
  exact hn

end EthLib.Execution.Transactions

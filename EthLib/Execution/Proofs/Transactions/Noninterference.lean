module

public import EthLib.Execution.Proofs.Evm.Call.NoninterferenceRun
public import EthLib.Execution.Proofs.Transactions.Candidate
public import EthLib.Execution.Proofs.Transactions.CodeOrigin
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: the message of a transaction depends only on what it records

Run the message of a transaction on two states that agree on four sets.

The sets name accounts, whole storages, slots and code hashes.

When the first run ends with every read in the sets, the second gives the same output.

Only the states of the two outputs differ, and they agree.

The preparation of the first frame reads each authority before it looks at its account.

It reads the recipient, then its delegate, each before it fetches its code.

A creation reads its address before it checks that a contract may be deployed there.

So each lookup of the preparation is at an account in the sets.

Both runs then prepare the same frame.

The run of a message depends only on what it records, so the two outputs agree.

A preparation that halts returns its state so far, and both runs halt with the same error.

The code that the message carries into the preparation of a call is replaced there.

The sets play the part of a block access list in [EIP-7928, Scope and Inclusion][bal].

[bal]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State
open EthLib.Execution.State.TransactionState (AgreesOn NoNewCandidate)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The code of the message of a call -/

/-- The preparation of a call replaces the code of its message, so it ignores that code. -/
theorem prepareFirstFrame_withCode {chainId : Nat} {message : Message fork} {target : Address}
    (htarget : message.target = some target) (code : ByteArray) (state : TransactionState)
    (substate : Substate) (auths : List Authorization) (paid : Std.ExtTreeSet Address) :
    prepareFirstFrame (Meter := Meter) chainId { message with code } state substate auths paid =
      prepareFirstFrame chainId message state substate auths paid := by
  simp only [prepareFirstFrame, htarget]

/-- The message of a call ignores the code that it starts with. -/
theorem processMessageCall_withCode [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {target : Address} (htarget : message.target = some target)
    (code : ByteArray) (state : TransactionState) (substate : Substate)
    (auths : List Authorization) (paid : Std.ExtTreeSet Address) :
    processMessageCall (Meter := Meter) chainId { message with code } state substate auths paid =
      processMessageCall (Meter := Meter) chainId message state substate auths paid := by
  simp only [processMessageCall, prepareFirstFrame_withCode htarget]

/-! ## Reads and lookups -/

section Helpers

variable {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
  {code : Hash32 → Prop}

/-- A record of an account read keeps every read. -/
private theorem readsLe_recordAccountRead (tx : TransactionState) (address : Address) :
    tx.ReadsLe (tx.recordAccountRead address) :=
  ⟨fun _ h => Std.ExtTreeSet.mem_insert.mpr (.inr h), fun _ _ h => h⟩

/-- A record of an account read holds that read. -/
private theorem mem_recordAccountRead (tx : TransactionState) (address : Address) :
    address ∈ (tx.recordAccountRead address).accountReads :=
  Std.ExtTreeSet.mem_insert_self

/-- An authorization that sets the code of its authority keeps every read. -/
private theorem readsLe_delegate {state state' : TransactionState} {authority : Address}
    {auth : Authorization} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) : state.ReadsLe state' := by
  obtain ⟨coded, hcode, h⟩ := bind_ok_iff.mp h
  obtain ⟨bumped, hnonce, h⟩ := bind_ok_iff.mp h
  cases h
  exact (readsLe_setCode hcode).trans (readsLe_modifyState hnonce)

/-- At an account in the sets, both states fetch the same code for its current code hash. -/
private theorem getCode_getAccount_eq {block : BlockState}
    (covers : CoversBlock block account allStorage code) {tx other : TransactionState}
    (hagree : AgreesOn account allStorage slot code tx other) (horigin : CodeOrigin block tx)
    {address : Address} (ha : account address) :
    other.getCode (other.getAccount address).codeHash =
      tx.getCode (tx.getAccount address).codeHash := by
  rw [hagree.getAccount_eq (.inr ha)]
  exact hagree.getCode_eq ((horigin address).imp_right
    (Or.imp_right fun heq => by rw [heq]; exact covers.code address ha))

/-- At an account in the sets, both states fetch the same code for its code hash in the block. -/
private theorem getCode_getPreStateAccount_eq {block : BlockState}
    (covers : CoversBlock block account allStorage code) {tx other : TransactionState}
    (hagree : AgreesOn account allStorage slot code tx other) (hparent : tx.parent = block)
    {address : Address} (ha : account address) :
    other.getCode (other.getPreStateAccount address).codeHash =
      tx.getCode (tx.getPreStateAccount address).codeHash := by
  rw [hagree.getPreStateAccount_eq ha]
  refine hagree.getCode_eq (.inr (.inr ?_))
  have : tx.getPreStateAccount address =
      (TransactionState.ofBlock block).getAccount address := by
    subst hparent
    simp [TransactionState.getPreStateAccount, TransactionState.getAccount,
      TransactionState.getAccountOptional, TransactionState.ofBlock,
      TransactionState.getPreStateAccountOptional]
  rw [this]
  exact covers.code address ha

/-! ## The authorizations -/

/-- The state that a result ends with: that of its value, or that of its error. -/
private def outState {α : Type} (getState : α → TransactionState) :
    Except (EvmError × TransactionState) α → TransactionState
  | .ok a => getState a
  | .error (_, read) => read

/-- Two results of the authorizations are the same, up to their states, which agree. -/
private def DelegationsAgree (account allStorage : Address → Prop)
    (slot : Address → Bytes32 → Prop) (code : Hash32 → Prop) :
    Except (EvmError × TransactionState) (Delegations Meter) →
      Except (EvmError × TransactionState) (Delegations Meter) → Prop
  | .ok d, .ok d' => d' = { d with state := d'.state } ∧ AgreesOn account allStorage slot code
      d.state d'.state
  | .error (e, read), .error (e', read') => e' = e ∧ AgreesOn account allStorage slot code
      read read'
  | _, _ => False

/-- At an authority in the sets, both states accept an authorization alike. -/
private theorem authorityAccepts_eq {block : BlockState}
    (covers : CoversBlock block account allStorage code) {tx other : TransactionState}
    (hagree : AgreesOn account allStorage slot code tx other) (horigin : CodeOrigin block tx)
    {authority : Address} (ha : account authority) (auth : Authorization) :
    authorityAccepts other authority auth = authorityAccepts tx authority auth := by
  have hcode := getCode_getAccount_eq covers hagree horigin ha
  rw [hagree.getAccount_eq (.inr ha)] at hcode
  simp only [authorityAccepts, hagree.getAccount_eq (.inr ha), hcode]

/-- At an authority in the sets, the payment of an authorization ignores the rest of the state. -/
private theorem payAuthorization_withState {block : BlockState}
    (covers : CoversBlock block account allStorage code) {done : Delegations Meter}
    {other : TransactionState} (hagree : AgreesOn account allStorage slot code done.state other)
    (hparent : done.state.parent = block) {authority : Address} (ha : account authority)
    (auth : Authorization) :
    payAuthorization fork { done with state := other } authority auth =
      (fun paid => { paid with state := other }) <$> payAuthorization fork done authority auth := by
  have hcharge : chargeAuthorization { done with state := other } authority auth =
      chargeAuthorization done authority auth := by
    simp only [chargeAuthorization, hagree.accountExists_eq (.inr ha),
      getCode_getPreStateAccount_eq covers hagree hparent ha]
  unfold payAuthorization
  split
  · rw [hcharge]
    cases chargeAuthorization done authority auth <;> rfl
  · rfl

/-- At an authority in the sets, an authorization sets the code alike on agreeing states. -/
private theorem delegate_agrees {tx other : TransactionState}
    (hagree : AgreesOn account allStorage slot code tx other) {authority : Address}
    (ha : account authority) (auth : Authorization) :
    ExceptRel (fun p q : TransactionState × Nat => AgreesOn account allStorage slot code p.1 q.1 ∧
        q.2 = p.2)
      (delegate fork tx authority auth) (delegate fork other authority auth) := by
  unfold delegate
  rw [hagree.accountExists_eq (.inr ha)]
  refine ExceptRel.bind (hagree.setCode fork (.inr ha) _) fun hab _ _ => ?_
  refine ExceptRel.bind (hab.incrementNonce fork (.inr ha)) fun hcd _ _ => ?_
  exact ⟨hcd, rfl⟩

/-- One authorization with its reads in the sets gives the same result on an agreeing state. -/
private theorem applyAuthorization_agrees {block : BlockState}
    (covers : CoversBlock block account allStorage code) {chainId : Nat}
    {done : Delegations Meter} {other : TransactionState} {auth : Authorization}
    (hagree : AgreesOn account allStorage slot code done.state other)
    (hparent : done.state.parent = block) (horigin : CodeOrigin block done.state)
    (hreads : ReadsIn account slot
      (outState Delegations.state (applyAuthorization fork chainId done auth))) :
    DelegationsAgree account allStorage slot code (applyAuthorization fork chainId done auth)
      (applyAuthorization fork chainId { done with state := other } auth) := by
  unfold applyAuthorization at hreads ⊢
  cases hscope : authorizationInScope chainId auth
  · exact ⟨rfl, hagree⟩
  cases hrec : recoverAuthority auth with
  | none => exact ⟨rfl, hagree⟩
  | some authority =>
    simp only [hscope, hrec, ↓reduceIte] at hreads ⊢
    have hrecord := hagree.recordAccountRead authority
    have horigin' : CodeOrigin block (done.state.recordAccountRead authority) := horigin
    have hmem := mem_recordAccountRead done.state authority
    cases hacc : authorityAccepts (done.state.recordAccountRead authority) authority auth with
    | error e =>
      simp only [hacc, Except.mapError, bind, Except.bind, outState, Function.comp] at hreads
      rw [authorityAccepts_eq covers hrecord horigin' (hreads.account _ hmem), hacc]
      exact ⟨rfl, hrecord⟩
    | ok accepts =>
      simp only [hacc, Except.mapError, bind, Except.bind] at hreads ⊢
      cases accepts with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, outState] at hreads ⊢
        rw [authorityAccepts_eq covers hrecord horigin' (hreads.account _ hmem), hacc]
        exact ⟨rfl, hrecord⟩
      | true =>
        simp only [↓reduceIte] at hreads ⊢
        generalize hd : (⟨done.state.recordAccountRead authority, done.accessed.insert authority,
          done.refund, done.meter, done.paidWrites, done.delegated⟩ : Delegations Meter) = d
          at hreads ⊢
        have ha : account authority := by
          refine (ReadsIn.of_readsLe ?_ hreads).account _ hmem
          cases hpay : payAuthorization fork d authority auth with
          | error e => exact .refl _
          | ok p =>
            have hp : p.state = done.state.recordAccountRead authority := by
              rw [(state_payAuthorization hpay).1, ← hd]
            cases hdel : delegate fork p.state authority auth with
            | error e =>
              simp only [hdel, outState, Function.comp]
              exact .refl _
            | ok sr =>
              obtain ⟨s, r⟩ := sr
              simp only [hdel, outState, pure, Except.pure]
              rw [← hp]
              exact readsLe_delegate hdel
        have hd' : (⟨other.recordAccountRead authority, done.accessed.insert authority,
            done.refund, done.meter, done.paidWrites, done.delegated⟩ : Delegations Meter) =
            { d with state := other.recordAccountRead authority } := by
          rw [← hd]
        have hpay2 := payAuthorization_withState (fork := fork) covers (done := d)
          (other := other.recordAccountRead authority) (by rw [← hd]; exact hrecord)
          (by rw [← hd]; exact hparent) ha auth
        rw [authorityAccepts_eq covers hrecord horigin' ha, hacc, hd', hpay2]
        simp only [↓reduceIte]
        cases hpay : payAuthorization fork d authority auth with
        | error e => exact ⟨rfl, hrecord⟩
        | ok p =>
          have hp : p.state = done.state.recordAccountRead authority := by
            rw [(state_payAuthorization hpay).1, ← hd]
          have hrel := delegate_agrees (fork := fork) hrecord ha auth
          rw [← hp] at hrel
          simp only [Functor.map, Except.map]
          cases hdel : delegate fork p.state authority auth with
          | error e =>
            cases hdel2 : delegate fork (other.recordAccountRead authority) authority auth <;>
              simp only [hdel, hdel2, ExceptRel] at hrel
            subst hrel
            exact ⟨rfl, hrecord⟩
          | ok sr =>
            cases hdel2 : delegate fork (other.recordAccountRead authority) authority auth with
            | error e => simp only [hdel, hdel2, ExceptRel] at hrel
            | ok sr' =>
              simp only [hdel, hdel2, ExceptRel] at hrel
              refine ⟨?_, hrel.1⟩
              simp only [hrel.2]

/-- One authorization keeps every read, whether it succeeds or fails. -/
private theorem readsLe_applyAuthorization {chainId : Nat} (done : Delegations Meter)
    (auth : Authorization) :
    done.state.ReadsLe
      (outState Delegations.state (applyAuthorization fork chainId done auth)) := by
  unfold applyAuthorization
  cases hscope : authorizationInScope chainId auth
  · exact .refl _
  cases hrec : recoverAuthority auth with
  | none => exact .refl _
  | some authority =>
    simp only [↓reduceIte]
    refine (readsLe_recordAccountRead _ authority).trans ?_
    cases hacc : authorityAccepts (done.state.recordAccountRead authority) authority auth with
    | error e => exact .refl _
    | ok accepts =>
      simp only [Except.mapError, bind, Except.bind]
      cases accepts with
      | false => exact .refl _
      | true =>
        simp only [↓reduceIte]
        generalize hd : (⟨done.state.recordAccountRead authority, done.accessed.insert authority,
          done.refund, done.meter, done.paidWrites, done.delegated⟩ : Delegations Meter) = d
        cases hpay : payAuthorization fork d authority auth with
        | error e => exact .refl _
        | ok p =>
          have hp : p.state = done.state.recordAccountRead authority := by
            rw [(state_payAuthorization hpay).1, ← hd]
          cases hdel : delegate fork p.state authority auth with
          | error e =>
            simp only [hdel, outState]
            exact .refl _
          | ok sr =>
            obtain ⟨s, r⟩ := sr
            simp only [hdel, outState, pure, Except.pure]
            rw [← hp]
            exact readsLe_delegate hdel

/-- The authorizations from a state keep every read, whether they succeed or fail. -/
private theorem readsLe_foldlM_applyAuthorization {chainId : Nat} :
    ∀ (auths : List Authorization) (start : Delegations Meter),
      start.state.ReadsLe
        (outState Delegations.state (auths.foldlM (applyAuthorization fork chainId) start))
  | [], _ => .refl _
  | auth :: rest, start => by
    have h1 := readsLe_applyAuthorization (fork := fork) (chainId := chainId) start auth
    simp only [List.foldlM_cons]
    cases happ : applyAuthorization fork chainId start auth with
    | error e =>
      rw [happ] at h1
      exact h1
    | ok next =>
      rw [happ] at h1
      exact h1.trans (readsLe_foldlM_applyAuthorization rest next)

/-- The authorizations with their reads in the sets give the same result on an agreeing state. -/
private theorem foldlM_applyAuthorization_agrees {block : BlockState}
    (covers : CoversBlock block account allStorage code) {chainId : Nat} :
    ∀ (auths : List Authorization) (start : Delegations Meter) (other : TransactionState),
      AgreesOn account allStorage slot code start.state other → start.state.parent = block →
      CodeOrigin block start.state →
      ReadsIn account slot
        (outState Delegations.state (auths.foldlM (applyAuthorization fork chainId) start)) →
      DelegationsAgree account allStorage slot code
        (auths.foldlM (applyAuthorization fork chainId) start)
        (auths.foldlM (applyAuthorization fork chainId) { start with state := other })
  | [], _, _, hagree, _, _, _ => ⟨rfl, hagree⟩
  | auth :: rest, start, other, hagree, hparent, horigin, hreads => by
    simp only [List.foldlM_cons] at hreads ⊢
    have hstep := applyAuthorization_agrees (fork := fork) (auth := auth) (chainId := chainId)
      covers hagree
      hparent horigin
    cases happ : applyAuthorization fork chainId start auth with
    | error er =>
      obtain ⟨e, read⟩ := er
      rw [happ] at hstep hreads
      have hstep := hstep hreads
      cases happ2 : applyAuthorization fork chainId { start with state := other } auth with
      | error er' =>
        rw [happ2] at hstep
        exact hstep
      | ok _ =>
        rw [happ2] at hstep
        exact hstep.elim
    | ok next =>
      rw [happ] at hstep hreads
      have hnext := ReadsIn.of_readsLe (readsLe_foldlM_applyAuthorization rest next) hreads
      have hstep := hstep hnext
      cases happ2 : applyAuthorization fork chainId { start with state := other } auth with
      | error _ =>
        rw [happ2] at hstep
        exact hstep.elim
      | ok next' =>
        rw [happ2] at hstep
        obtain ⟨hsame, hagree'⟩ := hstep
        have hkeeps := keepsCodeOrigin_applyAuthorization happ
        simp only [bind, Except.bind]
        rw [hsame]
        exact foldlM_applyAuthorization_agrees covers rest next next'.state hagree'
          (hkeeps.1.trans hparent) (horigin.of_keepsCodeOrigin hkeeps) hreads

/-! ## The preparation -/

/-- Two results of the preparation are the same, up to their states, which agree. -/
private def FramesAgree (account allStorage : Address → Prop)
    (slot : Address → Bytes32 → Prop) (code : Hash32 → Prop) :
    Except (EvmError × TransactionState) (FirstFrame fork Meter) →
      Except (EvmError × TransactionState) (FirstFrame fork Meter) → Prop
  | .ok f, .ok f' => f' = { f with state := f'.state } ∧ AgreesOn account allStorage slot code
      f.state f'.state
  | .error (e, read), .error (e', read') => e' = e ∧ AgreesOn account allStorage slot code
      read read'
  | _, _ => False

/-- The end of the preparation of a call, from the state before the read of its recipient.

It reads the recipient, then the delegate, and fetches their code. -/
private def callRest (message : Message fork) (target : Address) (substate : Substate)
    (accessed : Std.ExtTreeSet Address) (refund : Nat) (state : TransactionState)
    (meter : Meter) : Except (EvmError × TransactionState) (FirstFrame fork Meter) := do
  let substate := { substate with accessedAddresses := accessed }
  let state := state.recordAccountRead target
  let code ← (state.getCode (state.getAccount target).codeHash).mapError (.state ·, state)
  match if fork ≥ .pectra then delegatedAddress code else none with
  | some delegate =>
    let meter ← if fork ≥ .glamsterdam then
        (GasMeter.charge meter (accountAccessCost fork (delegate ∉ accessed))).mapError
          (·, state)
      else pure meter
    let state := state.recordAccountRead delegate
    let code ← (state.getCode (state.getAccount delegate).codeHash).mapError (.state ·, state)
    let message := { message with code, codeAddress := some delegate, disablePrecompiles := true }
    let substate := { substate with accessedAddresses := accessed.insert delegate }
    return .ofMeter message state substate refund meter
  | none => return .ofMeter { message with code } state substate refund meter

/-- The preparation of a call, from the delegations that its authorizations end with. -/
private def callFrame (message : Message fork) (target : Address) (substate : Substate)
    (done : Delegations Meter) : Except (EvmError × TransactionState) (FirstFrame fork Meter) := do
  let meter := GasMeter.commit done.meter
  let state := if message.value ≠ 0 then done.state.recordAccountRead target else done.state
  let meter ←
    if fork ≥ .glamsterdam ∧ message.value ≠ 0 ∧ !state.isAccountAlive target then
      (GasMeter.chargeState meter GasCosts.NEW_ACCOUNT_STATE_GAS).mapError (·, state)
    else pure meter
  callRest message target substate done.accessed done.refund state meter

/-- The preparation of a call applies its authorizations, then the rest of the preparation. -/
private theorem prepareFirstFrame_call {chainId : Nat} {message : Message fork}
    {target : Address} (htarget : message.target = some target) (state : TransactionState)
    (substate : Substate) (auths : List Authorization) (paid : Std.ExtTreeSet Address) :
    prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      applyAuthorizations fork chainId state substate.accessedAddresses
        (GasMeter.start message.gas message.reservoir) paid auths >>=
        callFrame message target substate := by
  cases message
  cases htarget
  simp only [prepareFirstFrame]
  congr 1

/-- The end of the preparation of a call keeps every read, with the read of its recipient. -/
private theorem readsLe_callRest {message : Message fork} {target : Address}
    {substate : Substate} {accessed : Std.ExtTreeSet Address} {refund : Nat}
    (state : TransactionState) (meter : Meter) :
    (state.recordAccountRead target).ReadsLe (outState FirstFrame.state
      (callRest message target substate accessed refund state meter)) := by
  unfold callRest
  simp only [bind, Except.bind, Except.mapError, pure, Except.pure]
  cases (state.recordAccountRead target).getCode
    ((state.recordAccountRead target).getAccount target).codeHash with
  | error e => exact .refl _
  | ok cd =>
    simp only
    cases (if fork ≥ .pectra then delegatedAddress cd else none) with
    | none => exact .refl _
    | some dg =>
      simp only
      have hdg := readsLe_recordAccountRead (state.recordAccountRead target) dg
      by_cases hg : fork ≥ .glamsterdam
      · simp only [hg, ↓reduceIte]
        cases GasMeter.charge meter (accountAccessCost fork (decide (dg ∉ accessed))) with
        | error e => exact .refl _
        | ok m =>
          simp only
          cases ((state.recordAccountRead target).recordAccountRead dg).getCode
            (((state.recordAccountRead target).recordAccountRead dg).getAccount dg).codeHash <;>
          exact hdg
      · simp only [hg, ↓reduceIte]
        cases ((state.recordAccountRead target).recordAccountRead dg).getCode
          (((state.recordAccountRead target).recordAccountRead dg).getAccount dg).codeHash <;>
        exact hdg

/-- The end of the preparation of a call with its reads in the sets agrees on agreeing states. -/
private theorem callRest_framesAgree {block : BlockState}
    (covers : CoversBlock block account allStorage code) {message : Message fork}
    {target : Address} {substate : Substate} {accessed : Std.ExtTreeSet Address} {refund : Nat}
    {state other : TransactionState} (hagree : AgreesOn account allStorage slot code state other)
    (horigin : CodeOrigin block state) (meter : Meter)
    (hreads : ReadsIn account slot (outState FirstFrame.state
      (callRest message target substate accessed refund state meter))) :
    FramesAgree account allStorage slot code
      (callRest message target substate accessed refund state meter)
      (callRest message target substate accessed refund other meter) := by
  have hrecord := hagree.recordAccountRead target
  have horigin' : CodeOrigin block (state.recordAccountRead target) := horigin
  have ht : account target := (ReadsIn.of_readsLe (readsLe_callRest state meter) hreads).account
    _ (mem_recordAccountRead _ _)
  unfold callRest at hreads ⊢
  simp only [bind, Except.bind, Except.mapError, pure, Except.pure] at hreads ⊢
  rw [getCode_getAccount_eq covers hrecord horigin' ht]
  cases hc : (state.recordAccountRead target).getCode
    ((state.recordAccountRead target).getAccount target).codeHash with
  | error e => exact ⟨rfl, hrecord⟩
  | ok cd =>
    rw [hc] at hreads
    simp only at hreads ⊢
    cases hd : (if fork ≥ .pectra then delegatedAddress cd else none) with
    | none => exact ⟨rfl, hrecord⟩
    | some dg =>
      rw [hd] at hreads
      simp only at hreads ⊢
      have hrecord2 := hrecord.recordAccountRead dg
      have horigin2 : CodeOrigin block ((state.recordAccountRead target).recordAccountRead dg) :=
        horigin
      by_cases hg : fork ≥ .glamsterdam
      · simp only [hg, ↓reduceIte] at hreads ⊢
        cases hm : GasMeter.charge meter (accountAccessCost fork (decide (dg ∉ accessed))) with
        | error e => exact ⟨rfl, hrecord⟩
        | ok m =>
          rw [hm] at hreads
          simp only at hreads ⊢
          have hdg : account dg := by
            refine hreads.account _ ?_
            cases ((state.recordAccountRead target).recordAccountRead dg).getCode
              (((state.recordAccountRead target).recordAccountRead dg).getAccount dg).codeHash <;>
            exact mem_recordAccountRead _ _
          rw [getCode_getAccount_eq covers hrecord2 horigin2 hdg]
          cases ((state.recordAccountRead target).recordAccountRead dg).getCode
            (((state.recordAccountRead target).recordAccountRead dg).getAccount dg).codeHash <;>
          exact ⟨rfl, hrecord2⟩
      · simp only [hg, ↓reduceIte] at hreads ⊢
        have hdg : account dg := by
          refine hreads.account _ ?_
          cases ((state.recordAccountRead target).recordAccountRead dg).getCode
            (((state.recordAccountRead target).recordAccountRead dg).getAccount dg).codeHash <;>
          exact mem_recordAccountRead _ _
        rw [getCode_getAccount_eq covers hrecord2 horigin2 hdg]
        cases ((state.recordAccountRead target).recordAccountRead dg).getCode
          (((state.recordAccountRead target).recordAccountRead dg).getAccount dg).codeHash <;>
        exact ⟨rfl, hrecord2⟩

/-- The preparation of a call after its authorizations keeps every read, with its recipient. -/
private theorem readsLe_callFrame {message : Message fork} {target : Address}
    {substate : Substate} (done : Delegations Meter) :
    (done.state.recordAccountRead target).ReadsLe
      (outState FirstFrame.state (callFrame message target substate done)) := by
  unfold callFrame
  by_cases hv : message.value = 0
  · simp only [hv, ne_eq, not_true_eq_false, ↓reduceIte, false_and, and_false, pure,
      Except.pure, bind, Except.bind]
    exact readsLe_callRest _ _
  · simp only [hv, ne_eq, not_false_eq_true, ↓reduceIte, true_and, bind, Except.bind, pure,
      Except.pure, Except.mapError]
    split
    · cases GasMeter.chargeState (GasMeter.commit done.meter) GasCosts.NEW_ACCOUNT_STATE_GAS with
      | error e => exact .refl _
      | ok m => exact (readsLe_recordAccountRead _ _).trans (readsLe_callRest _ _)
    · exact (readsLe_recordAccountRead _ _).trans (readsLe_callRest _ _)

/-- The preparation of a call after its authorizations agrees on agreeing states. -/
private theorem callFrame_framesAgree {block : BlockState}
    (covers : CoversBlock block account allStorage code) {message : Message fork}
    {target : Address} {substate : Substate} {done : Delegations Meter}
    {other : TransactionState} (hagree : AgreesOn account allStorage slot code done.state other)
    (horigin : CodeOrigin block done.state)
    (hreads : ReadsIn account slot (outState FirstFrame.state
      (callFrame message target substate done))) :
    FramesAgree account allStorage slot code (callFrame message target substate done)
      (callFrame message target substate { done with state := other }) := by
  have ht : account target :=
    (ReadsIn.of_readsLe (readsLe_callFrame done) hreads).account _ (mem_recordAccountRead _ _)
  have hrecord := hagree.recordAccountRead target
  have horigin' : CodeOrigin block (done.state.recordAccountRead target) := horigin
  unfold callFrame at hreads ⊢
  by_cases hv : message.value = 0
  · simp only [hv, ne_eq, not_true_eq_false, ↓reduceIte, false_and, and_false, pure,
      Except.pure, bind, Except.bind] at hreads ⊢
    exact callRest_framesAgree covers hagree horigin _ hreads
  · simp only [hv, ne_eq, not_false_eq_true, ↓reduceIte, true_and, bind, Except.bind, pure,
      Except.pure, Except.mapError] at hreads ⊢
    rw [hrecord.isAccountAlive_eq (.inr ht)]
    split
    · rename_i hcond
      simp only [hcond] at hreads
      cases hc : GasMeter.chargeState (GasMeter.commit done.meter)
        GasCosts.NEW_ACCOUNT_STATE_GAS with
      | error e => exact ⟨rfl, hrecord⟩
      | ok m =>
        rw [hc] at hreads
        exact callRest_framesAgree covers hrecord horigin' m hreads
    · rename_i hcond
      simp only [hcond, ↓reduceIte] at hreads
      exact callRest_framesAgree covers hrecord horigin' _ hreads

/-- A preparation with its reads in the sets gives the same result on an agreeing state. -/
private theorem prepareFirstFrame_framesAgree {block : BlockState}
    (covers : CoversBlock block account allStorage code) {chainId : Nat} {message : Message fork}
    {state other : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} (hagree : AgreesOn account allStorage slot code state other)
    (hparent : state.parent = block) (horigin : CodeOrigin block state)
    (hcandidates : NoNewCandidate block state)
    (hreads : ReadsIn account slot (outState FirstFrame.state
      (prepareFirstFrame (Meter := Meter) chainId message state substate auths paid))) :
    FramesAgree (Meter := Meter) account allStorage slot code
      (prepareFirstFrame chainId message state substate auths paid)
      (prepareFirstFrame chainId message other substate auths paid) := by
  cases htarget : message.target with
  | none =>
    unfold prepareFirstFrame at hreads ⊢
    rw [htarget] at hreads ⊢
    simp only [bind, Except.bind, Except.mapError, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hreads ⊢
    have hrecord := hagree.recordAccountRead message.currentTarget
    generalize GasMeter.chargeState (GasMeter.start (Meter := Meter) message.gas message.reservoir)
      GasCosts.NEW_ACCOUNT_STATE_GAS = charged at hreads ⊢
    have ha : account message.currentTarget := by
      refine hreads.account _ ?_
      by_cases hd : (state.recordAccountRead message.currentTarget).accountDeployable
        message.currentTarget = true <;>
      by_cases hg : fork ≥ .glamsterdam ∧ (state.recordAccountRead
        message.currentTarget).getPreStateAccount message.currentTarget = EMPTY_ACCOUNT <;>
      cases charged <;> simp only [hd, hg, ↓reduceIte, outState, FirstFrame.ofMeter] <;>
      exact mem_recordAccountRead _ _
    have hdeploy : (other.recordAccountRead message.currentTarget).accountDeployable
        message.currentTarget = (state.recordAccountRead message.currentTarget).accountDeployable
        message.currentTarget :=
      hrecord.accountDeployable_eq (.inr ha) fun hn hc =>
        (hcandidates _ hn hc).imp_right fun ⟨hn', hc'⟩ => covers.allStorage _ ha hn' hc'
    rw [hdeploy, hrecord.getPreStateAccount_eq ha]
    by_cases hd : (state.recordAccountRead message.currentTarget).accountDeployable
      message.currentTarget = true <;>
    by_cases hg : fork ≥ .glamsterdam ∧ (state.recordAccountRead
      message.currentTarget).getPreStateAccount message.currentTarget = EMPTY_ACCOUNT <;>
    cases charged <;> simp only [hd, hg, ↓reduceIte] <;>
    exact ⟨rfl, hrecord⟩
  | some target =>
    rw [prepareFirstFrame_call htarget] at hreads ⊢
    rw [prepareFirstFrame_call htarget]
    unfold applyAuthorizations at hreads ⊢
    have hfold := foldlM_applyAuthorization_agrees (fork := fork) (chainId := chainId) covers auths
      (⟨state, substate.accessedAddresses, 0, GasMeter.start message.gas message.reservoir, paid,
        ∅⟩ : Delegations Meter) other hagree hparent horigin
    dsimp only at hfold
    cases hf : List.foldlM (applyAuthorization fork chainId)
      (⟨state, substate.accessedAddresses, 0, GasMeter.start message.gas message.reservoir, paid,
        ∅⟩ : Delegations Meter) auths with
    | error er =>
      obtain ⟨e, read⟩ := er
      rw [hf] at hreads hfold
      have hfold := hfold hreads
      cases hf2 : List.foldlM (applyAuthorization fork chainId)
        (⟨other, substate.accessedAddresses, 0, GasMeter.start message.gas message.reservoir, paid,
          ∅⟩ : Delegations Meter) auths with
      | error er' =>
        rw [hf2] at hfold
        exact hfold
      | ok _ =>
        rw [hf2] at hfold
        exact hfold.elim
    | ok done =>
      rw [hf] at hreads hfold
      have hk : KeepsCodeOrigin state done.state := keepsCodeOrigin_applyAuthorizations hf
      have hfold := hfold (ReadsIn.of_readsLe
        ((readsLe_recordAccountRead _ target).trans (readsLe_callFrame done)) hreads)
      cases hf2 : List.foldlM (applyAuthorization fork chainId)
        (⟨other, substate.accessedAddresses, 0, GasMeter.start message.gas message.reservoir, paid,
          ∅⟩ : Delegations Meter) auths with
      | error _ =>
        rw [hf2] at hfold
        exact hfold.elim
      | ok done' =>
        rw [hf2] at hfold
        obtain ⟨hsame, hagree'⟩ := hfold
        show FramesAgree account allStorage slot code (callFrame message target substate done)
          (callFrame message target substate done')
        rw [hsame]
        exact callFrame_framesAgree covers hagree' (horigin.of_keepsCodeOrigin hk) hreads

/-! ## The address and the output of a frame -/

/-- The first frame runs at the same address as its message. -/
private theorem currentTarget_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame chainId message state substate auths paid = .ok first) :
    first.message.currentTarget = message.currentTarget := by
  unfold prepareFirstFrame at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  all_goals
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      simp only [Except.ok.injEq] at h
      subst h
      rfl

/-- The output of a frame with another state is the output with that state. -/
private theorem ofFrame_withState (evm : Evm fork Meter) (state : TransactionState)
    (refund : Nat) (touched : Std.ExtTreeSet Address) :
    CallOutput.ofFrame { evm with state } refund touched =
      { CallOutput.ofFrame evm refund touched with state } := by
  unfold CallOutput.ofFrame
  dsimp only
  split <;> rfl

end Helpers

/-! ## The first frame -/

/-- A preparation that ends with its reads in the sets gives the same frame on an agreeing state.

The two frames differ only in their states, which agree.

The sets must cover the block, which the first state must have as its parent.

The code hashes of the first state must come from the block or from writes.

The first state must have no new deployment candidate. -/
theorem prepareFirstFrame_agrees {block : BlockState} {account allStorage : Address → Prop}
    {slot : Address → Bytes32 → Prop} {code : Hash32 → Prop}
    (covers : CoversBlock block account allStorage code) {chainId : Nat} {message : Message fork}
    {state other : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} (hagree : AgreesOn account allStorage slot code state other)
    (hparent : state.parent = block) (horigin : CodeOrigin block state)
    (hcandidates : NoNewCandidate block state) {first : FirstFrame fork Meter}
    (h : prepareFirstFrame chainId message state substate auths paid = .ok first)
    (hreads : ReadsIn account slot first.state) :
    ∃ first', prepareFirstFrame chainId message other substate auths paid = .ok first' ∧
      first' = { first with state := first'.state } ∧
      AgreesOn account allStorage slot code first.state first'.state := by
  have hfa := prepareFirstFrame_framesAgree covers (chainId := chainId) (message := message)
    (substate := substate) (auths := auths) (paid := paid) hagree hparent horigin hcandidates
    (by rw [h]; exact hreads)
  rw [h] at hfa
  cases h2 : prepareFirstFrame (Meter := Meter) chainId message other substate auths paid with
  | error _ =>
    rw [h2] at hfa
    exact hfa.elim
  | ok first' =>
    rw [h2] at hfa
    exact ⟨first', rfl, hfa⟩

/-- A preparation that stops with its reads in the sets stops alike on an agreeing state.

The error is the same, and the states it keeps agree.

The sets must cover the block, which the first state must have as its parent.

The code hashes of the first state must come from the block or from writes.

The first state must have no new deployment candidate. -/
theorem prepareFirstFrame_agrees_error {block : BlockState}
    {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
    {code : Hash32 → Prop} (covers : CoversBlock block account allStorage code) {chainId : Nat}
    {message : Message fork} {state other : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    (hagree : AgreesOn account allStorage slot code state other)
    (hparent : state.parent = block) (horigin : CodeOrigin block state)
    (hcandidates : NoNewCandidate block state) {e : EvmError} {read : TransactionState}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .error (e, read))
    (hreads : ReadsIn account slot read) :
    ∃ read', prepareFirstFrame (Meter := Meter) chainId message other substate auths paid =
        .error (e, read') ∧
      AgreesOn account allStorage slot code read read' := by
  have hfa := prepareFirstFrame_framesAgree covers (chainId := chainId) (message := message)
    (substate := substate) (auths := auths) (paid := paid) hagree hparent horigin hcandidates
    (by rw [h]; exact hreads)
  rw [h] at hfa
  cases h2 : prepareFirstFrame (Meter := Meter) chainId message other substate auths paid with
  | error er =>
    obtain ⟨e', read'⟩ := er
    rw [h2] at hfa
    obtain ⟨rfl, hread⟩ := hfa
    exact ⟨read', rfl, hread⟩
  | ok _ =>
    rw [h2] at hfa
    exact hfa.elim

/-! ## The message -/

/-- A message of a transaction with its reads in the sets gives the same output on agreeing states.

The two outputs differ only in their states, which agree.

The sets must cover the block, which the first state must have as its parent.

The code hashes of the first state must come from the block or from writes.

The first state must have no new deployment candidate.

A call must run at its recipient. -/
theorem processMessageCall_agrees [LawfulGasMeter Meter] {block : BlockState}
    {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
    {code : Hash32 → Prop} (covers : CoversBlock block account allStorage code) {chainId : Nat}
    {message : Message fork} {state other : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    (hagree : AgreesOn account allStorage slot code state other)
    (hparent : state.parent = block) (horigin : CodeOrigin block state)
    (hcandidates : NoNewCandidate block state)
    (recipient : ∀ target, message.target = some target → target = message.currentTarget)
    {output : CallOutput}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output)
    (hreads : ReadsIn account slot output.state) :
    ∃ output', processMessageCall (Meter := Meter) chainId message other substate auths paid =
        .ok output' ∧
      output' = { output with state := output'.state } ∧
      AgreesOn account allStorage slot code output.state output'.state := by
  unfold processMessageCall at h ⊢
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
    · rename_i halts
      cases h
      obtain ⟨read', h2, hread⟩ := prepareFirstFrame_agrees_error covers hagree hparent horigin
        hcandidates hprep ⟨hreads.account, hreads.slot⟩
      rw [h2]
      dsimp only
      simp only [halts, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, rfl, rfl, hagree.withReadsOf hread.tracker⟩
  · rw [hprep] at h
    dsimp only at h
    have horigin1 := horigin.of_keepsCodeOrigin (keepsCodeOrigin_prepareFirstFrame hprep)
    have hcandidates1 := noNewCandidate_prepareFirstFrame hcandidates hprep
    have hcurrent : first.message.currentTarget ∈ first.state.accountReads := by
      rw [currentTarget_prepareFirstFrame hprep]
      exact currentRead_prepareFirstFrame recipient hprep
    split at h
    · rename_i htarget
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [state_ofFrame] at hreads
      obtain ⟨first', h2, hsame, hfirst⟩ := prepareFirstFrame_agrees covers hagree hparent horigin
        hcandidates hprep (ReadsIn.of_readsLe (readsLe_processCreateMessage hrun) hreads)
      obtain ⟨⟨evm', used'⟩, hrun', hrest, hstate⟩ := processCreateMessage_agrees covers hfirst
        horigin1 hcandidates1 hcurrent hrun hreads
      dsimp only at hrest hstate hreads
      rw [h2]
      dsimp only
      rw [hsame]
      dsimp only
      rw [hrun']
      dsimp only [bind, Except.bind, pure, Except.pure]
      refine ⟨_, rfl, ?_, ?_⟩
      · rw [state_ofFrame, hrest, ofFrame_withState]
      · rw [state_ofFrame, state_ofFrame]
        exact hstate
    · rename_i target htarget
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [state_ofFrame] at hreads
      have hle := readsLe_processMessage hrun
      obtain ⟨first', h2, hsame, hfirst⟩ := prepareFirstFrame_agrees covers hagree hparent horigin
        hcandidates hprep (ReadsIn.of_readsLe hle hreads)
      obtain ⟨⟨evm', used'⟩, hrun', hrest, hstate⟩ := processMessage_agrees covers hfirst
        horigin1 hcandidates1 hcurrent hrun hreads
      dsimp only at hrest hstate hreads hle
      have ht : account target := by
        refine hreads.account _ (hle.accountReads _ ?_)
        rw [recipient target htarget, ← currentTarget_prepareFirstFrame hprep]
        exact hcurrent
      rw [h2]
      dsimp only
      rw [hsame]
      dsimp only
      rw [hrun']
      dsimp only [bind, Except.bind, pure, Except.pure]
      generalize evm'.state = s' at hrest hstate
      subst hrest
      refine ⟨_, rfl, ?_, ?_⟩
      · dsimp only
        rw [hstate.accountExistsAndIsEmpty_eq (.inr ht), ofFrame_withState]
      · rw [state_ofFrame, state_ofFrame]
        exact hstate

end EthLib.Execution.Transactions

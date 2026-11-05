module

public import EthLib.Base.Except
public import EthLib.Execution.Proofs.Evm.Delegation
public import EthLib.Execution.Proofs.State.Tracker
public import EthLib.Execution.Transactions.Authorization

/-!
# Proofs: the authorizations of a set code transaction

A valid authorization gives its authority the code it names and one more nonce.

That code delegates to the address of the authorization.

An authorization to the zero address clears the code of its authority instead.

Every other address keeps its account, or its absence of one.

An authorization for another chain, or with a nonce of `2^64 - 1`, changes nothing.

An authority that refuses an authorization, such as for a wrong nonce, is only marked accessed.

An authorization with no valid signature changes nothing.

A valid authorization gives back 12500 exactly when its authority already has an account.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm (delegatedAddress delegatedAddress_delegationIndicator)
open EthLib.Execution.State (EMPTY_CODE_HASH TransactionState)
open EthLib.Execution.State.TransactionState

variable {fork : Fork} {chainId : Nat} {done done' : Delegations} {auth : Authorization}
  {authority : Address}

/-! ## The code an authorization sets -/

/-- An authorization to the zero address sets no code. -/
theorem delegationCode_of_eq_null (h : auth.address = NULL_ADDRESS) :
    delegationCode auth = .empty := by
  simp only [delegationCode, h, ↓reduceIte]

/-- The code an authorization to another address sets delegates to that address. -/
theorem delegatedAddress_delegationCode (h : auth.address ≠ NULL_ADDRESS) :
    delegatedAddress (delegationCode auth) = some auth.address := by
  simp only [delegationCode, h, ↓reduceIte]
  exact delegatedAddress_delegationIndicator _

/-! ## A valid authorization -/

/-- Taking an authorization sets the code of the authority and adds one to its nonce.

Its balance is unchanged.

Every other address keeps its account, or its absence of one.

The refund is 12500 exactly when the authority has an account. -/
theorem delegate_eq_ok {state state' : TransactionState} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) :
    refund = (if state.accountExists authority then 12500 else 0) ∧
      state'.getAccount authority = { state.getAccount authority with
        nonce := (state.getAccount authority).nonce + 1
        codeHash := Cryptography.Hash.Keccak.keccak256 (delegationCode auth) } ∧
      ∀ other, other ≠ authority →
        state'.getAccountOptional other = state.getAccountOptional other := by
  obtain ⟨coded, hcode, h⟩ := bind_ok_iff.mp h
  obtain ⟨bumped, hnonce, h⟩ := bind_ok_iff.mp h
  cases h
  obtain ⟨hcode_self, hcode_other⟩ := getAccount_setCode hcode
  obtain ⟨hnonce_self, hnonce_other⟩ := getAccount_incrementNonce hnonce
  refine ⟨rfl, ?_, fun other hne => (hnonce_other other hne).trans (hcode_other other hne)⟩
  rw [hnonce_self, hcode_self]

/-- Taking an authorization leaves every other address with or without an account as before.

So it changes no refund of a later authorization for another authority. -/
theorem accountExists_delegate_of_ne {state state' : TransactionState} {refund : Nat}
    {other : Address} (h : delegate fork state authority auth = .ok (state', refund))
    (hne : other ≠ authority) : state'.accountExists other = state.accountExists other := by
  simp only [accountExists, (delegate_eq_ok h).2.2 other hne]

/-- Taking an authorization never fails. -/
theorem delegate_isOk (state : TransactionState) :
    ∃ result, delegate fork state authority auth = .ok result := by
  obtain ⟨coded, hcode⟩ := setCode_isOk fork state authority (delegationCode auth)
  obtain ⟨bumped, hnonce⟩ := incrementNonce_isOk fork coded authority
  simp only [delegate, hcode, hnonce, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
    exists_eq']

/-- An accepted authorization delegates the authority, marks it as accessed, and adds the refund. -/
theorem applyAuthorization_of_accepts (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (haccept : authorityAccepts done.state authority auth = .ok true) :
    applyAuthorization fork chainId done auth =
      (delegate fork done.state authority auth).map fun (state, refund) =>
        ⟨state, done.accessed.insert authority, done.refund + refund⟩ := by
  simp only [applyAuthorization, hscope, hrecover, ↓reduceIte, haccept, bind, Except.bind]
  cases delegate fork done.state authority auth <;> rfl

/-- After an accepted authorization to the zero address, the authority has no code. -/
theorem codeHash_applyAuthorization_of_eq_null (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (haccept : authorityAccepts done.state authority auth = .ok true)
    (hnull : auth.address = NULL_ADDRESS)
    (h : applyAuthorization fork chainId done auth = .ok done') :
    (done'.state.getAccount authority).codeHash = EMPTY_CODE_HASH := by
  rw [applyAuthorization_of_accepts hscope hrecover haccept] at h
  cases hdelegate : delegate fork done.state authority auth with
  | error e => simp [hdelegate, Except.map] at h
  | ok result =>
    simp only [hdelegate, Except.map, Except.ok.injEq] at h
    subst h
    rw [(delegate_eq_ok hdelegate).2.1, delegationCode_of_eq_null hnull]
    rfl

/-- An accepted authorization adds 12500 to the refund exactly when the authority has an account. -/
theorem refund_applyAuthorization_of_accepts (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (haccept : authorityAccepts done.state authority auth = .ok true)
    (h : applyAuthorization fork chainId done auth = .ok done') :
    done'.refund = done.refund + if done.state.accountExists authority then 12500 else 0 := by
  rw [applyAuthorization_of_accepts hscope hrecover haccept] at h
  cases hdelegate : delegate fork done.state authority auth with
  | error e => simp [hdelegate, Except.map] at h
  | ok result =>
    simp only [hdelegate, Except.map, Except.ok.injEq] at h
    subst h
    rw [(delegate_eq_ok hdelegate).1]

/-! ## A skipped authorization -/

/-- An authorization out of scope changes nothing. -/
theorem applyAuthorization_of_not_inScope (h : authorizationInScope chainId auth = false) :
    applyAuthorization fork chainId done auth = .ok done := by
  simp only [applyAuthorization, h, Bool.false_eq_true, ↓reduceIte]

/-- An authorization for another chain changes nothing. -/
theorem applyAuthorization_of_chainId_ne (hzero : auth.chainId.toNat ≠ 0)
    (hchain : auth.chainId.toNat ≠ chainId) :
    applyAuthorization fork chainId done auth = .ok done :=
  applyAuthorization_of_not_inScope (by simp [authorizationInScope, hzero, hchain])

/-- An authorization with no valid signature changes nothing. -/
theorem applyAuthorization_of_recoverAuthority_none (h : recoverAuthority auth = none) :
    applyAuthorization fork chainId done auth = .ok done := by
  unfold applyAuthorization
  split <;> simp only [h]

/-- An authorization that its authority refuses only marks the authority as accessed. -/
theorem applyAuthorization_of_refused (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (hrefuse : authorityAccepts done.state authority auth = .ok false) :
    applyAuthorization fork chainId done auth =
      .ok { done with accessed := done.accessed.insert authority } := by
  simp only [applyAuthorization, hscope, hrecover, ↓reduceIte, hrefuse, bind, Except.bind,
    Bool.false_eq_true, pure, Except.pure]

/-- An authority whose code can be read refuses an authorization with another nonce. -/
theorem authorityAccepts_of_nonce_ne {state : TransactionState} {code : ByteArray}
    (hcode : state.getCode (state.getAccount authority).codeHash = .ok code)
    (hnonce : (state.getAccount authority).nonce ≠ auth.nonce.toNat) :
    authorityAccepts state authority auth = .ok false := by
  simp [authorityAccepts, hcode, hnonce, bind, Except.bind, pure, Except.pure]

/-- An authorization with a wrong nonce only marks its authority as accessed.

The code of the authority must be readable.

A missing code makes the authorization fail with an error instead. -/
theorem applyAuthorization_of_nonce_ne {code : ByteArray}
    (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (hcode : done.state.getCode (done.state.getAccount authority).codeHash = .ok code)
    (hnonce : (done.state.getAccount authority).nonce ≠ auth.nonce.toNat) :
    applyAuthorization fork chainId done auth =
      .ok { done with accessed := done.accessed.insert authority } :=
  applyAuthorization_of_refused hscope hrecover (authorityAccepts_of_nonce_ne hcode hnonce)

end EthLib.Execution.Transactions

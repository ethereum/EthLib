module

public import EthLib.Base.Except
public import EthLib.Execution.Proofs.Evm.Call.Delegation
public import EthLib.Execution.Proofs.State.Frame
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

A parity of `y` above 1, `r` outside `[1, n - 1]` or `s` outside `[1, n / 2]` names no authority.

An out-of-range `yParity`, `r` or `s` changes nothing.

An out-of-range `yParity`, `r` or `s` leaves the state as it was, up to the records of reads.

The hash that an authority signs ignores the signature of the authorization.

Up to BPO5, a valid authorization gives back 12500 exactly when its authority has an account.

From Glamsterdam, an authority pays for its first write and its new indicator at most once.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Cryptography.Secp256k1
open EthLib.Execution.Evm (GasMeter delegatedAddress delegatedAddress_delegationIndicator)
open EthLib.Execution.State (EMPTY_CODE_HASH TransactionState)
open EthLib.Execution.State.TransactionState

variable {fork : Fork} {chainId : Nat} {Meter : Type} [GasMeter Meter]
  {done done' : Delegations Meter} {auth : Authorization} {authority : Address}

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

Up to BPO5, the refund is 12500 exactly when the authority has an account. -/
theorem delegate_eq_ok {state state' : TransactionState} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) :
    refund = (if fork < .glamsterdam ∧ state.accountExists authority then 12500 else 0) ∧
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

/-- A record of a read changes no answer of an authority. -/
theorem authorityAccepts_recordAccountRead (state : TransactionState) (address : Address) :
    authorityAccepts (state.recordAccountRead address) authority auth =
      authorityAccepts state authority auth := rfl

/-- Up to BPO5, an accepted authorization delegates and accesses the authority, and adds the refund.

The authority is read first, and an error comes with that state. -/
theorem applyAuthorization_of_accepts (hfork : fork < .glamsterdam)
    (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (haccept : authorityAccepts done.state authority auth = .ok true) :
    applyAuthorization fork chainId done auth =
      ((delegate fork (done.state.recordAccountRead authority) authority auth).mapError
          fun e => (.state e, done.state.recordAccountRead authority)).map
        fun (state, refund) =>
          { done with
            state := state
            accessed := done.accessed.insert authority
            refund := done.refund + refund } := by
  have hpre : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hfork
  simp only [applyAuthorization, payAuthorization, hpre, hscope, hrecover, ↓reduceIte,
    authorityAccepts_recordAccountRead, haccept, Except.mapError, bind, Except.bind]
  cases delegate fork (done.state.recordAccountRead authority) authority auth <;> rfl

/-- Up to BPO5, after an accepted authorization to the zero address, the authority has no code. -/
theorem codeHash_applyAuthorization_of_eq_null (hfork : fork < .glamsterdam)
    (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (haccept : authorityAccepts done.state authority auth = .ok true)
    (hnull : auth.address = NULL_ADDRESS)
    (h : applyAuthorization fork chainId done auth = .ok done') :
    (done'.state.getAccount authority).codeHash = EMPTY_CODE_HASH := by
  rw [applyAuthorization_of_accepts hfork hscope hrecover haccept] at h
  cases hdelegate : delegate fork (done.state.recordAccountRead authority) authority auth with
  | error e => simp [hdelegate, Except.map, Except.mapError] at h
  | ok result =>
    simp only [hdelegate, Except.map, Except.mapError, Except.ok.injEq] at h
    subst h
    rw [(delegate_eq_ok hdelegate).2.1, delegationCode_of_eq_null hnull]
    rfl

/-- Up to BPO5, an accepted authorization refunds 12500 exactly when its authority exists. -/
theorem refund_applyAuthorization_of_accepts (hfork : fork < .glamsterdam)
    (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (haccept : authorityAccepts done.state authority auth = .ok true)
    (h : applyAuthorization fork chainId done auth = .ok done') :
    done'.refund = done.refund + if done.state.accountExists authority then 12500 else 0 := by
  rw [applyAuthorization_of_accepts hfork hscope hrecover haccept] at h
  cases hdelegate : delegate fork (done.state.recordAccountRead authority) authority auth with
  | error e => simp [hdelegate, Except.map, Except.mapError] at h
  | ok result =>
    simp only [hdelegate, Except.map, Except.mapError, Except.ok.injEq] at h
    subst h
    rw [(delegate_eq_ok hdelegate).1]
    simp only [hfork, true_and]
    rfl

/-! ## The ranges of `yParity`, `r` and `s` -/

/-- A parity of `y` above 1 names no authority. -/
theorem recoverAuthority_yParity_gt (h : 1 < auth.yParity.toNat) :
    recoverAuthority auth = none := by
  have hy : ¬ (auth.yParity.toNat < 2 ∧ 0 < auth.r.toNat ∧ auth.r.toNat < Fn.modulus ∧
      0 < auth.s.toNat ∧ Ecdsa.isLowS auth.s.toNat = true) := by omega
  simp only [recoverAuthority, hy, ↓reduceIte]

/-- A first integer of 0 names no authority. -/
theorem recoverAuthority_r_zero (h : auth.r.toNat = 0) :
    recoverAuthority auth = none := by
  have hr : ¬ (auth.yParity.toNat < 2 ∧ 0 < auth.r.toNat ∧ auth.r.toNat < Fn.modulus ∧
      0 < auth.s.toNat ∧ Ecdsa.isLowS auth.s.toNat = true) := by omega
  simp only [recoverAuthority, hr, ↓reduceIte]

/-- A first integer of `n` or more names no authority. -/
theorem recoverAuthority_r_ge (h : Fn.modulus ≤ auth.r.toNat) :
    recoverAuthority auth = none := by
  have hr : ¬ (auth.yParity.toNat < 2 ∧ 0 < auth.r.toNat ∧ auth.r.toNat < Fn.modulus ∧
      0 < auth.s.toNat ∧ Ecdsa.isLowS auth.s.toNat = true) := by omega
  simp only [recoverAuthority, hr, ↓reduceIte]

/-- A first integer outside `[1, n - 1]` names no authority. -/
theorem recoverAuthority_r_out (h : auth.r.toNat = 0 ∨ Fn.modulus ≤ auth.r.toNat) :
    recoverAuthority auth = none :=
  h.elim recoverAuthority_r_zero recoverAuthority_r_ge

/-- A second integer of 0 names no authority. -/
theorem recoverAuthority_s_zero (h : auth.s.toNat = 0) :
    recoverAuthority auth = none := by
  have hs : ¬ (auth.yParity.toNat < 2 ∧ 0 < auth.r.toNat ∧ auth.r.toNat < Fn.modulus ∧
      0 < auth.s.toNat ∧ Ecdsa.isLowS auth.s.toNat = true) := by omega
  simp only [recoverAuthority, hs, ↓reduceIte]

/-- A second integer above `n / 2` names no authority. -/
theorem recoverAuthority_high_s (h : Fn.modulus / 2 < auth.s.toNat) :
    recoverAuthority auth = none := by
  have hs : ¬ (auth.yParity.toNat < 2 ∧ 0 < auth.r.toNat ∧ auth.r.toNat < Fn.modulus ∧
      0 < auth.s.toNat ∧ Ecdsa.isLowS auth.s.toNat = true) := by
    simp only [Ecdsa.isLowS, decide_eq_true_eq]
    omega
  simp only [recoverAuthority, hs, ↓reduceIte]

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

/-- An out-of-range `yParity`, `r` or `s` changes nothing. -/
theorem applyAuthorization_of_out_of_range
    (h : 1 < auth.yParity.toNat ∨ auth.r.toNat = 0 ∨ Fn.modulus ≤ auth.r.toNat ∨
      auth.s.toNat = 0 ∨ Fn.modulus / 2 < auth.s.toNat) :
    applyAuthorization fork chainId done auth = .ok done := by
  apply applyAuthorization_of_recoverAuthority_none
  rcases h with hy | hr0 | hrge | hs0 | hshigh
  · exact recoverAuthority_yParity_gt hy
  · exact recoverAuthority_r_zero hr0
  · exact recoverAuthority_r_ge hrge
  · exact recoverAuthority_s_zero hs0
  · exact recoverAuthority_high_s hshigh

/-- An out-of-range `yParity`, `r` or `s` leaves the state as it was, up to the records of reads. -/
theorem sameOutside_applyAuthorization_of_out_of_range
    (h : 1 < auth.yParity.toNat ∨ auth.r.toNat = 0 ∨ Fn.modulus ≤ auth.r.toNat ∨
      auth.s.toNat = 0 ∨ Fn.modulus / 2 < auth.s.toNat)
    (happly : applyAuthorization fork chainId done auth = .ok done') :
    SameOutside [] done.state done'.state := by
  rw [applyAuthorization_of_out_of_range h, Except.ok.injEq] at happly
  subst happly
  exact SameOutside.refl [] done.state

/-- An authorization that its authority refuses only marks the authority as accessed and read. -/
theorem applyAuthorization_of_refused (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (hrefuse : authorityAccepts done.state authority auth = .ok false) :
    applyAuthorization fork chainId done auth =
      .ok { done with
        state := done.state.recordAccountRead authority
        accessed := done.accessed.insert authority } := by
  simp only [applyAuthorization, hscope, hrecover, ↓reduceIte, authorityAccepts_recordAccountRead,
    hrefuse, Except.mapError, bind, Except.bind, Bool.false_eq_true, pure, Except.pure]

/-- An authority whose code can be read refuses an authorization with another nonce. -/
theorem authorityAccepts_of_nonce_ne {state : TransactionState} {code : ByteArray}
    (hcode : state.getCode (state.getAccount authority).codeHash = .ok code)
    (hnonce : (state.getAccount authority).nonce ≠ auth.nonce.toNat) :
    authorityAccepts state authority auth = .ok false := by
  simp [authorityAccepts, hcode, hnonce, bind, Except.bind, pure, Except.pure]

/-- An authorization with a wrong nonce only marks its authority as accessed and read.

The code of the authority must be readable.

A missing code makes the authorization fail with an error instead. -/
theorem applyAuthorization_of_nonce_ne {code : ByteArray}
    (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (hcode : done.state.getCode (done.state.getAccount authority).codeHash = .ok code)
    (hnonce : (done.state.getAccount authority).nonce ≠ auth.nonce.toNat) :
    applyAuthorization fork chainId done auth =
      .ok { done with
        state := done.state.recordAccountRead authority
        accessed := done.accessed.insert authority } :=
  applyAuthorization_of_refused hscope hrecover (authorityAccepts_of_nonce_ne hcode hnonce)

/-! ## What an authorization pays -/

/-- Up to BPO5, an accepted authorization pays nothing before it applies. -/
theorem payAuthorization_of_lt_glamsterdam (hfork : fork < .glamsterdam) :
    payAuthorization fork done authority auth = .ok done := by
  have hpre : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hfork
  simp only [payAuthorization, hpre, ↓reduceIte]

/-- From Glamsterdam, an authorization that pays records the write to its authority as paid.

It also records the authority as delegated when it sets a delegation indicator.

So a later authorization for the same authority pays neither again. -/
theorem mem_payAuthorization (hfork : .glamsterdam ≤ fork)
    (h : payAuthorization fork done authority auth = .ok done') :
    authority ∈ done'.paidWrites ∧
      (auth.address ≠ NULL_ADDRESS → authority ∈ done'.delegated) ∧
      done'.state = done.state := by
  simp only [payAuthorization, hfork, ↓reduceIte] at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  cases h
  refine ⟨Std.ExtTreeSet.mem_insert_self, fun hset => ?_, rfl⟩
  simp only [ne_eq, hset, not_false_eq_true, ↓reduceIte]
  exact Std.ExtTreeSet.mem_insert_self

/-- From Glamsterdam, an existing authority whose write and indicator are paid pays nothing more.

The authority's code before the transaction must be readable. -/
theorem meter_payAuthorization_of_paid {code : ByteArray} (hfork : .glamsterdam ≤ fork)
    (hexists : done.state.accountExists authority = true)
    (hpaid : authority ∈ done.paidWrites)
    (hset : auth.address = NULL_ADDRESS ∨ authority ∈ done.delegated)
    (hcode : done.state.getCode (done.state.getPreStateAccount authority).codeHash = .ok code) :
    ∃ done', payAuthorization fork done authority auth = .ok done' ∧ done'.meter = done.meter := by
  rcases hset with hnull | hdel
  · simp [payAuthorization, chargeAuthorization, hfork, hexists, hpaid, hcode, hnull,
      Except.mapError, bind, Except.bind, pure, Except.pure]
  · simp [payAuthorization, chargeAuthorization, hfork, hexists, hpaid, hcode, hdel,
      Except.mapError, bind, Except.bind, pure, Except.pure]

/-! ## The hash that an authority signs -/

/-- The hash that an authority signs ignores the parity, `r` and `s`. -/
theorem authorizationHash_signature (auth : Authorization) (yParity : UInt8) (r s : U256) :
    authorizationHash { auth with yParity := yParity, r := r, s := s } = authorizationHash auth :=
  rfl

end EthLib.Execution.Transactions

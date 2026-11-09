module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Evm.Call.Delegation
public import EthLib.Execution.Proofs.Evm.Gas.StateGas
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

Here `n` is the order of the secp256k1 group.

Such an authorization changes nothing.

The hash that an authority signs ignores the signature of the authorization.

Up to BPO5, a valid authorization gives back 12500 exactly when its authority has an account.

From Glamsterdam, an authority pays for its first write and its new indicator at most once.

An authorization that succeeds is skipped, refused, or accepted after it pays and delegates.

An authority whose code is neither empty nor a delegation indicator refuses every authorization.

The authorizations keep the account, storage and transient storage of an address with such code.

They keep that code under its hash.

This needs one hypothesis: no authorization sets a code whose hash is the code hash of the address.

Up to BPO5, the authorizations keep the meter.

The authorizations succeed when the state holds the code of every account.

From Glamsterdam, the state must also hold the code of every account before the transaction.

From Glamsterdam, the meter must also hold 227790 execution gas for each authorization.

From Glamsterdam, each charge of at most the gas left must also succeed and take at most its amount.

That holds for the meter up to BPO5 and for the meter of EIP-8037.

Each authorization then takes at most 227790 execution gas.

The theorems that the authorizations succeed hold for any recovery of an authority.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Cryptography.Secp256k1
open EthLib.Execution.Evm (GasMeter delegatedAddress delegatedAddress_delegationIndicator
  isValidDelegation)
open EthLib.Execution.Evm.GasCosts (ACCOUNT_WRITE AUTH_BASE_STATE_GAS NEW_ACCOUNT_STATE_GAS)
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
  obtain ⟨hcode_self, -⟩ := getAccount_setCode hcode
  obtain ⟨hnonce_self, -⟩ := getAccount_incrementNonce hnonce
  refine ⟨rfl, ?_, fun other hne =>
    ((sameOutside_setCode hcode).trans (sameOutside_incrementNonce hnonce) other
      (by simpa using hne)).1⟩
  rw [hnonce_self, hcode_self]

/-- Taking an authorization leaves every other address with or without an account as before.

So it changes no refund of a later authorization for another authority. -/
theorem accountExists_delegate_of_ne {state state' : TransactionState} {refund : Nat}
    {other : Address} (h : delegate fork state authority auth = .ok (state', refund))
    (hne : other ≠ authority) : state'.accountExists other = state.accountExists other := by
  simp only [accountExists, (delegate_eq_ok h).2.2 other hne]

/-- Taking an authorization never fails.

Up to BPO5, the refund is 12500 exactly when the authority has an account. -/
theorem delegate_isOk (state : TransactionState) :
    ∃ state', delegate fork state authority auth = .ok (state',
      if fork < .glamsterdam ∧ state.accountExists authority then 12500 else 0) := by
  obtain ⟨coded, hcode⟩ := setCode_isOk fork state authority (delegationCode auth)
  obtain ⟨bumped, hnonce⟩ := incrementNonce_isOk fork coded authority
  exact ⟨bumped, by simp only [delegate, hcode, hnonce, bind, Except.bind, pure, Except.pure]; rfl⟩

/-- Taking an authorization changes no account, storage or transient storage but the authority's.

It also keeps the block of the state. -/
theorem sameOutside_delegate {state state' : TransactionState} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) :
    SameOutside [authority] state state' ∧ state'.parent = state.parent := by
  obtain ⟨coded, hcode, h⟩ := bind_ok_iff.mp h
  obtain ⟨bumped, hnonce, h⟩ := bind_ok_iff.mp h
  cases h
  exact ⟨((sameOutside_setCode hcode).trans (sameOutside_incrementNonce hnonce)).mono (by simp),
    (parent_incrementNonce hnonce).trans (parent_setCode hcode)⟩

/-- Taking an authorization keeps the code under every hash but the hash of the code it sets. -/
theorem getCode_delegate_of_ne {state state' : TransactionState} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) {codeHash : Hash32}
    (hne : codeHash ≠ Cryptography.Hash.Keccak.keccak256 (delegationCode auth)) :
    state'.getCode codeHash = state.getCode codeHash := by
  obtain ⟨coded, hcode, h⟩ := bind_ok_iff.mp h
  obtain ⟨bumped, hnonce, h⟩ := bind_ok_iff.mp h
  cases h
  rw [getCode_modifyState hnonce, getCode_setCode_of_ne hcode hne]

/-- Taking an authorization stores the code it sets under the hash of that code.

The hash must differ from the hash of the empty code. -/
theorem getCode_delegate_self {state state' : TransactionState} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund))
    (hne : Cryptography.Hash.Keccak.keccak256 (delegationCode auth) ≠ EMPTY_CODE_HASH) :
    state'.getCode (Cryptography.Hash.Keccak.keccak256 (delegationCode auth)) =
      .ok (delegationCode auth) := by
  obtain ⟨coded, hcode, h⟩ := bind_ok_iff.mp h
  obtain ⟨bumped, hnonce, h⟩ := bind_ok_iff.mp h
  cases h
  rw [getCode_modifyState hnonce, getCode_setCode_self hcode hne]

/-! ## What an authorization pays -/

/-- Up to BPO5, an accepted authorization pays nothing before it applies. -/
theorem payAuthorization_of_lt_glamsterdam (hfork : fork < .glamsterdam) :
    payAuthorization fork done authority auth = .ok done := by
  have hpre : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hfork
  simp only [payAuthorization, hpre, ↓reduceIte]

/-- From Glamsterdam, an authorization pays exactly when its charge succeeds.

It then takes the meter that the charge leaves, and records the write to its authority as paid.

It records the authority as delegated when the authorization is not to the zero address.

It keeps the state, the accesses and the refund. -/
theorem payAuthorization_eq_ok_iff (hfork : .glamsterdam ≤ fork) :
    payAuthorization fork done authority auth = .ok done' ↔
      ∃ meter, chargeAuthorization done authority auth = .ok meter ∧
        done' = { done with
          meter
          paidWrites := done.paidWrites.insert authority
          delegated := if auth.address ≠ NULL_ADDRESS then done.delegated.insert authority
            else done.delegated } := by
  simp only [payAuthorization, hfork, ↓reduceIte]
  constructor
  · intro h
    obtain ⟨meter, hmeter, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨meter, hmeter, rfl⟩
  · rintro ⟨meter, hmeter, rfl⟩
    simp only [hmeter, bind, Except.bind, pure, Except.pure]

/-- The payment of an authorization keeps the state, the accesses and the refund, at every fork. -/
theorem state_payAuthorization (h : payAuthorization fork done authority auth = .ok done') :
    done'.state = done.state ∧ done'.accessed = done.accessed ∧ done'.refund = done.refund := by
  by_cases hfork : .glamsterdam ≤ fork
  · obtain ⟨meter, -, rfl⟩ := (payAuthorization_eq_ok_iff hfork).mp h
    exact ⟨rfl, rfl, rfl⟩
  · rw [payAuthorization_of_lt_glamsterdam (Nat.lt_of_not_le hfork), Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩

/-- From Glamsterdam, an authorization that pays records the write to its authority as paid.

It also records the authority as delegated when it sets a delegation indicator.

So a later authorization for the same authority pays neither again. -/
theorem mem_payAuthorization (hfork : .glamsterdam ≤ fork)
    (h : payAuthorization fork done authority auth = .ok done') :
    authority ∈ done'.paidWrites ∧
      (auth.address ≠ NULL_ADDRESS → authority ∈ done'.delegated) ∧
      done'.state = done.state := by
  obtain ⟨_, -, rfl⟩ := (payAuthorization_eq_ok_iff hfork).mp h
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

/-- A record of a read changes no answer of an authority. -/
theorem authorityAccepts_recordAccountRead (state : TransactionState) (address : Address) :
    authorityAccepts (state.recordAccountRead address) authority auth =
      authorityAccepts state authority auth := rfl

/-- An accepted authorization reads and accesses the authority, pays, delegates and adds the refund.

Here `paid` is what the payment leaves, from the delegations with that read and that access.

An error comes with the state that has the read. -/
theorem applyAuthorization_of_accepts_of_pay {paid : Delegations Meter}
    (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (haccept : authorityAccepts done.state authority auth = .ok true)
    (hpay : payAuthorization fork { done with
      state := done.state.recordAccountRead authority
      accessed := done.accessed.insert authority } authority auth = .ok paid) :
    applyAuthorization fork chainId done auth =
      ((delegate fork paid.state authority auth).mapError
          fun e => (.state e, done.state.recordAccountRead authority)).map
        fun (state, refund) => { paid with state := state, refund := paid.refund + refund } := by
  simp only [applyAuthorization, hscope, hrecover, ↓reduceIte, authorityAccepts_recordAccountRead,
    haccept, hpay, Except.mapError, bind, Except.bind]
  cases delegate fork paid.state authority auth <;> rfl

/-- An accepted authorization whose payment fails stops the authorizations with that error.

The error comes with the state that has the read of the authority. -/
theorem applyAuthorization_of_payAuthorization_error {e : Evm.EvmError}
    (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (haccept : authorityAccepts done.state authority auth = .ok true)
    (hpay : payAuthorization fork { done with
      state := done.state.recordAccountRead authority
      accessed := done.accessed.insert authority } authority auth = .error e) :
    applyAuthorization fork chainId done auth =
      .error (e, done.state.recordAccountRead authority) := by
  simp only [applyAuthorization, hscope, hrecover, ↓reduceIte, authorityAccepts_recordAccountRead,
    haccept, hpay, Except.mapError, bind, Except.bind]

/-- An authority whose code cannot be read stops the authorizations with that error.

The error comes with the state that has the read of the authority. -/
theorem applyAuthorization_of_authorityAccepts_error {e : State.StateError}
    (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (haccept : authorityAccepts done.state authority auth = .error e) :
    applyAuthorization fork chainId done auth =
      .error (.state e, done.state.recordAccountRead authority) := by
  have hread : authorityAccepts (done.state.recordAccountRead authority) authority auth =
      .error e := haccept
  simp only [applyAuthorization, hscope, hrecover, ↓reduceIte, hread, Except.mapError, bind,
    Except.bind]
  rfl

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
  rw [applyAuthorization_of_accepts_of_pay hscope hrecover haccept
    (payAuthorization_of_lt_glamsterdam hfork)]

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

/-! ## The ranges of the parity of `y`, `r` and `s` -/

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

/-- A parity of `y`, an `r` or an `s` out of range changes nothing. -/
theorem applyAuthorization_of_out_of_range
    (h : 1 < auth.yParity.toNat ∨ auth.r.toNat = 0 ∨ Fn.modulus ≤ auth.r.toNat ∨
      auth.s.toNat = 0 ∨ Fn.modulus / 2 < auth.s.toNat) :
    applyAuthorization fork chainId done auth = .ok done := by
  apply applyAuthorization_of_recoverAuthority_none
  rcases h with hy | hr | hr | hs0 | hshigh
  · exact recoverAuthority_yParity_gt hy
  · exact recoverAuthority_r_out (.inl hr)
  · exact recoverAuthority_r_out (.inr hr)
  · exact recoverAuthority_s_zero hs0
  · exact recoverAuthority_high_s hshigh

/-- A parity of `y`, an `r` or an `s` out of range leaves the state and its records as they were. -/
theorem eq_of_applyAuthorization_of_out_of_range
    (h : 1 < auth.yParity.toNat ∨ auth.r.toNat = 0 ∨ Fn.modulus ≤ auth.r.toNat ∨
      auth.s.toNat = 0 ∨ Fn.modulus / 2 < auth.s.toNat)
    (happly : applyAuthorization fork chainId done auth = .ok done') :
    done' = done := by
  rw [applyAuthorization_of_out_of_range h, Except.ok.injEq] at happly
  exact happly.symm

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

/-- An authority refuses every authorization when its code is neither empty nor an indicator.

Its code must be readable. -/
theorem authorityAccepts_of_code {state : TransactionState} {code : ByteArray}
    (hcode : state.getCode (state.getAccount authority).codeHash = .ok code)
    (hsize : code.size ≠ 0) (hindicator : isValidDelegation code = false) :
    authorityAccepts state authority auth = .ok false := by
  simp [authorityAccepts, hcode, hsize, hindicator, bind, Except.bind, pure, Except.pure]

/-- An authorization whose authority has real code only marks the authority as accessed and read.

Real code is neither empty nor a delegation indicator. -/
theorem applyAuthorization_of_code {code : ByteArray}
    (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (hcode : done.state.getCode (done.state.getAccount authority).codeHash = .ok code)
    (hsize : code.size ≠ 0) (hindicator : isValidDelegation code = false) :
    applyAuthorization fork chainId done auth =
      .ok { done with
        state := done.state.recordAccountRead authority
        accessed := done.accessed.insert authority } :=
  applyAuthorization_of_refused hscope hrecover (authorityAccepts_of_code hcode hsize hindicator)

/-! ## Every authorization that succeeds -/

/-- An authorization that succeeds is skipped, refused or accepted.

A skipped authorization keeps the delegations.

A refused one only marks its recovered authority as accessed and read.

An accepted one pays, then delegates the authority and adds the refund. -/
theorem applyAuthorization_cases (h : applyAuthorization fork chainId done auth = .ok done') :
    done' = done ∨ ∃ authority, authorizationInScope chainId auth = true ∧
      recoverAuthority auth = some authority ∧
      ((authorityAccepts done.state authority auth = .ok false ∧
          done' = { done with
            state := done.state.recordAccountRead authority
            accessed := done.accessed.insert authority }) ∨
        (authorityAccepts done.state authority auth = .ok true ∧
          ∃ paid state refund,
            payAuthorization fork { done with
              state := done.state.recordAccountRead authority
              accessed := done.accessed.insert authority } authority auth = .ok paid ∧
            delegate fork paid.state authority auth = .ok (state, refund) ∧
            done' = { paid with state := state, refund := paid.refund + refund })) := by
  cases hscope : authorizationInScope chainId auth
  · rw [applyAuthorization_of_not_inScope hscope] at h
    exact .inl (Except.ok.inj h).symm
  cases hrecover : recoverAuthority auth with
  | none =>
    rw [applyAuthorization_of_recoverAuthority_none hrecover] at h
    exact .inl (Except.ok.inj h).symm
  | some authority =>
    refine .inr ⟨authority, rfl, rfl, ?_⟩
    cases haccept : authorityAccepts done.state authority auth with
    | error e =>
      rw [applyAuthorization_of_authorityAccepts_error hscope hrecover haccept] at h
      cases h
    | ok accepts =>
      cases accepts
      · rw [applyAuthorization_of_refused hscope hrecover haccept] at h
        exact .inl ⟨rfl, (Except.ok.inj h).symm⟩
      · refine .inr ⟨rfl, ?_⟩
        cases hpay : payAuthorization fork { done with
            state := done.state.recordAccountRead authority
            accessed := done.accessed.insert authority } authority auth with
        | error e =>
          rw [applyAuthorization_of_payAuthorization_error hscope hrecover haccept hpay] at h
          cases h
        | ok paid =>
          obtain ⟨state, hdelegate⟩ := delegate_isOk (fork := fork) (authority := authority)
            (auth := auth) paid.state
          rw [applyAuthorization_of_accepts_of_pay hscope hrecover haccept hpay, hdelegate] at h
          exact ⟨paid, state, _, rfl, hdelegate, (Except.ok.inj h).symm⟩

/-! ## An address with real code

Real code is neither empty nor a delegation indicator.

An address with real code refuses every authorization, so the authorizations keep it.

It needs one hypothesis: no authorization sets a code whose hash is the code hash of the address.

When the state stores each code under its own hash, only a collision of Keccak-256 breaks it.

A code that an authorization sets is stored under its hash, over any code with that hash. -/

/-- An authorization keeps the account, storage and transient storage of an address with real code.

It also keeps that code under its hash.

The hash of the code that the authorization sets must not be the code hash of the address. -/
theorem applyAuthorization_keeps {address : Address} {code : ByteArray}
    (h : applyAuthorization fork chainId done auth = .ok done')
    (hcode : done.state.getCode (done.state.getAccount address).codeHash = .ok code)
    (hsize : code.size ≠ 0) (hindicator : isValidDelegation code = false)
    (hhash : Cryptography.Hash.Keccak.keccak256 (delegationCode auth) ≠
      (done.state.getAccount address).codeHash) :
    done'.state.getAccountOptional address = done.state.getAccountOptional address ∧
      (∀ key, done'.state.getStorage address key = done.state.getStorage address key) ∧
      (∀ key, done'.state.getTransientStorage address key =
        done.state.getTransientStorage address key) ∧
      done'.state.getCode (done.state.getAccount address).codeHash = .ok code := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨haccept, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact ⟨rfl, fun _ => rfl, fun _ => rfl, hcode⟩
  · exact ⟨rfl, fun _ => rfl, fun _ => rfl, hcode⟩
  · have hne : address ≠ authority := by
      rintro rfl
      rw [authorityAccepts_of_code hcode hsize hindicator] at haccept
      cases haccept
    obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    obtain ⟨haccount, hstorage, htransient⟩ :=
      (sameOutside_delegate hdelegate).1 address (by simpa using hne)
    rw [hstate] at haccount hstorage htransient
    refine ⟨haccount, hstorage, htransient, ?_⟩
    rw [getCode_delegate_of_ne hdelegate (Ne.symm hhash), hstate]
    exact hcode

/-- The authorizations of a list keep an address with real code.

They keep its account, storage and transient storage, and that code under its hash.

No authorization of the list may set a code whose hash is the code hash of the address. -/
theorem foldlM_applyAuthorization_keeps {address : Address} {code : ByteArray}
    (hsize : code.size ≠ 0) (hindicator : isValidDelegation code = false) :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      start.state.getCode (start.state.getAccount address).codeHash = .ok code →
      (∀ auth ∈ auths, Cryptography.Hash.Keccak.keccak256 (delegationCode auth) ≠
        (start.state.getAccount address).codeHash) →
      done.state.getAccountOptional address = start.state.getAccountOptional address ∧
        (∀ key, done.state.getStorage address key = start.state.getStorage address key) ∧
        (∀ key, done.state.getTransientStorage address key =
          start.state.getTransientStorage address key) ∧
        done.state.getCode (start.state.getAccount address).codeHash = .ok code
  | [], _, _, h, hcode, _ => by
    cases h
    exact ⟨rfl, fun _ => rfl, fun _ => rfl, hcode⟩
  | auth :: rest, start, done, h, hcode, hhash => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    obtain ⟨haccount, hstorage, htransient, hcode'⟩ :=
      applyAuthorization_keeps hnext hcode hsize hindicator (hhash auth List.mem_cons_self)
    have hsame : next.state.getAccount address = start.state.getAccount address := by
      simp only [getAccount, haccount]
    rw [← hsame] at hcode'
    obtain ⟨haccount', hstorage', htransient', hcode''⟩ :=
      foldlM_applyAuthorization_keeps hsize hindicator h hcode'
        (fun a ha => hsame ▸ hhash a (List.mem_cons_of_mem _ ha))
    exact ⟨haccount'.trans haccount, fun key => (hstorage' key).trans (hstorage key),
      fun key => (htransient' key).trans (htransient key), hsame ▸ hcode''⟩

/-! ## The meter up to BPO5 -/

/-- Up to BPO5, an authorization keeps the meter. -/
theorem meter_applyAuthorization_of_lt_glamsterdam (hfork : fork < .glamsterdam)
    (h : applyAuthorization fork chainId done auth = .ok done') : done'.meter = done.meter := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, -, rfl⟩⟩
  · rfl
  · rfl
  · rw [payAuthorization_of_lt_glamsterdam hfork, Except.ok.injEq] at hpay
    subst hpay
    rfl

/-- Up to BPO5, the authorizations of a list keep the meter. -/
theorem meter_foldlM_applyAuthorization_of_lt_glamsterdam (hfork : fork < .glamsterdam) :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done → done.meter = start.meter :=
  fun {_ start _} => foldlM_ok_invariant (fun next => next.meter = start.meter)
    (fun _ _ _ hheld hstep => (meter_applyAuthorization_of_lt_glamsterdam hfork hstep).trans hheld)
    rfl

/-! ## The authorizations succeed

No statement here assumes anything of the recovery of an authority.

The state must hold the code of every account.

From Glamsterdam, it must also hold the code of every account before the transaction. -/

/-- Whether the state holds the code of every account. -/
def HasCodes (state : TransactionState) : Prop :=
  ∀ address, ∃ code, state.getCode (state.getAccount address).codeHash = .ok code

/-- Whether the state holds the code of every account before the transaction. -/
def HasPreCodes (state : TransactionState) : Prop :=
  ∀ address, ∃ code, state.getCode (state.getPreStateAccount address).codeHash = .ok code

/-- Taking an authorization keeps every code that the state holds. -/
theorem exists_getCode_delegate {state state' : TransactionState} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) {codeHash : Hash32}
    (hcode : ∃ code, state.getCode codeHash = .ok code) :
    ∃ code, state'.getCode codeHash = .ok code := by
  obtain ⟨code, hcode⟩ := hcode
  by_cases hset : codeHash = Cryptography.Hash.Keccak.keccak256 (delegationCode auth)
  · by_cases hempty : codeHash = EMPTY_CODE_HASH
    · exact ⟨.empty, by simp [getCode, hempty]⟩
    · subst hset
      exact ⟨_, getCode_delegate_self h hempty⟩
  · exact ⟨code, (getCode_delegate_of_ne h hset).trans hcode⟩

/-- Taking an authorization keeps the code of every account in the state. -/
theorem hasCodes_delegate {state state' : TransactionState} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) (hcodes : HasCodes state) :
    HasCodes state' := by
  intro address
  by_cases hself : address = authority
  · subst hself
    have hhash : (state'.getAccount address).codeHash =
        Cryptography.Hash.Keccak.keccak256 (delegationCode auth) := by
      rw [(delegate_eq_ok h).2.1]
    rw [hhash]
    by_cases hempty : Cryptography.Hash.Keccak.keccak256 (delegationCode auth) = EMPTY_CODE_HASH
    · exact ⟨.empty, by simp [getCode, hempty]⟩
    · exact ⟨_, getCode_delegate_self h hempty⟩
  · have hother : state'.getAccount address = state.getAccount address := by
      simp only [getAccount, ((sameOutside_delegate h).1 address (by simpa using hself)).1]
    rw [hother]
    exact exists_getCode_delegate h (hcodes address)

/-- Taking an authorization keeps the code of every account before the transaction in the state. -/
theorem hasPreCodes_delegate {state state' : TransactionState} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) (hpre : HasPreCodes state) :
    HasPreCodes state' := by
  intro address
  have hother : state'.getPreStateAccount address = state.getPreStateAccount address := by
    simp only [getPreStateAccount, getPreStateAccountOptional, (sameOutside_delegate h).2]
  rw [hother]
  exact exists_getCode_delegate h (hpre address)

/-- An authorization keeps the code of every account before the transaction in the state. -/
theorem hasPreCodes_applyAuthorization (h : applyAuthorization fork chainId done auth = .ok done')
    (hpre : HasPreCodes done.state) : HasPreCodes done'.state := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact hpre
  · exact hpre
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    exact hasPreCodes_delegate hdelegate (by rw [hstate]; exact hpre)

/-- One authorization succeeds when each payment it may make succeeds.

The state must hold the code of every account, and the result keeps that fact.

The resulting meter meets `Q` when the meter before and the meter after each payment meet it. -/
theorem applyAuthorization_isOk_of_pay (Q : Meter → Prop) (hQ : Q done.meter)
    (hcodes : HasCodes done.state)
    (hpay : ∀ authority, ∃ paid, payAuthorization fork { done with
      state := done.state.recordAccountRead authority
      accessed := done.accessed.insert authority } authority auth = .ok paid ∧ Q paid.meter) :
    ∃ done', applyAuthorization fork chainId done auth = .ok done' ∧ HasCodes done'.state ∧
      Q done'.meter := by
  cases hscope : authorizationInScope chainId auth
  · exact ⟨done, applyAuthorization_of_not_inScope hscope, hcodes, hQ⟩
  cases hrecover : recoverAuthority auth with
  | none => exact ⟨done, applyAuthorization_of_recoverAuthority_none hrecover, hcodes, hQ⟩
  | some authority =>
    obtain ⟨code, hcode⟩ := hcodes authority
    cases haccept : authorityAccepts done.state authority auth with
    | error e => simp [authorityAccepts, hcode, bind, Except.bind, pure, Except.pure] at haccept
    | ok accepts =>
      cases accepts
      · exact ⟨_, applyAuthorization_of_refused hscope hrecover haccept, hcodes, hQ⟩
      · obtain ⟨paid, hpaid, hmeter⟩ := hpay authority
        obtain ⟨hstate, -, -⟩ := state_payAuthorization hpaid
        obtain ⟨state, hdelegate⟩ := delegate_isOk (fork := fork) (authority := authority)
          (auth := auth) paid.state
        have hcodes' := hasCodes_delegate hdelegate (by rw [hstate]; exact hcodes)
        have happly := applyAuthorization_of_accepts_of_pay (chainId := chainId) hscope hrecover
          haccept hpaid
        rw [hdelegate] at happly
        exact ⟨_, happly, hcodes', hmeter⟩

/-- Whether every charge of at most the execution gas left succeeds and takes at most its amount.

It holds for a charge of execution gas and for a charge of state gas.

Neither charge raises the execution gas left. -/
def ChargesWithin (Meter : Type) [GasMeter Meter] : Prop :=
  ∀ (meter : Meter) (amount : Nat), amount ≤ GasMeter.gasLeft meter →
    (∃ after, GasMeter.charge meter amount = .ok after ∧
      GasMeter.gasLeft meter - amount ≤ GasMeter.gasLeft after ∧
      GasMeter.gasLeft after ≤ GasMeter.gasLeft meter) ∧
    (∃ after, GasMeter.chargeState meter amount = .ok after ∧
      GasMeter.gasLeft meter - amount ≤ GasMeter.gasLeft after ∧
      GasMeter.gasLeft after ≤ GasMeter.gasLeft meter)

/-- The meter of every fork up to BPO5 charges within the gas left. -/
theorem chargesWithin_nat : ChargesWithin Nat := by
  intro meter amount h
  have hlt : ¬meter < amount := Nat.not_lt_of_le h
  exact ⟨⟨meter - amount, by simp [GasMeter.charge, hlt], by simp [GasMeter.gasLeft],
      by simp [GasMeter.gasLeft]⟩,
    ⟨meter - amount, by simp [GasMeter.chargeState, hlt], by simp [GasMeter.gasLeft],
      by simp [GasMeter.gasLeft]⟩⟩

/-- The meter of EIP-8037 charges within the gas left.

A charge of state gas takes the reservoir first, so it may take less execution gas. -/
theorem chargesWithin_stateGasMeter : ChargesWithin Evm.StateGasMeter := by
  intro meter amount h
  simp only [GasMeter.gasLeft] at h ⊢
  refine ⟨?_, ?_⟩
  · exact ⟨_, Evm.StateGasMeter.charge_eq_ok_iff.mpr ⟨h, rfl⟩, Nat.le_refl _, Nat.sub_le _ _⟩
  · simp only [GasMeter.chargeState, Evm.StateGasMeter.chargeState]
    by_cases hreservoir : amount ≤ meter.reservoir
    · simp only [hreservoir, ↓reduceIte]
      exact ⟨_, rfl, Nat.sub_le _ _, Nat.le_refl _⟩
    · have hsum : amount ≤ meter.reservoir + meter.gasLeft := by omega
      simp only [hreservoir, hsum, ↓reduceIte]
      exact ⟨_, rfl, Nat.sub_le_sub_left (Nat.sub_le _ _) _, Nat.sub_le _ _⟩

/-- The charge of an accepted authorization succeeds with at least 227790 execution gas left.

It takes at most 227790 execution gas.

That is 183600 of state gas for a new account, 9000 for the first write, and 35190 of state gas.

The last part pays for a new delegation indicator.

The meter must charge within the gas left.

The code of the authority before the transaction must be readable. -/
theorem chargeAuthorization_isOk (hcharges : ChargesWithin Meter) {code : ByteArray}
    (hcode : done.state.getCode (done.state.getPreStateAccount authority).codeHash = .ok code)
    (hgas : NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE + AUTH_BASE_STATE_GAS ≤
      GasMeter.gasLeft done.meter) :
    ∃ meter, chargeAuthorization done authority auth = .ok meter ∧
      GasMeter.gasLeft done.meter - (NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE + AUTH_BASE_STATE_GAS) ≤
        GasMeter.gasLeft meter ∧
      GasMeter.gasLeft meter ≤ GasMeter.gasLeft done.meter := by
  obtain ⟨m1, h1, l1, u1⟩ : ∃ m1, (if done.state.accountExists authority then pure done.meter
      else GasMeter.chargeState done.meter NEW_ACCOUNT_STATE_GAS : Except Evm.EvmError Meter) =
        .ok m1 ∧
      GasMeter.gasLeft done.meter - NEW_ACCOUNT_STATE_GAS ≤ GasMeter.gasLeft m1 ∧
      GasMeter.gasLeft m1 ≤ GasMeter.gasLeft done.meter := by
    split
    · exact ⟨_, rfl, Nat.sub_le _ _, Nat.le_refl _⟩
    · exact (hcharges done.meter _ (by omega)).2
  obtain ⟨m2, h2, l2, u2⟩ : ∃ m2, (if authority ∈ done.paidWrites then pure m1
      else GasMeter.charge m1 ACCOUNT_WRITE : Except Evm.EvmError Meter) = .ok m2 ∧
      GasMeter.gasLeft m1 - ACCOUNT_WRITE ≤ GasMeter.gasLeft m2 ∧
      GasMeter.gasLeft m2 ≤ GasMeter.gasLeft m1 := by
    split
    · exact ⟨_, rfl, Nat.sub_le _ _, Nat.le_refl _⟩
    · exact (hcharges m1 _ (by omega)).1
  obtain ⟨m3, h3, l3, u3⟩ : ∃ m3, (if auth.address ≠ NULL_ADDRESS ∧ !isValidDelegation code ∧
      authority ∉ done.delegated then GasMeter.chargeState m2 AUTH_BASE_STATE_GAS
      else pure m2 : Except Evm.EvmError Meter) = .ok m3 ∧
      GasMeter.gasLeft m2 - AUTH_BASE_STATE_GAS ≤ GasMeter.gasLeft m3 ∧
      GasMeter.gasLeft m3 ≤ GasMeter.gasLeft m2 := by
    split
    · exact (hcharges m2 _ (by omega)).2
    · exact ⟨_, rfl, Nat.sub_le _ _, Nat.le_refl _⟩
  refine ⟨m3, ?_, by omega, by omega⟩
  unfold chargeAuthorization
  by_cases hexists : done.state.accountExists authority = true <;>
    by_cases hpaid : authority ∈ done.paidWrites <;>
    simp only [hexists, hpaid, ↓reduceIte, Bool.false_eq_true] at h1 h2 ⊢ <;>
    simp only [h1, h2, hcode, Except.mapError, bind, Except.bind] <;>
    exact h3

/-- One authorization succeeds, and from Glamsterdam it takes at most 227790 execution gas.

From Glamsterdam, the meter must charge within the gas left, and hold at least 227790 of it.

The state must hold the code of every account, and the result keeps that fact.

From Glamsterdam, the state must also hold the code of every account before the transaction. -/
theorem applyAuthorization_isOk (hcharges : .glamsterdam ≤ fork → ChargesWithin Meter)
    (hgas : .glamsterdam ≤ fork →
      NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE + AUTH_BASE_STATE_GAS ≤ GasMeter.gasLeft done.meter)
    (hcodes : HasCodes done.state) (hpre : .glamsterdam ≤ fork → HasPreCodes done.state) :
    ∃ done', applyAuthorization fork chainId done auth = .ok done' ∧ HasCodes done'.state ∧
      GasMeter.gasLeft done.meter - (NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE + AUTH_BASE_STATE_GAS) ≤
        GasMeter.gasLeft done'.meter ∧
      GasMeter.gasLeft done'.meter ≤ GasMeter.gasLeft done.meter :=
  applyAuthorization_isOk_of_pay
    (fun meter => GasMeter.gasLeft done.meter -
        (NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE + AUTH_BASE_STATE_GAS) ≤ GasMeter.gasLeft meter ∧
      GasMeter.gasLeft meter ≤ GasMeter.gasLeft done.meter)
    ⟨Nat.sub_le _ _, Nat.le_refl _⟩ hcodes fun authority => by
      by_cases hfork : .glamsterdam ≤ fork
      · obtain ⟨code, hcode⟩ := hpre hfork authority
        obtain ⟨meter, hmeter, hlow, hhigh⟩ :=
          chargeAuthorization_isOk (done := { done with
            state := done.state.recordAccountRead authority
            accessed := done.accessed.insert authority }) (auth := auth) (hcharges hfork) hcode
            (hgas hfork)
        exact ⟨_, (payAuthorization_eq_ok_iff hfork).mpr ⟨meter, hmeter, rfl⟩, hlow, hhigh⟩
      · exact ⟨_, payAuthorization_of_lt_glamsterdam (Nat.lt_of_not_le hfork),
          Nat.sub_le _ _, Nat.le_refl _⟩

/-- The authorizations of a list succeed.

From Glamsterdam, they take at most 227790 execution gas times the length of the list.

From Glamsterdam, the meter must charge within the gas left.

It must then hold at least 227790 times the length of the list.

The state must hold the code of every account.

From Glamsterdam, it must also hold the code of every account before the transaction. -/
theorem foldlM_applyAuthorization_isOk (hcharges : .glamsterdam ≤ fork → ChargesWithin Meter) :
    ∀ (auths : List Authorization) {start : Delegations Meter},
      (.glamsterdam ≤ fork → (NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE + AUTH_BASE_STATE_GAS) *
        auths.length ≤ GasMeter.gasLeft start.meter) →
      HasCodes start.state → (.glamsterdam ≤ fork → HasPreCodes start.state) →
      ∃ done, auths.foldlM (applyAuthorization fork chainId) start = .ok done ∧
        GasMeter.gasLeft start.meter - (NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE +
          AUTH_BASE_STATE_GAS) * auths.length ≤ GasMeter.gasLeft done.meter ∧
        GasMeter.gasLeft done.meter ≤ GasMeter.gasLeft start.meter
  | [], start, _, _, _ => ⟨start, rfl, Nat.sub_le _ _, Nat.le_refl _⟩
  | auth :: rest, start, hgas, hcodes, hpre => by
    simp only [List.length_cons, Nat.mul_succ] at hgas ⊢
    obtain ⟨next, hnext, hcodes', hlow, hhigh⟩ :=
      applyAuthorization_isOk (chainId := chainId) (auth := auth) hcharges
        (fun hfork => Nat.le_trans (Nat.le_add_left _ _) (hgas hfork)) hcodes hpre
    obtain ⟨done, h, hlow', hhigh'⟩ :=
      foldlM_applyAuthorization_isOk hcharges rest
        (fun hfork => by
          have hall := hgas hfork
          generalize (NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE + AUTH_BASE_STATE_GAS) * rest.length =
            rest_gas at hall ⊢
          generalize NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE + AUTH_BASE_STATE_GAS = one at hall hlow
          omega) hcodes' fun hfork => hasPreCodes_applyAuthorization hnext (hpre hfork)
    refine ⟨done, by simp only [List.foldlM_cons, hnext, bind, Except.bind, h], ?_, by omega⟩
    generalize (NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE + AUTH_BASE_STATE_GAS) * rest.length =
      rest_gas at hlow' ⊢
    generalize NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE + AUTH_BASE_STATE_GAS = one at hlow ⊢
    omega

/-- Up to BPO5, one authorization succeeds over any meter.

The state must hold the code of every account, and the result keeps that fact. -/
theorem applyAuthorization_isOk_of_lt_glamsterdam (hfork : fork < .glamsterdam)
    (hcodes : HasCodes done.state) :
    ∃ done', applyAuthorization fork chainId done auth = .ok done' ∧ HasCodes done'.state := by
  have hpre : ¬.glamsterdam ≤ fork := Nat.not_le_of_lt hfork
  obtain ⟨done', h, hcodes', -⟩ := applyAuthorization_isOk (chainId := chainId) (auth := auth)
    (absurd · hpre) (absurd · hpre) hcodes (absurd · hpre)
  exact ⟨done', h, hcodes'⟩

/-- Up to BPO5, the authorizations of every list succeed over any meter.

The state must hold the code of every account. -/
theorem foldlM_applyAuthorization_isOk_of_lt_glamsterdam (hfork : fork < .glamsterdam)
    (auths : List Authorization) {start : Delegations Meter} (hcodes : HasCodes start.state) :
    ∃ done, auths.foldlM (applyAuthorization fork chainId) start = .ok done := by
  have hpre : ¬.glamsterdam ≤ fork := Nat.not_le_of_lt hfork
  obtain ⟨done, h, -⟩ := foldlM_applyAuthorization_isOk (chainId := chainId) (absurd · hpre) auths
    (absurd · hpre) hcodes (absurd · hpre)
  exact ⟨done, h⟩

/-! ## The hash that an authority signs -/

/-- The hash that an authority signs ignores the parity, `r` and `s`. -/
theorem authorizationHash_signature (auth : Authorization) (yParity : UInt8) (r s : U256) :
    authorizationHash { auth with yParity := yParity, r := r, s := s } = authorizationHash auth :=
  rfl

end EthLib.Execution.Transactions

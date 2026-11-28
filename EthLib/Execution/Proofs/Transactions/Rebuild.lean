module

public import EthLib.Execution.Proofs.Transactions.Unfold
public import EthLib.Execution.Proofs.Transactions.Authorization
public import EthLib.Execution.Proofs.Transactions.Deletion
public import EthLib.Execution.Proofs.Transactions.SettlementRebuild

/-!
# Proofs: a transaction from Dencun keeps what rebuilding its block state needs

A transaction buys its gas, applies its authorizations, runs its message and settles its gas.

Each of these keeps the rebuild property of the state on its block.

Sources:

- [EIP-7702][eip7702]: an authorization sets the code of its authority, then raises its nonce.
- [EIP-6780][eip6780]: the accounts that a transaction deletes at its end are ones it created.

[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
[eip6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256)
open EthLib.Execution.Evm
open EthLib.Execution.State

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## Helpers for one delegation -/

/-- A change of an account keeps the storage writes and wipes, or deletes the empty account. -/
theorem storage_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    (tx'.storageWrites = tx.storageWrites ∧ tx'.storageClears = tx.storageClears) ∨
      (f (tx.getAccount address) = .ok EMPTY_ACCOUNT ∧
        tx'.storageWrites = tx.storageWrites.erase address ∧
        tx'.storageClears = tx.storageClears.insert address) := by
  obtain ⟨account, hf, rfl⟩ := TransactionState.modifyState_eq_ok_iff.mp h
  split
  · rename_i hdel
    have hempty : account = EMPTY_ACCOUNT := by
      have he := TransactionState.eq_empty_of_accountExistsAndIsEmpty
        (Bool.and_eq_true_iff.mp hdel).2
      simpa [TransactionState.getAccount, TransactionState.getAccountOptional_setAccount_self]
        using he
    subst hempty
    exact .inr ⟨hf, rfl, rfl⟩
  · exact .inl ⟨rfl, rfl⟩

/-- Setting a code keeps the storage writes and wipes, or deletes the account left empty. -/
theorem storage_setCode {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') :
    (tx'.storageWrites = tx.storageWrites ∧ tx'.storageClears = tx.storageClears) ∨
      ({ tx.getAccount address with codeHash := keccak256 code } = EMPTY_ACCOUNT ∧
        tx'.storageWrites = tx.storageWrites.erase address ∧
        tx'.storageClears = tx.storageClears.insert address) := by
  dsimp only [TransactionState.setCode] at h
  split at h <;>
  · rcases storage_modifyState h with hs | ⟨hf, hs⟩
    · exact .inl hs
    · exact .inr ⟨Except.ok.inj hf, hs⟩

/-- Storage writes kept, or dropped at one address, keep the writes elsewhere. -/
private theorem slot_of_ne {tx tx' : TransactionState} {address other : Address}
    (hne : other ≠ address)
    (hs : (tx'.storageWrites = tx.storageWrites ∧ tx'.storageClears = tx.storageClears) ∨
      (tx'.storageWrites = tx.storageWrites.erase address ∧
        tx'.storageClears = tx.storageClears.insert address)) (key : Bytes32) :
    tx'.storageWrites.slot other key = tx.storageWrites.slot other key := by
  rcases hs with ⟨hw, -⟩ | ⟨hw, -⟩
  · rw [hw]
  · rw [hw]
    simp only [StorageMap.slot, Std.ExtTreeMap.getElem?_erase, Std.compare_eq_iff_eq,
      Ne.symm hne, ↓reduceIte]

/-- Setting a code keeps each returned code under its hash. -/
private theorem code_setCode {tx tx' : TransactionState} {address : Address} {code : ByteArray}
    (hvalid : ∀ hash bytes, tx.getCode hash = .ok bytes → keccak256 bytes = hash)
    (h : tx.setCode fork address code = .ok tx') :
    ∀ hash bytes, tx'.getCode hash = .ok bytes → keccak256 bytes = hash := by
  intro hash bytes hread
  by_cases heq : hash = keccak256 code
  · subst heq
    by_cases hempty_hash : keccak256 code = EMPTY_CODE_HASH
    · rw [hempty_hash] at hread ⊢
      have hok : tx'.getCode EMPTY_CODE_HASH = .ok .empty := by
        simp [TransactionState.getCode]
      rw [hok, Except.ok.injEq] at hread
      subst hread
      rfl
    · have hself := TransactionState.getCode_setCode_self h hempty_hash
      rw [hself, Except.ok.injEq] at hread
      subst hread
      rfl
  · rw [TransactionState.getCode_setCode_of_ne h heq] at hread
    exact hvalid hash bytes hread

/-- A delegation of an authority with no nonce or code keeps the rebuild property.

Setting the code may delete the authority and wipe its storage, but it was plain in the block. -/
private theorem rebuildState_delegate_of_plain {block : BlockState} {tx tx' : TransactionState}
    {authority : Address} {auth : Authorization} {refund : Nat}
    (valid : RebuildState block tx) (hplain : ¬HasNonceOrCode tx authority)
    (h : delegate fork tx authority auth = .ok (tx', refund)) :
    RebuildState block tx' ∧ KeepsNonceOrCode tx tx' := by
  obtain ⟨-, hself, hother⟩ := delegate_eq_ok h
  obtain ⟨coded, hcode, h⟩ := bind_ok_iff.mp h
  obtain ⟨bumped, hnonce, h⟩ := bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hnc_self : HasNonceOrCode bumped authority := by
    left
    rw [hself]
    exact Nat.le_add_left 1 _
  have hacc : ∀ other, other ≠ authority → bumped.getAccount other = tx.getAccount other := by
    intro other hne
    simp only [TransactionState.getAccount, hother other hne]
  have hp : bumped.parent = tx.parent :=
    (TransactionState.parent_incrementNonce hnonce).trans (TransactionState.parent_setCode hcode)
  have hcreated : bumped.createdAccounts = tx.createdAccounts :=
    (TransactionState.createdAccounts_modifyState hnonce).trans
      (TransactionState.createdAccounts_setCode hcode)
  have hstore : (bumped.storageWrites = tx.storageWrites ∧
        bumped.storageClears = tx.storageClears) ∨
      (bumped.storageWrites = tx.storageWrites.erase authority ∧
        bumped.storageClears = tx.storageClears.insert authority) := by
    have hbump : bumped.storageWrites = coded.storageWrites ∧
        bumped.storageClears = coded.storageClears := by
      rcases storage_modifyState hnonce with hs | ⟨hf, -⟩
      · exact hs
      · have hn := congrArg Account.nonce (Except.ok.inj hf)
        simp [EMPTY_ACCOUNT] at hn
    rw [hbump.1, hbump.2]
    -- From Paris, setting the code deletes an account that it leaves empty, with its storage.
    exact (storage_setCode hcode).imp id fun hs => hs.2
  -- The authority had neither a nonce nor code, so the new code and the new nonce keep both.
  refine ⟨⟨⟨hp.trans valid.parent, ?_, ?_, ?_, ?_⟩, ?_⟩,
    (keepsNonceOrCode_setCode_of_not_hasNonceOrCode hplain hcode).trans
      (keepsNonceOrCode_incrementNonce hnonce)⟩
  · intro hash bytes hread
    rw [TransactionState.getCode_modifyState hnonce] at hread
    exact code_setCode valid.code hcode hash bytes hread
  · intro other hnot
    have hne : other ≠ authority := fun heq => hnot (heq ▸ hnc_self)
    have hnot' : ¬HasNonceOrCode tx other :=
      fun hc => hnot ((HasNonceOrCode.congr (hacc other hne)).mpr hc)
    obtain ⟨hb0, hslot⟩ := valid.plain other hnot'
    refine ⟨hb0, fun key => ?_⟩
    rw [slot_of_ne hne hstore key]
    exact hslot key
  · intro other hmem
    rcases hstore with ⟨-, hc⟩ | ⟨-, hc⟩
    · exact valid.clears other (hc ▸ hmem)
    · rw [hc, Std.ExtTreeSet.mem_insert, Std.compare_eq_iff_eq] at hmem
      rcases hmem with rfl | hmem
      -- The wiped authority was plain, so it had no nonce or code in the block.
      · exact (valid.plain _ hplain).1
      · exact valid.clears other hmem
  · intro other code hn hc hv
    have hne : other ≠ authority := by
      rintro rfl
      rw [hself] at hn
      exact Nat.succ_ne_zero _ hn
    rw [hacc other hne] at hn hc ⊢
    exact valid.delegations other code hn hc hv
  · intro other hmem
    exact valid.created other (hcreated ▸ hmem)

/-- An authority that takes an authorization and has nonce 0 has no nonce or code.

Its code reads as empty or as a delegation indicator, and no account with nonce 0 holds one. -/
private theorem not_hasNonceOrCode_of_authorityAccepts {block : BlockState}
    {tx : TransactionState} {authority : Address} {auth : Authorization}
    (valid : RebuildState block tx) (haccept : authorityAccepts tx authority auth = .ok true)
    (hn0 : (tx.getAccount authority).nonce = 0) : ¬HasNonceOrCode tx authority := by
  rintro (hn | hc)
  · omega
  unfold authorityAccepts at haccept
  cases hcode : tx.getCode (tx.getAccount authority).codeHash with
  | error e => simp [hcode, bind, Except.bind] at haccept
  | ok code =>
    simp only [hcode, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq] at haccept
    have hhash := valid.code _ code hcode
    rcases haccept.1 with hsize | hdel
    · have hempty : code = .empty := by
        obtain ⟨data⟩ := code
        simp only [ByteArray.size, Array.size_eq_zero_iff] at hsize
        subst hsize
        rfl
      subst hempty
      exact hc hhash.symm
    -- No account with nonce 0 holds a delegation.
    · exact valid.delegations authority code hn0 hc hdel hhash

/-- One authorization keeps the rebuild property, lowers no nonce and keeps each nonce or code. -/
private theorem applyAuthorization_rebuildState {block : BlockState} {chainId : Nat}
    {auth : Authorization} {done done' : Delegations Meter}
    (valid : RebuildState block done.state)
    (h : applyAuthorization fork chainId done auth = .ok done') :
    RebuildState block done'.state ∧ KeepsNonceOrCode done.state done'.state := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨haccept, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact ⟨valid, .refl _⟩
  · exact ⟨valid.of_sameWrites (SameWrites.recordAccountRead _ _) rfl rfl,
      (SameWrites.recordAccountRead _ _).keepsNonceOrCode rfl⟩
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    dsimp only at hdelegate ⊢
    have vrec : RebuildState block (done.state.recordAccountRead authority) :=
      valid.of_sameWrites (SameWrites.recordAccountRead _ _) rfl rfl
    have krec : KeepsNonceOrCode done.state (done.state.recordAccountRead authority) :=
      (SameWrites.recordAccountRead _ _).keepsNonceOrCode rfl
    -- The authorization sets the code of its authority and then raises its nonce, by EIP-7702.
    by_cases hn : 1 ≤ ((done.state.recordAccountRead authority).getAccount authority).nonce
    · obtain ⟨coded, hcode, h2⟩ := bind_ok_iff.mp hdelegate
      obtain ⟨bumped, hnonce, h3⟩ := bind_ok_iff.mp h2
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, -⟩ := h3
      obtain ⟨v1, k1⟩ := vrec.setCode hn hcode
      obtain ⟨v2, k2, -⟩ := v1.incrementNonce hnonce
      exact ⟨v2, krec.trans (k1.trans k2)⟩
    · have hplain := not_hasNonceOrCode_of_authorityAccepts vrec haccept (by omega)
      obtain ⟨v, k⟩ := rebuildState_delegate_of_plain vrec hplain hdelegate
      exact ⟨v, krec.trans k⟩

/-- A run of authorizations keeps the rebuild property and each nonce or code. -/
private theorem foldlM_applyAuthorization_rebuildState {block : BlockState} {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      RebuildState block start.state →
      RebuildState block done.state ∧ KeepsNonceOrCode start.state done.state
  | [], _, _, h, valid => by
    cases h
    exact ⟨valid, .refl _⟩
  | _ :: _, _, _, h, valid => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    obtain ⟨v1, k1⟩ := applyAuthorization_rebuildState valid hnext
    obtain ⟨v2, k2⟩ := foldlM_applyAuthorization_rebuildState h v1
    exact ⟨v2, k1.trans k2⟩

/-! ## The authorizations -/

/-- Applying the authorizations of a transaction keeps the rebuild property.

It lowers no nonce, and keeps a nonce or code wherever there was one. -/
theorem applyAuthorizations_rebuildState {block : BlockState} {chainId : Nat}
    {state : TransactionState} {accessed : Std.ExtTreeSet Address} {meter : Meter}
    {paid : Std.ExtTreeSet Address} {auths : List Authorization} {done : Delegations Meter}
    (valid : RebuildState block state)
    (h : applyAuthorizations fork chainId state accessed meter paid auths = .ok done) :
    RebuildState block done.state ∧ KeepsNonceOrCode state done.state :=
  foldlM_applyAuthorization_rebuildState h valid

/-! ## The message -/

/-- Preparing the first frame of a message keeps the rebuild property and a caller's nonce or code.

A call that runs code runs it at a target with a nonce or code. -/
theorem prepareFirstFrame_rebuildState {block : BlockState} {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (valid : RebuildState block state) (hcaller : HasNonceOrCode state message.caller)
    (htarget : ∀ target, message.target = some target → message.currentTarget = target)
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    RebuildState block first.state ∧ HasNonceOrCode first.state first.message.caller ∧
      (message.target = none →
        first.state.accountDeployable first.message.currentTarget = true) ∧
      (message.target ≠ none → first.message.code.size ≠ 0 →
        HasNonceOrCode first.state first.message.currentTarget) := by
  unfold prepareFirstFrame at h
  split at h
  · rename_i hnone
    have vrec : RebuildState block (state.recordAccountRead message.currentTarget) :=
      valid.of_sameWrites (SameWrites.recordAccountRead _ _) rfl rfl
    dsimp only at h
    split at h
    · rename_i hdeploy
      have hfin : first.state = state.recordAccountRead message.currentTarget ∧
          first.message.caller = message.caller ∧
          first.message.currentTarget = message.currentTarget := by
        split at h <;>
        · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
          cases h
          exact ⟨rfl, rfl, rfl⟩
      obtain ⟨hs, hc, hct⟩ := hfin
      rw [hs, hc, hct]
      exact ⟨vrec, hcaller, fun _ => hdeploy, fun hne => absurd hnone hne⟩
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target htgt
    have hcur : message.currentTarget = target := htarget target htgt
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    obtain ⟨vdone, kdone⟩ := applyAuthorizations_rebuildState valid hdone
    dsimp only at h
    generalize hs1 : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = s1 at h
    have hsw1 : SameWrites s1 done.state ∧ s1.parent = done.state.parent ∧
        s1.createdAccounts = done.state.createdAccounts := by
      rw [← hs1]
      split
      · exact ⟨SameWrites.recordAccountRead _ _, rfl, rfl⟩
      · exact ⟨SameWrites.refl _, rfl, rfl⟩
    have v1 : RebuildState block s1 := vdone.of_sameWrites hsw1.1 hsw1.2.1 hsw1.2.2
    have k1 : KeepsNonceOrCode state s1 :=
      kdone.trans (hsw1.1.keepsNonceOrCode hsw1.2.1)
    have v2 : RebuildState block (s1.recordAccountRead target) :=
      v1.of_sameWrites (SameWrites.recordAccountRead _ _) rfl rfl
    have k2 : KeepsNonceOrCode state (s1.recordAccountRead target) :=
      k1.trans ((SameWrites.recordAccountRead _ _).keepsNonceOrCode rfl)
    have hsome : message.target ≠ none := by rw [htgt]; exact Option.some_ne_none _
    split at h
    all_goals
      obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, hcode, h⟩ := bind_ok_iff.mp h
      have hread := mapError_ok_iff.mp hcode
      have hhash : code ≠ .empty →
          HasNonceOrCode (s1.recordAccountRead target) target := by
        intro hne
        refine .inr fun hh => hne ?_
        rw [hh] at hread
        simp only [TransactionState.getCode, ↓reduceIte, Except.ok.injEq] at hread
        exact hread.symm
      generalize hdel : (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        refine ⟨v2, k2.2 _ hcaller, fun hn => absurd hn hsome, fun _ hsize => ?_⟩
        dsimp only [FirstFrame.ofMeter]
        rw [hcur]
        refine hhash fun hempty => hsize ?_
        dsimp only [FirstFrame.ofMeter] at hsize ⊢
        rw [hempty]
        rfl
      · have hcode_ne : code ≠ .empty := by
          intro hempty
          rw [hempty, delegatedAddress_empty, ite_self] at hdel
          cases hdel
        have v3 : RebuildState block ((s1.recordAccountRead target).recordAccountRead delegate) :=
          v2.of_sameWrites (SameWrites.recordAccountRead _ _) rfl rfl
        have k3 : KeepsNonceOrCode (s1.recordAccountRead target)
            ((s1.recordAccountRead target).recordAccountRead delegate) :=
          (SameWrites.recordAccountRead _ _).keepsNonceOrCode rfl
        dsimp only at h
        split at h
        all_goals
          obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          refine ⟨v3, k3.2 _ (k2.2 _ hcaller), fun hn => absurd hn hsome, fun _ _ => ?_⟩
          dsimp only [FirstFrame.ofMeter]
          rw [hcur]
          exact k3.2 _ (hhash hcode_ne)

/-- From Spurious Dragon, the message of a transaction keeps the rebuild property.

Its caller must have a nonce or code.

A call must run at its recipient, as the message of a transaction does. -/
theorem processMessageCall_rebuildState [LawfulGasMeter Meter]
    (hfork : .spuriousDragon ≤ fork) {block : BlockState} {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (valid : RebuildState block state) (hcaller : HasNonceOrCode state message.caller)
    (htarget : ∀ target, message.target = some target → message.currentTarget = target)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    RebuildState block output.state := by
  rw [processMessageCall_unfold] at h
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
    · cases h
      exact valid.of_sameWrites (SameWrites.withReadsOf _ _) rfl rfl
  · rw [hprep] at h
    dsimp only at h
    obtain ⟨vfirst, hcf, hdep, hcode⟩ := prepareFirstFrame_rebuildState valid hcaller htarget hprep
    have hframe : ∀ {evm : Evm fork Meter} {r : Nat} {t : Std.ExtTreeSet Address},
        (CallOutput.ofFrame evm r t).state = evm.state := by
      intro evm r t
      unfold CallOutput.ofFrame
      dsimp only
      split <;> rfl
    split at h
    · rename_i hnone
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [hframe]
      exact (processCreateMessage_rebuildState hfork vfirst (hdep hnone) (.inr hcf) hrun).1
    · rename_i target hsome
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [hframe]
      have hne : message.target ≠ none := by rw [hsome]; exact Option.some_ne_none _
      exact (processMessage_rebuildState hfork vfirst (hcode hne) (.inr hcf) hrun).1

/-! ## The deletions -/

/-- Dropping the writes of one address keeps the writes of every other address. -/
private theorem slot_erase (writes : StorageMap) (address other : Address) (key : Bytes32) :
    StorageMap.slot (writes.erase address) other key =
      if address = other then none else writes.slot other key := by
  simp only [StorageMap.slot, Std.ExtTreeMap.getElem?_erase, Std.compare_eq_iff_eq]
  split <;> rfl

/-- A wipe of one account with no nonce or code in the block keeps what the end needs.

The account is left with no code and no writes, and every other account and its writes stay. -/
private theorem _root_.EthLib.Execution.Evm.RebuildEnd.of_wipe
    {block : BlockState} {tx tx' : TransactionState}
    {address : Address} (valid : RebuildEnd block tx)
    (hblock : ¬HasNonceOrCode (TransactionState.ofBlock block) address)
    (hp : tx'.parent = tx.parent) (hcode : tx'.getCode = tx.getCode)
    (hacc : ∀ other, other ≠ address → tx'.getAccount other = tx.getAccount other)
    (hslot : ∀ other key, tx'.storageWrites.slot other key =
      if address = other then none else tx.storageWrites.slot other key)
    (hhash : (tx'.getAccount address).codeHash = EMPTY_CODE_HASH)
    (hclears : ∀ other, other ∈ tx'.storageClears →
      other = address ∨ other ∈ tx.storageClears) :
    RebuildEnd block tx' := by
  refine ⟨hp.trans valid.parent, fun hash code hread => valid.code hash code (hcode ▸ hread),
    fun other hempty => ?_, fun other hmem => ?_, fun other code hn hc hv => ?_⟩
  · by_cases hne : address = other
    · subst hne
      exact ⟨hblock, fun key => by simp only [hslot, ↓reduceIte]⟩
    · obtain ⟨hb0, hwrites⟩ := valid.plain other
        (fun hc => hempty ((HasNonceOrCode.congr (hacc other (Ne.symm hne))).mpr hc))
      exact ⟨hb0, fun key => by simp only [hslot, hne, ↓reduceIte, hwrites key]⟩
  · rcases hclears other hmem with rfl | hmem
    · exact hblock
    · exact valid.clears other hmem
  · have hne : other ≠ address := by
      rintro rfl
      exact hc hhash
    rw [hacc other hne] at hn hc ⊢
    exact valid.delegations other code hn hc hv

/-- Deleting an account with no nonce or code in the block keeps what the end needs. -/
private theorem _root_.EthLib.Execution.Evm.RebuildEnd.destroyAccount
    {block : BlockState} {tx : TransactionState}
    {address : Address} (valid : RebuildEnd block tx)
    (hblock : ¬HasNonceOrCode (TransactionState.ofBlock block) address) :
    RebuildEnd block (tx.destroyAccount address) := by
  refine valid.of_wipe hblock rfl rfl (fun other hne => ?_)
    (fun other key => slot_erase _ _ _ _) ?_ (fun other hmem => ?_)
  · simp only [TransactionState.getAccount_destroyAccount, hne, ↓reduceIte]
  · simp only [TransactionState.getAccount_destroyAccount, ↓reduceIte]
    rfl
  · simp only [TransactionState.destroyAccount, TransactionState.setAccount,
      TransactionState.destroyStorage, Std.ExtTreeSet.mem_insert, Std.compare_eq_iff_eq] at hmem
    rcases hmem with rfl | hmem
    · exact .inl rfl
    · exact .inr hmem

/-- Clearing an account with no nonce or code in the block keeps what the end needs. -/
private theorem _root_.EthLib.Execution.Evm.RebuildEnd.clearAccountPreservingBalance
    {block : BlockState}
    {tx tx' : TransactionState} {address : Address} (valid : RebuildEnd block tx)
    (hblock : ¬HasNonceOrCode (TransactionState.ofBlock block) address)
    (h : tx.clearAccountPreservingBalance fork address = .ok tx') :
    RebuildEnd block tx' := by
  have hm : (tx.destroyStorage address).modifyState fork address
      (fun account => .ok { account with nonce := 0, codeHash := EMPTY_CODE_HASH }) = .ok tx' := h
  refine valid.of_wipe hblock (TransactionState.parent_clearAccountPreservingBalance h)
    (by rw [TransactionState.getCode_modifyState hm]; rfl) (fun other hne => ?_)
    (fun other key => ?_) ?_ (fun other hmem => ?_)
  · simp only [TransactionState.getAccount,
      TransactionState.getAccountOptional_modifyState_of_ne hm hne,
      TransactionState.getAccountOptional_destroyStorage]
  -- The wipe drops the writes of the account, and a deletion after it drops them again.
  · rcases storage_modifyState hm with ⟨hw, -⟩ | ⟨-, hw, -⟩
    · rw [hw]
      exact slot_erase _ _ _ _
    · rw [hw, slot_erase]
      by_cases hne : address = other
      · simp only [hne, ↓reduceIte]
      · simp only [hne, ↓reduceIte]
        exact (slot_erase _ _ _ _).trans (by simp only [hne, ↓reduceIte])
  · rw [TransactionState.getAccount_clearAccountPreservingBalance h]
  · have hmid : ∀ x, x ∈ (tx.destroyStorage address).storageClears →
        x = address ∨ x ∈ tx.storageClears := by
      intro x hx
      simp only [TransactionState.destroyStorage, Std.ExtTreeSet.mem_insert,
        Std.compare_eq_iff_eq] at hx
      rcases hx with rfl | hx
      · exact .inl rfl
      · exact .inr hx
    rcases storage_modifyState hm with ⟨-, hc⟩ | ⟨-, -, hc⟩
    · exact hmid other (hc ▸ hmem)
    · rw [hc, Std.ExtTreeSet.mem_insert, Std.compare_eq_iff_eq] at hmem
      rcases hmem with rfl | hmem
      · exact .inl rfl
      · exact hmid other hmem

/-- The deletions of a list of accounts keep what the end needs.

Each account in the list had no nonce or code in the block. -/
private theorem foldlM_delete_rebuildEnd {block : BlockState} {l : List Address}
    (hblock : ∀ address ∈ l, ¬HasNonceOrCode (TransactionState.ofBlock block) address) :
    ∀ {l' : List Address} {init final : TransactionState}, l' ⊆ l →
      l'.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      RebuildEnd block init → RebuildEnd block final
  | [], _, _, _, h, valid => by
    cases h
    exact valid
  | address :: rest, _, _, hsub, h, valid => by
    obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
    have hplain := hblock address (hsub List.mem_cons_self)
    have vmid : RebuildEnd block mid := by
      split at hmid
      · exact valid.clearAccountPreservingBalance hplain hmid
      · cases hmid
        exact valid.destroyAccount hplain
    exact foldlM_delete_rebuildEnd hblock (fun x hx => hsub (List.mem_cons_of_mem _ hx)) h vmid

/-- Deleting the accounts of a transaction keeps what its end needs.

Each account to delete must be one that the transaction created, as it is from Dencun.

No account may be touched, as from Paris. -/
theorem deleteAccounts_rebuildEnd {block : BlockState}
    {state state' : TransactionState} {output : CallOutput} (valid : RebuildState block state)
    (hcreated : ∀ address ∈ output.accountsToDelete, address ∈ state.createdAccounts)
    (htouched : ∀ address, address ∉ output.touchedAccounts)
    (h : deleteAccounts fork state output = .ok state') :
    -- The deletion keeps less than the rebuild property.
    --
    -- An account that it deletes may lose its balance.
    --
    -- The deletion keeps the block and each code under its hash.
    --
    -- Each wipe is still at an account with no nonce or code in the block.
    --
    -- It also keeps every account with nonce 0 off delegations.
    RebuildEnd block state' := by
  unfold deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  -- Each account to delete was created in the transaction.
  --
  -- So it had no nonce or code in the block.
  have hblock : ∀ address ∈ output.accountsToDelete.toList,
      ¬HasNonceOrCode (TransactionState.ofBlock block) address :=
    fun address hmem => valid.created address (hcreated address (Std.ExtTreeSet.mem_toList.mp hmem))
  have vdel := foldlM_delete_rebuildEnd hblock (List.Subset.refl _) hdeleted valid.toRebuildEnd
  have hnil : output.touchedAccounts.toList = [] := by
    cases hl : output.touchedAccounts.toList with
    | nil => rfl
    | cons x rest =>
      have hx : x ∈ output.touchedAccounts.toList := by rw [hl]; exact List.mem_cons_self
      exact absurd (Std.ExtTreeSet.mem_toList.mp hx) (htouched x)
  rw [hnil]
  unfold TransactionState.destroyTouchedEmptyAccounts
  split
  · exact vdel
  · exact vdel

/-! ## The transaction -/

/-- A run of a transaction meets the hypotheses on the start of its message.

After the purchase of gas, the state has the rebuild property and the caller has a nonce.

A call of the run goes to its recipient. -/
theorem TransactionRun.messageReady [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    {target : Address} {bought : TransactionState} {message : Message fork}
    {output : CallOutput} {settled : TransactionState}
    -- Each code read in its block state has its hash.
    (code : ∀ hash code, (TransactionState.ofBlock block).getCode hash = .ok code →
      keccak256 code = hash)
    -- That state holds no delegation indicator at an account with nonce 0.
    (delegations : DelegationsHaveNonce (.ofBlock block))
    (h : TransactionRun Meter env block included tx out target bought message output settled) :
    RebuildState block bought ∧ HasNonceOrCode bought message.caller ∧
      (∀ t, message.target = some t → message.currentTarget = t) := by
  obtain ⟨hTarget, hBought, hMessage, -⟩ := h
  -- Buying the gas keeps the rebuild property, and raises the nonce of the sender.
  obtain ⟨vb, -, hnonce⟩ := buyGas_rebuildState (RebuildState.ofBlock code delegations) hBought
  refine ⟨vb, caller_transactionMessage hMessage ▸ .inl hnonce, fun t ht => ?_⟩
  -- A call of a transaction runs at its recipient.
  obtain ⟨hto, hcur⟩ := target_transactionMessage hMessage
  rw [hcur]
  rw [hto] at ht
  unfold messageTarget at hTarget
  rw [ht] at hTarget
  exact (Except.ok.inj hTarget).symm

/-- From Dencun, a run of a transaction with any gas meter keeps what its end needs. -/
private theorem runTransaction_rebuildEnd [LawfulGasMeter Meter] (hfork : .dencun ≤ fork)
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {output : TransactionOutput}
    (code : ∀ hash code, (TransactionState.ofBlock block).getCode hash = .ok code →
      keccak256 code = hash)
    (delegations : DelegationsHaveNonce (.ofBlock block))
    (h : runTransaction Meter env block included tx = .ok output) :
    RebuildEnd block output.state := by
  obtain ⟨target, bought, message, out, settled, hrun⟩ := runTransaction_eq_ok h
  -- Buying the gas keeps the rebuild property of the state on its block.
  obtain ⟨vb, hcaller, htarget⟩ := hrun.messageReady code delegations
  obtain ⟨-, -, -, hOutput, -, hSettle, hDeleted⟩ := hrun
  -- So do its authorizations and its message.
  have vout := processMessageCall_rebuildState (Nat.le_trans (by decide) hfork)
    (message := { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir })
    vb hcaller htarget hOutput
  -- So does the settlement of the gas.
  obtain ⟨vs, -⟩ := settleGas_rebuildState (Nat.le_trans (by decide) hfork) vout hSettle
  refine deleteAccounts_rebuildEnd vs (fun address hmem => ?_) (fun address hmem => ?_)
    hDeleted
  -- At the end, the transaction deletes the accounts that destroyed themselves, by EIP-6780.
  --
  -- Each was created in the same transaction.
  · rw [createdAccounts_settleGas hSettle]
    exact accountsToDelete_processMessageCall hfork hOutput
      (fun _ hm => by simp at hm) address hmem
  -- From Paris, the message touches no account.
  --
  -- So the transaction deletes no other account.
  · have hstart := touchedAccounts_processMessageCall (Nat.le_trans (by decide) hfork) hOutput
      address hmem
    simp at hstart

/-- From Dencun, a transaction keeps what its end needs.

Each code read in the block state before it must have its hash.

That state must hold no delegation at an account with nonce 0. -/
theorem processTransaction_rebuildEnd (hfork : .dencun ≤ fork) {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction} {output : TransactionOutput}
    (code : ∀ hash code, (TransactionState.ofBlock block).getCode hash = .ok code →
      keccak256 code = hash)
    (delegations : DelegationsHaveNonce (.ofBlock block))
    (h : processTransaction env block included tx = .ok output) :
    RebuildEnd block output.state := by
  rw [processTransaction_unfold] at h
  split at h
  · cases h
  split at h
  · exact runTransaction_rebuildEnd hfork code delegations h
  · exact runTransaction_rebuildEnd hfork code delegations h

end EthLib.Execution.Transactions

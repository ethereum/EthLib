module

public import EthLib.Execution.Proofs.Evm.Call.Nonce
public import EthLib.Execution.Proofs.Evm.Call.Reads
public import EthLib.Execution.Proofs.Evm.Call.StepRules
public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: every message from Spurious Dragon keeps the rebuild property

From Spurious Dragon, every successful call and creation keeps a property of transaction states.

The state runs on a fixed block state.

Each code that the state returns has the Keccak-256 hash under which it is read.

Every empty or missing account holds no nonzero word of storage.

Every address whose storage was wiped held no nonzero word in the block state.

Every address with nonce 0 and no code keeps at least its balance from the block state.

It also had nonce 0 and no code in the block state, and has no storage write in the transaction.

That ties the storage of a call to the storage of the block state at every key not written.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork Hash32 U256 toAddressMasked)
open EthLib.Cryptography.Hash.Keccak (keccak256)
open EthLib.Execution.State (Account BlockState EMPTY_ACCOUNT EMPTY_CODE_HASH StateError
  StorageMap TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## Accounts with a nonce or code -/

/-- Whether the account at `address` in `tx` has a positive nonce or holds code. -/
def HasNonceOrCode (tx : TransactionState) (address : Address) : Prop :=
  1 ≤ (tx.getAccount address).nonce ∨ (tx.getAccount address).codeHash ≠ EMPTY_CODE_HASH

/-- An account with a nonce or code is not the empty account. -/
theorem HasNonceOrCode.ne_empty {tx : TransactionState} {address : Address}
    (h : HasNonceOrCode tx address) : tx.getAccount address ≠ EMPTY_ACCOUNT := by
  intro hempty
  rcases h with hn | hc
  · rw [hempty] at hn
    exact Nat.not_succ_le_zero 0 hn
  · rw [hempty] at hc
    exact hc rfl

/-- Two states with the same account at `address` agree on `HasNonceOrCode`. -/
theorem HasNonceOrCode.congr {tx tx' : TransactionState} {address : Address}
    (h : tx'.getAccount address = tx.getAccount address) :
    HasNonceOrCode tx' address ↔ HasNonceOrCode tx address := by
  simp only [HasNonceOrCode, h]

/-- Whether `tx'` keeps every positive nonce and every code hash of `tx`, and lowers no nonce. -/
def KeepsNonceOrCode (tx tx' : TransactionState) : Prop :=
  NonceLe tx tx' ∧ ∀ address, HasNonceOrCode tx address → HasNonceOrCode tx' address

/-- Every state keeps its own nonces and code hashes. -/
theorem KeepsNonceOrCode.refl (tx : TransactionState) : KeepsNonceOrCode tx tx :=
  ⟨NonceLe.refl tx, fun _ h => h⟩

/-- Two transitions that keep nonces and code hashes compose. -/
theorem KeepsNonceOrCode.trans {a b c : TransactionState}
    (hab : KeepsNonceOrCode a b) (hbc : KeepsNonceOrCode b c) : KeepsNonceOrCode a c :=
  ⟨hab.1.trans hbc.1, fun address h => hbc.2 address (hab.2 address h)⟩

/-! ## Same writes and the rebuild property -/

/-- The property of a transaction state on `block` that execution from Spurious Dragon keeps. -/
structure RebuildState (block : BlockState) (tx : TransactionState) : Prop where
  /-- The state runs on `block`. -/
  parent : tx.parent = block
  /-- Each returned code has the hash under which it is read. -/
  code : ∀ hash code, tx.getCode hash = .ok code → keccak256 code = hash
  /-- Empty and missing accounts hold no nonzero storage word. -/
  emptyStorage : ∀ address, tx.getAccount address = EMPTY_ACCOUNT →
    ∀ key, tx.getStorage address key = 0
  /-- Every wiped storage held no nonzero word in `block`. -/
  clears : ∀ address, address ∈ tx.storageClears →
    ∀ key, (TransactionState.ofBlock block).getStorage address key = 0
  /-- An account without a nonce or code had none in `block`, gained balance, and has no write. -/
  plain : ∀ address, ¬HasNonceOrCode tx address →
    ¬HasNonceOrCode (TransactionState.ofBlock block) address ∧
      ((TransactionState.ofBlock block).getAccount address).balance ≤
        (tx.getAccount address).balance ∧
      ∀ key, tx.storageWrites.slot address key = none

/-- With no write on top of `block`, the code and empty-storage laws give `RebuildState`. -/
theorem RebuildState.ofBlock {block : BlockState}
    (hcode : ∀ hash code, (TransactionState.ofBlock block).getCode hash = .ok code →
      keccak256 code = hash)
    (hempty : ∀ address, (TransactionState.ofBlock block).getAccount address = EMPTY_ACCOUNT →
      ∀ key, (TransactionState.ofBlock block).getStorage address key = 0) :
    RebuildState block (.ofBlock block) where
  parent := rfl
  code := hcode
  emptyStorage := hempty
  clears _ hmem := absurd hmem Std.ExtTreeSet.not_mem_empty
  plain _ hnc := ⟨hnc, BitVec.le_refl _, fun _ => rfl⟩

/-- Same writes are reflexive. -/
theorem SameWrites.refl (tx : TransactionState) : SameWrites tx tx :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Same writes are symmetric. -/
theorem SameWrites.symm {a b : TransactionState} (h : SameWrites a b) : SameWrites b a :=
  ⟨h.accountWrites.symm, h.storageWrites.symm, h.codeWrites.symm, h.storageClears.symm,
    h.transientStorage.symm⟩

/-- Same writes are transitive. -/
theorem SameWrites.trans {a b c : TransactionState} (hab : SameWrites a b)
    (hbc : SameWrites b c) : SameWrites a c :=
  ⟨hab.accountWrites.trans hbc.accountWrites, hab.storageWrites.trans hbc.storageWrites,
    hab.codeWrites.trans hbc.codeWrites, hab.storageClears.trans hbc.storageClears,
    hab.transientStorage.trans hbc.transientStorage⟩

/-- Recording an account read keeps the writes. -/
theorem SameWrites.recordAccountRead (tx : TransactionState) (address : Address) :
    SameWrites (tx.recordAccountRead address) tx :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Recording a storage read keeps the writes. -/
theorem SameWrites.recordStorageRead (tx : TransactionState) (address : Address) (key : Bytes32) :
    SameWrites (tx.recordStorageRead address key) tx :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Copying reads from another transaction keeps the writes. -/
theorem SameWrites.withReadsOf (tx other : TransactionState) :
    SameWrites (tx.withReadsOf other) tx :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Two states with the same writes and the same block read the same optional accounts. -/
theorem SameWrites.getAccountOptional {tx snapshot : TransactionState}
    (h : SameWrites tx snapshot) (hp : tx.parent = snapshot.parent) (address : Address) :
    tx.getAccountOptional address = snapshot.getAccountOptional address := by
  simp only [TransactionState.getAccountOptional, h.accountWrites, hp]

/-- Two states with the same writes and the same block read the same accounts. -/
theorem SameWrites.getAccount {tx snapshot : TransactionState}
    (h : SameWrites tx snapshot) (hp : tx.parent = snapshot.parent) (address : Address) :
    tx.getAccount address = snapshot.getAccount address := by
  simp only [TransactionState.getAccount, h.getAccountOptional hp address]

/-- Two states with the same writes and the same block read the same code. -/
theorem SameWrites.getCode {tx snapshot : TransactionState}
    (h : SameWrites tx snapshot) (hp : tx.parent = snapshot.parent) (hash : Hash32) :
    tx.getCode hash = snapshot.getCode hash := by
  simp only [TransactionState.getCode, h.codeWrites, hp]

/-- Two states with the same writes and the same block read the same storage. -/
theorem SameWrites.getStorage {tx snapshot : TransactionState}
    (h : SameWrites tx snapshot) (hp : tx.parent = snapshot.parent)
    (address : Address) (key : Bytes32) :
    tx.getStorage address key = snapshot.getStorage address key := by
  simp only [TransactionState.getStorage, h.storageWrites, h.storageClears, hp]

/-- Same writes on the same block keep nonces and code hashes. -/
theorem SameWrites.keepsNonceOrCode {tx snapshot : TransactionState}
    (h : SameWrites snapshot tx) (hp : snapshot.parent = tx.parent) :
    KeepsNonceOrCode tx snapshot := by
  refine ⟨fun address => ?_, fun address hnc => ?_⟩
  · rw [h.getAccount hp address]
    exact Nat.le_refl _
  · exact (HasNonceOrCode.congr (h.getAccount hp address)).mpr hnc

/-- Same writes on the same block keep `RebuildState`. -/
theorem RebuildState.of_sameWrites {block : BlockState} {tx tx' : TransactionState}
    (valid : RebuildState block tx) (h : SameWrites tx' tx) (hp : tx'.parent = tx.parent) :
    RebuildState block tx' where
  parent := hp.trans valid.parent
  code hash code hread := valid.code hash code ((h.getCode hp hash).symm.trans hread)
  emptyStorage address hempty key := by
    rw [h.getStorage hp address key]
    exact valid.emptyStorage address ((h.getAccount hp address).symm.trans hempty) key
  clears address hmem key := valid.clears address (h.storageClears ▸ hmem) key
  plain address hnc := by
    have hnc' : ¬HasNonceOrCode tx address :=
      fun hc => hnc ((HasNonceOrCode.congr (h.getAccount hp address)).mpr hc)
    obtain ⟨hb0, hbal, hslot⟩ := valid.plain address hnc'
    refine ⟨hb0, ?_, fun key => ?_⟩
    · rw [h.getAccount hp address]
      exact hbal
    · rw [h.storageWrites]
      exact hslot key

/-- Under `RebuildState`, an empty account had no nonzero storage word in `block`. -/
theorem RebuildState.blockStorage_of_empty {block : BlockState} {tx : TransactionState}
    {address : Address} (valid : RebuildState block tx)
    (hempty : tx.getAccount address = EMPTY_ACCOUNT) (key : Bytes32) :
    (TransactionState.ofBlock block).getStorage address key = 0 := by
  have hnc : ¬HasNonceOrCode tx address := fun h => h.ne_empty hempty
  have hslot := (valid.plain address hnc).2.2 key
  have hzero := valid.emptyStorage address hempty key
  unfold TransactionState.getStorage at hzero ⊢
  rw [hslot, valid.parent] at hzero
  by_cases hclear : address ∈ tx.storageClears
  · exact valid.clears address hclear key
  · simp only [hclear, ↓reduceIte] at hzero
    have hnone : (TransactionState.ofBlock block).storageWrites.slot address key = none := by
      simp [TransactionState.ofBlock, StorageMap.slot]
    have hnot : address ∉ (TransactionState.ofBlock block).storageClears := by
      simp [TransactionState.ofBlock]
    simp only [hnone, hnot, ↓reduceIte]
    exact hzero

/-! ## Transitions on `TransactionState` -/

/-- An account with a nonce or code is not empty when set. -/
private theorem accountExistsAndIsEmpty_setAccount_of_hasNonceOrCode
    {tx : TransactionState} {address : Address} {account : Account}
    (h : 1 ≤ account.nonce ∨ account.codeHash ≠ EMPTY_CODE_HASH) :
    (tx.setAccount address (some account)).accountExistsAndIsEmpty address = false := by
  rcases h with hn | hc
  · have hne : account.nonce ≠ 0 := by omega
    simp [TransactionState.accountExistsAndIsEmpty,
      TransactionState.getAccountOptional_setAccount_self, hne]
  · exact TransactionState.accountExistsAndIsEmpty_setAccount_of_code hc

/-- A change whose result has a nonce or code records a read, then sets the account. -/
private theorem modifyState_eq_of_hasNonceOrCode {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx')
    (keeps : ∀ account, f (tx.getAccount address) = .ok account →
      1 ≤ account.nonce ∨ account.codeHash ≠ EMPTY_CODE_HASH) :
    ∃ account, f (tx.getAccount address) = .ok account ∧
      tx' = (tx.recordAccountRead address).setAccount address (some account) := by
  obtain ⟨account, hf, rfl⟩ := TransactionState.modifyState_eq_ok_iff.mp h
  refine ⟨account, hf, ?_⟩
  split
  · rename_i hc
    simp [accountExistsAndIsEmpty_setAccount_of_hasNonceOrCode (keeps account hf)] at hc
  · rfl

/-- Writing storage at an account with a nonce or code keeps `RebuildState`. -/
theorem RebuildState.setStorage {block : BlockState} {tx tx' : TransactionState}
    {address : Address} {key : Bytes32} {value : U256}
    (valid : RebuildState block tx) (hnc : HasNonceOrCode tx address)
    (h : tx.setStorage address key value = .ok tx') :
    RebuildState block tx' ∧ KeepsNonceOrCode tx tx' := by
  have hacc : ∀ other, tx'.getAccount other = tx.getAccount other := by
    intro other
    simp only [TransactionState.getAccount, TransactionState.getAccountOptional_setStorage h]
  have hk : KeepsNonceOrCode tx tx' :=
    ⟨nonceLe_setStorage h, fun other hc => (HasNonceOrCode.congr (hacc other)).mpr hc⟩
  refine ⟨?_, hk⟩
  unfold TransactionState.setStorage at h
  split at h
  · cases h
  cases h
  refine ⟨valid.parent, valid.code, ?_, valid.clears, ?_⟩
  · intro other hempty slot
    have hne : other ≠ address := fun heq => by
      subst heq
      exact hnc.ne_empty ((hacc other).symm.trans hempty)
    have hget :
        ({ (tx.recordAccountRead address) with
            storageWrites := (tx.recordAccountRead address).storageWrites.insert address
              (((tx.recordAccountRead address).storageWrites.getD address ∅).insert key value) }
          : TransactionState).getStorage other slot = tx.getStorage other slot := by
      simp [TransactionState.getStorage, StorageMap.slot, TransactionState.recordAccountRead,
        Std.ExtTreeMap.getElem?_insert, Ne.symm hne] <;> rfl
    rw [hget]
    exact valid.emptyStorage other ((hacc other).symm.trans hempty) slot
  · intro other hnot
    have hnot' : ¬HasNonceOrCode tx other :=
      fun hc => hnot ((HasNonceOrCode.congr (hacc other)).mpr hc)
    have hne : other ≠ address := fun heq => hnot' (heq ▸ hnc)
    obtain ⟨hb0, hbal, hslot⟩ := valid.plain other hnot'
    refine ⟨hb0, ?_, fun slot => ?_⟩
    · rw [hacc other]
      exact hbal
    · simp only [StorageMap.slot, TransactionState.recordAccountRead,
        Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq, eq_comm (a := address),
        hne, ↓reduceIte]
      exact hslot slot

/-- Writing transient storage keeps `RebuildState`. -/
theorem RebuildState.setTransientStorage {block : BlockState} {tx : TransactionState}
    (valid : RebuildState block tx) (address : Address) (key : Bytes32) (value : U256) :
    RebuildState block (tx.setTransientStorage address key value) ∧
      KeepsNonceOrCode tx (tx.setTransientStorage address key value) :=
  ⟨⟨valid.parent, valid.code, valid.emptyStorage, valid.clears, valid.plain⟩,
    ⟨fun _ => Nat.le_refl _, fun _ h => h⟩⟩

/-- Touching an account keeps `RebuildState`. -/
theorem RebuildState.touchAccount {block : BlockState} {tx : TransactionState}
    (valid : RebuildState block tx) (address : Address) :
    RebuildState block (tx.touchAccount address) ∧
      KeepsNonceOrCode tx (tx.touchAccount address) := by
  have hacc : ∀ other, (tx.touchAccount address).getAccount other = tx.getAccount other := by
    intro other
    by_cases hne : other = address
    · subst hne
      exact TransactionState.getAccount_touchAccount_self tx other
    · exact TransactionState.getAccount_touchAccount hne
  have hst : ∀ other key,
      (tx.touchAccount address).getStorage other key = tx.getStorage other key := by
    intro other key
    unfold TransactionState.touchAccount
    split <;> rfl
  have hclears : (tx.touchAccount address).storageClears = tx.storageClears := by
    unfold TransactionState.touchAccount
    split <;> rfl
  have hwrites : (tx.touchAccount address).storageWrites = tx.storageWrites := by
    unfold TransactionState.touchAccount
    split <;> rfl
  refine ⟨⟨(TransactionState.parent_touchAccount tx address).trans valid.parent,
      fun hash code hread => valid.code hash code
        ((TransactionState.getCode_touchAccount tx address hash).symm.trans hread),
      fun other hempty key => by
        rw [hst other key]
        exact valid.emptyStorage other ((hacc other).symm.trans hempty) key,
      fun other hmem key => valid.clears other (hclears ▸ hmem) key,
      fun other hnot => by
        have hnot' : ¬HasNonceOrCode tx other :=
          fun hc => hnot ((HasNonceOrCode.congr (hacc other)).mpr hc)
        obtain ⟨hb0, hbal, hslot⟩ := valid.plain other hnot'
        refine ⟨hb0, ?_, fun key => ?_⟩
        · rw [hacc other]
          exact hbal
        · rw [hwrites]
          exact hslot key⟩,
    ⟨nonceLe_touchAccount tx address,
      fun other hc => (HasNonceOrCode.congr (hacc other)).mpr hc⟩⟩

/-- Raising the nonce of an account keeps `RebuildState`. -/
theorem RebuildState.incrementNonce {block : BlockState} {tx tx' : TransactionState}
    {address : Address} (valid : RebuildState block tx)
    (h : tx.incrementNonce fork address = .ok tx') :
    RebuildState block tx' ∧ KeepsNonceOrCode tx tx' ∧ HasNonceOrCode tx' address := by
  obtain ⟨account, hf, htx'⟩ := modifyState_eq_of_hasNonceOrCode h fun acc hacc => by
    cases hacc
    exact .inl (Nat.succ_le_succ (Nat.zero_le _))
  cases hf
  obtain ⟨hself, hother⟩ := TransactionState.getAccount_incrementNonce h
  have hnc_self : HasNonceOrCode tx' address := by
    left
    rw [hself]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hk : KeepsNonceOrCode tx tx' := by
    refine ⟨nonceLe_incrementNonce h, fun other hc => ?_⟩
    by_cases hne : other = address
    · exact hne ▸ hnc_self
    · have ho : tx'.getAccount other = tx.getAccount other := by
        simp only [TransactionState.getAccount, hother other hne]
      exact (HasNonceOrCode.congr ho).mpr hc
  refine ⟨?_, hk, hnc_self⟩
  have hp : tx'.parent = block := (TransactionState.parent_incrementNonce h).trans valid.parent
  have hclears : tx'.storageClears = tx.storageClears := by subst htx'; rfl
  have hwrites : tx'.storageWrites = tx.storageWrites := by subst htx'; rfl
  have hst : ∀ other key, tx'.getStorage other key = tx.getStorage other key := by
    subst htx'; intros; rfl
  refine ⟨hp, fun hash code hread => valid.code hash code
      ((TransactionState.getCode_modifyState h) ▸ hread),
    fun other hempty key => ?_,
    fun other hmem key => valid.clears other (hclears ▸ hmem) key,
    fun other hnot => ?_⟩
  · have hne : other ≠ address := fun heq => hnc_self.ne_empty (heq ▸ hempty)
    have ho : tx'.getAccount other = tx.getAccount other := by
      simp only [TransactionState.getAccount, hother other hne]
    rw [hst other key]
    exact valid.emptyStorage other (ho.symm.trans hempty) key
  · have hne : other ≠ address := fun heq => hnot (heq ▸ hnc_self)
    have ho : tx'.getAccount other = tx.getAccount other := by
      simp only [TransactionState.getAccount, hother other hne]
    have hnot' : ¬HasNonceOrCode tx other :=
      fun hc => hnot ((HasNonceOrCode.congr ho).mpr hc)
    obtain ⟨hb0, hbal, hslot⟩ := valid.plain other hnot'
    refine ⟨hb0, ?_, fun key => ?_⟩
    · rw [ho]
      exact hbal
    · rw [hwrites]
      exact hslot key

/-- Adding ether to `target` keeps `RebuildState`. -/
theorem RebuildState.createEther {block : BlockState} {tx tx' : TransactionState}
    {target : Address} {amount : U256} (valid : RebuildState block tx)
    (h : tx.createEther fork target amount = .ok tx') :
    RebuildState block tx' ∧ KeepsNonceOrCode tx tx' := by
  have hk : KeepsNonceOrCode tx tx' := by
    refine ⟨nonceLe_createEther h, fun other hc => ?_⟩
    obtain ⟨-, hn, hcode⟩ := TransactionState.getAccount_createEther h other
    rcases hc with h1 | h2
    · exact .inl (hn ▸ h1)
    · exact .inr (hcode ▸ h2)
  refine ⟨?_, hk⟩
  have hp : tx'.parent = block := (TransactionState.parent_createEther h).trans valid.parent
  have hcode : ∀ hash code, tx'.getCode hash = .ok code → keccak256 code = hash :=
    fun hash code hread => valid.code hash code ((TransactionState.getCode_modifyState h) ▸ hread)
  have hempty_of_empty : ∀ other, tx'.getAccount other = EMPTY_ACCOUNT →
      tx.getAccount other = EMPTY_ACCOUNT := by
    intro other hempty
    obtain ⟨hbal, hn, hc⟩ := TransactionState.getAccount_createEther h other
    cases hold : tx.getAccount other with
    | mk n b c =>
      simp only [hold, hempty, EMPTY_ACCOUNT] at hbal hn hc ⊢
      change 0 = b.toNat + _ at hbal
      have hb : b = 0 := BitVec.eq_of_toNat_eq (by change b.toNat = 0; omega)
      subst n; subst c; subst b; rfl
  refine ⟨hp, hcode, ?_, ?_, ?_⟩
  · intro other hempty key
    rw [TransactionState.getStorage_modifyState h]
    split
    · rfl
    · exact valid.emptyStorage other (hempty_of_empty other hempty) key
  · intro other hmem key
    obtain ⟨account, hf, hdef⟩ := TransactionState.modifyState_eq_ok_iff.mp h
    rw [hdef] at hmem
    split at hmem
    · rename_i hdel
      have hempty_acc : account = EMPTY_ACCOUNT := by
        have he := TransactionState.eq_empty_of_accountExistsAndIsEmpty
          (Bool.and_eq_true_iff.mp hdel).2
        simpa [TransactionState.getAccount, TransactionState.getAccountOptional_setAccount_self]
          using he
      have htx'_empty : tx'.getAccount target = EMPTY_ACCOUNT := by
        obtain ⟨acc, hf', hself, -⟩ := TransactionState.modifyState_eq_ok h
        rw [hf, Except.ok.injEq] at hf'
        subst hf'
        exact hself.trans hempty_acc
      simp only [TransactionState.destroyAccount, TransactionState.setAccount,
        TransactionState.destroyStorage, TransactionState.recordAccountRead,
        Std.ExtTreeSet.mem_insert, Std.compare_eq_iff_eq] at hmem
      rcases hmem with rfl | hmem
      · exact valid.blockStorage_of_empty (hempty_of_empty _ htx'_empty) key
      · exact valid.clears other hmem key
    · exact valid.clears other hmem key
  · intro other hnot
    have hnot' : ¬HasNonceOrCode tx other := fun hc => hnot (hk.2 other hc)
    obtain ⟨hb0, hbal, hslot⟩ := valid.plain other hnot'
    obtain ⟨hbal_eq, -, -⟩ := TransactionState.getAccount_createEther h other
    refine ⟨hb0, ?_, fun key => ?_⟩
    · apply BitVec.le_def.mpr
      have hle : ((TransactionState.ofBlock block).getAccount other).balance.toNat ≤
          (tx.getAccount other).balance.toNat := BitVec.le_def.mp hbal
      omega
    · obtain ⟨account, -, rfl⟩ := TransactionState.modifyState_eq_ok_iff.mp h
      split
      · by_cases hne : other = target
        · subst hne
          simp [TransactionState.destroyAccount, TransactionState.setAccount,
            TransactionState.destroyStorage, StorageMap.slot]
        · simp only [TransactionState.destroyAccount, TransactionState.setAccount,
            TransactionState.destroyStorage, TransactionState.recordAccountRead,
            StorageMap.slot, Std.ExtTreeMap.getElem?_erase, Std.compare_eq_iff_eq,
            eq_comm (a := target), hne, ↓reduceIte]
          exact hslot key
      · exact hslot key

/-- Changing an account that keeps a nonce or code keeps `RebuildState`. -/
private theorem RebuildState.modifyState_of_hasNonceOrCode {block : BlockState}
    {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (valid : RebuildState block tx)
    (h : tx.modifyState fork address f = .ok tx')
    (hnonce : ∀ account, f (tx.getAccount address) = .ok account →
      (tx.getAccount address).nonce ≤ account.nonce)
    (hkeeps : ∀ account, f (tx.getAccount address) = .ok account →
      1 ≤ account.nonce ∨ account.codeHash ≠ EMPTY_CODE_HASH) :
    RebuildState block tx' ∧ KeepsNonceOrCode tx tx' ∧ HasNonceOrCode tx' address := by
  obtain ⟨account, hf, htx'⟩ := modifyState_eq_of_hasNonceOrCode h hkeeps
  obtain ⟨acc', hf', hself, hother⟩ := TransactionState.modifyState_eq_ok h
  rw [hf, Except.ok.injEq] at hf'
  subst hf'
  have hnc_self : HasNonceOrCode tx' address := by
    unfold HasNonceOrCode
    rw [hself]
    exact hkeeps account hf
  have hk : KeepsNonceOrCode tx tx' := by
    refine ⟨fun other => ?_, fun other hc => ?_⟩
    · by_cases hne : other = address
      · subst hne
        rw [hself]
        exact hnonce account hf
      · rw [hother other hne]
        exact Nat.le_refl _
    · by_cases hne : other = address
      · exact hne ▸ hnc_self
      · exact (HasNonceOrCode.congr (hother other hne)).mpr hc
  refine ⟨?_, hk, hnc_self⟩
  have hp : tx'.parent = block := (TransactionState.parent_modifyState h).trans valid.parent
  have hclears : tx'.storageClears = tx.storageClears := by subst htx'; rfl
  have hwrites : tx'.storageWrites = tx.storageWrites := by subst htx'; rfl
  have hst : ∀ other key, tx'.getStorage other key = tx.getStorage other key := by
    subst htx'; intros; rfl
  refine ⟨hp, fun hash code hread => valid.code hash code
      ((TransactionState.getCode_modifyState h) ▸ hread),
    fun other hempty key => ?_,
    fun other hmem key => valid.clears other (hclears ▸ hmem) key,
    fun other hnot => ?_⟩
  · have hne : other ≠ address := fun heq => hnc_self.ne_empty (heq ▸ hempty)
    rw [hst other key]
    exact valid.emptyStorage other ((hother other hne).symm.trans hempty) key
  · have hne : other ≠ address := fun heq => hnot (heq ▸ hnc_self)
    have hnot' : ¬HasNonceOrCode tx other :=
      fun hc => hnot ((HasNonceOrCode.congr (hother other hne)).mpr hc)
    obtain ⟨hb0, hbal, hslot⟩ := valid.plain other hnot'
    refine ⟨hb0, ?_, fun key => ?_⟩
    · rw [hother other hne]
      exact hbal
    · rw [hwrites]
      exact hslot key

/-- Setting the balance of an account that has a nonce or code keeps `RebuildState`. -/
theorem RebuildState.setAccountBalance {block : BlockState} {tx tx' : TransactionState}
    {address : Address} {amount : U256} (valid : RebuildState block tx)
    (hnc : HasNonceOrCode tx address) (h : tx.setAccountBalance fork address amount = .ok tx') :
    RebuildState block tx' ∧ KeepsNonceOrCode tx tx' := by
  obtain ⟨valid', hk, -⟩ := valid.modifyState_of_hasNonceOrCode h
    (fun account hf => by cases hf; exact Nat.le_refl _)
    (fun account hf => by cases hf; exact hnc)
  exact ⟨valid', hk⟩

/-- Moving ether from an account that has a nonce or code keeps `RebuildState`. -/
theorem RebuildState.moveEther {block : BlockState} {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256} (valid : RebuildState block tx)
    (hnc : HasNonceOrCode tx sender) (h : tx.moveEther fork sender recipient amount = .ok tx') :
    RebuildState block tx' ∧ KeepsNonceOrCode tx tx' := by
  obtain ⟨debited, hdeb, hcred⟩ := Base.bind_ok_iff.mp h
  have hdebit : ∀ account, Account.debit sender amount (tx.getAccount sender) = .ok account →
      account.nonce = (tx.getAccount sender).nonce ∧
        account.codeHash = (tx.getAccount sender).codeHash := by
    intro account hf
    unfold Account.debit at hf
    split at hf
    · cases hf
    · cases hf
      exact ⟨rfl, rfl⟩
  obtain ⟨v1, k1, -⟩ := valid.modifyState_of_hasNonceOrCode hdeb
    (fun account hf => by rw [(hdebit account hf).1]; exact Nat.le_refl _)
    (fun account hf => by
      obtain ⟨hn, hc⟩ := hdebit account hf
      rw [hn, hc]
      exact hnc)
  obtain ⟨v2, k2⟩ := v1.createEther hcred
  exact ⟨v2, k1.trans k2⟩

/-- The balance transfer of SELFDESTRUCT from an account with a nonce or code keeps `RebuildState`.
-/
theorem RebuildState.selfdestructTransfer {block : BlockState} {tx tx' : TransactionState}
    {originator beneficiary : Address} (valid : RebuildState block tx)
    (hnc : HasNonceOrCode tx originator)
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    RebuildState block tx' ∧ KeepsNonceOrCode tx tx' := by
  unfold Evm.selfdestructTransfer at h
  dsimp only at h
  split at h
  · obtain ⟨moved, hm, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨v1, k1⟩ := valid.moveEther hnc hm
    split at h
    · obtain ⟨v2, k2⟩ := v1.setAccountBalance (k1.2 originator hnc) h
      exact ⟨v2, k1.trans k2⟩
    · cases h
      exact ⟨v1, k1⟩
  · obtain ⟨credited, hc, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨v1, k1⟩ := valid.createEther hc
    obtain ⟨v2, k2⟩ := v1.setAccountBalance (k1.2 originator hnc) h
    exact ⟨v2, k1.trans k2⟩

/-- Wiping the storage of a deployable address and marking it created keeps `RebuildState`. -/
private theorem RebuildState.destroyStorage_markAccountCreated {block : BlockState}
    {tx : TransactionState} {address : Address} (valid : RebuildState block tx)
    (hdep : tx.accountDeployable address = true) :
    let wiped := (tx.destroyStorage address).markAccountCreated address
    RebuildState block wiped ∧ KeepsNonceOrCode tx wiped := by
  obtain ⟨hn0, hc0, hst0⟩ := TransactionState.accountDeployable_eq_true_iff.mp hdep
  have hnot_addr : ¬HasNonceOrCode tx address := by
    rintro (hn | hc)
    · omega
    · exact hc hc0
  have hblock_zero : ∀ key, (TransactionState.ofBlock block).getStorage address key = 0 := by
    intro key
    have hslot := (valid.plain address hnot_addr).2.2 key
    have hz := hst0 key
    unfold TransactionState.getStorage at hz ⊢
    rw [hslot, valid.parent] at hz
    by_cases hclear : address ∈ tx.storageClears
    · exact valid.clears address hclear key
    · simp only [hclear, ↓reduceIte] at hz
      have hnone : (TransactionState.ofBlock block).storageWrites.slot address key = none := by
        simp [TransactionState.ofBlock, StorageMap.slot]
      have hnot : address ∉ (TransactionState.ofBlock block).storageClears := by
        simp [TransactionState.ofBlock]
      simp only [hnone, hnot, ↓reduceIte]
      exact hz
  dsimp only
  have hacc : ∀ other,
      ((tx.destroyStorage address).markAccountCreated address).getAccount other =
        tx.getAccount other := fun _ => rfl
  refine ⟨⟨valid.parent, valid.code, ?_, ?_, ?_⟩,
    ⟨fun _ => Nat.le_refl _, fun _ h => h⟩⟩
  · intro other hempty key
    by_cases hne : other = address
    · subst hne
      simp [TransactionState.markAccountCreated, TransactionState.destroyStorage,
        TransactionState.getStorage, StorageMap.slot]
    · have hget : ((tx.destroyStorage address).markAccountCreated address).getStorage other key =
          tx.getStorage other key := by
        simp only [TransactionState.markAccountCreated, TransactionState.destroyStorage,
          TransactionState.getStorage, StorageMap.slot, Std.ExtTreeMap.getElem?_erase,
          Std.ExtTreeSet.mem_insert, Std.compare_eq_iff_eq, eq_comm (a := address), hne,
          false_or, ↓reduceIte]
        rfl
      rw [hget]
      exact valid.emptyStorage other hempty key
  · intro other hmem key
    simp only [TransactionState.markAccountCreated, TransactionState.destroyStorage,
      Std.ExtTreeSet.mem_insert, Std.compare_eq_iff_eq] at hmem
    rcases hmem with rfl | hmem
    · exact hblock_zero key
    · exact valid.clears other hmem key
  · intro other hnot
    obtain ⟨hb0, hbal, hslot⟩ := valid.plain other hnot
    refine ⟨hb0, hbal, fun key => ?_⟩
    by_cases hne : other = address
    · subst hne
      simp [TransactionState.markAccountCreated, TransactionState.destroyStorage, StorageMap.slot]
    · simp only [TransactionState.markAccountCreated, TransactionState.destroyStorage,
        StorageMap.slot, Std.ExtTreeMap.getElem?_erase, Std.compare_eq_iff_eq,
        eq_comm (a := address), hne, ↓reduceIte]
      exact hslot key

/-- From Spurious Dragon, preparing a creation at a deployable address keeps `RebuildState`.

It also raises the nonce of the new address to at least 1. -/
theorem RebuildState.prepareCreation (hfork : .spuriousDragon ≤ fork) {block : BlockState}
    {tx prepared : TransactionState} {address : Address} (valid : RebuildState block tx)
    (hdep : tx.accountDeployable address = true)
    (h : prepareCreation fork tx address = .ok prepared) :
    RebuildState block prepared ∧ KeepsNonceOrCode tx prepared ∧
      1 ≤ (prepared.getAccount address).nonce := by
  unfold Evm.prepareCreation at h
  simp only [show fork ≥ .spuriousDragon from hfork, ↓reduceIte] at h
  have hinc := Base.mapError_ok_iff.mp h
  obtain ⟨v1, k1⟩ := valid.destroyStorage_markAccountCreated hdep
  obtain ⟨v2, k2, -⟩ := v1.incrementNonce hinc
  obtain ⟨hself, -⟩ := TransactionState.getAccount_incrementNonce hinc
  refine ⟨v2, k1.trans k2, ?_⟩
  rw [hself]
  exact Nat.succ_le_of_lt (Nat.succ_pos _)

/-- Setting the code of an account with a positive nonce keeps `RebuildState`. -/
theorem RebuildState.setCode {block : BlockState} {tx tx' : TransactionState}
    {address : Address} {code : ByteArray} (valid : RebuildState block tx)
    (hnonce : 1 ≤ (tx.getAccount address).nonce) (h : tx.setCode fork address code = .ok tx') :
    RebuildState block tx' ∧ KeepsNonceOrCode tx tx' := by
  have hcode : ∀ hash bytes, tx'.getCode hash = .ok bytes → keccak256 bytes = hash := by
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
      exact valid.code hash bytes hread
  dsimp only [TransactionState.setCode] at h
  split at h
  · obtain ⟨v, hk, -⟩ := valid.modifyState_of_hasNonceOrCode h
      (fun account hf => by cases hf; exact Nat.le_refl _)
      (fun account hf => by cases hf; exact .inl hnonce)
    exact ⟨v, hk⟩
  · rename_i hne_hash
    let mid : TransactionState :=
      { tx with codeWrites := tx.codeWrites.insert (keccak256 code) code }
    have hmid : RebuildState block mid :=
      ⟨valid.parent,
        fun hash bytes hread => by
          rw [← TransactionState.getCode_modifyState h] at hread
          exact hcode hash bytes hread,
        valid.emptyStorage, valid.clears, valid.plain⟩
    obtain ⟨v, hk, -⟩ := hmid.modifyState_of_hasNonceOrCode h
      (fun account hf => by cases hf; exact Nat.le_refl _)
      (fun account hf => by cases hf; exact .inl hnonce)
    exact ⟨v, hk⟩

/-- Depositing code after a creation whose target has a positive nonce keeps `RebuildState`. -/
theorem RebuildState.depositCode {block : BlockState} {snapshot : TransactionState}
    {evm after : Evm fork Meter} (vsnap : RebuildState block snapshot)
    (vevm : RebuildState block evm.state) (hk : KeepsNonceOrCode snapshot evm.state)
    (hnonce : 1 ≤ (evm.state.getAccount evm.message.currentTarget).nonce)
    (h : depositCode fork snapshot evm = .ok after) :
    RebuildState block after.state ∧ KeepsNonceOrCode snapshot after.state := by
  obtain ⟨-, -, hcases⟩ := depositCode_cases h
  rcases hcases with hrest | hsame | hset
  · rw [hrest]
    have hsw := sameWrites_restoreTxState evm.state snapshot
    have hp : (evm.state.restoreTxState snapshot).parent = snapshot.parent :=
      vevm.parent.trans vsnap.parent.symm
    exact ⟨vsnap.of_sameWrites hsw hp, hsw.keepsNonceOrCode hp⟩
  · rw [hsame]
    exact ⟨vevm, hk⟩
  · obtain ⟨vafter, kafter⟩ := vevm.setCode hnonce hset
    exact ⟨vafter, hk.trans kafter⟩

/-- Starting the state of a call keeps `RebuildState`. -/
theorem RebuildState.startState {block : BlockState} {tx : TransactionState}
    (valid : RebuildState block tx) (message : Message fork) :
    RebuildState block (startState fork message tx) ∧
      KeepsNonceOrCode tx (startState fork message tx) := by
  unfold Evm.startState
  split
  · exact valid.touchAccount message.currentTarget
  · exact ⟨valid, .refl tx⟩

/-- Rolling back on error to a snapshot with `RebuildState` keeps `RebuildState`. -/
theorem RebuildState.rollbackOnError {block : BlockState} {snapshot : TransactionState}
    {ended : Evm fork Meter} (vsnap : RebuildState block snapshot)
    (vended : RebuildState block ended.state) (hk : KeepsNonceOrCode snapshot ended.state) :
    RebuildState block (rollbackOnError snapshot ended).state ∧
      KeepsNonceOrCode snapshot (rollbackOnError snapshot ended).state := by
  unfold Evm.rollbackOnError
  split
  · dsimp only
    have hsw := sameWrites_restoreTxState ended.state snapshot
    have hp : (ended.state.restoreTxState snapshot).parent = snapshot.parent :=
      vended.parent.trans vsnap.parent.symm
    exact ⟨vsnap.of_sameWrites hsw hp, hsw.keepsNonceOrCode hp⟩
  · exact ⟨vended, hk⟩

/-! ## Steps of an EVM frame -/

/-- A step that keeps `RebuildState`, nonces and code hashes, the message, and the code. -/
private def RebuildStep (block : BlockState) (a b : Evm fork Meter) : Prop :=
  (RebuildState block a.state → RebuildState block b.state ∧ KeepsNonceOrCode a.state b.state) ∧
    b.message = a.message ∧ b.code = a.code

omit [GasMeter Meter] in
private theorem RebuildStep.refl {block : BlockState} (evm : Evm fork Meter) :
    RebuildStep block evm evm :=
  ⟨fun valid => ⟨valid, .refl evm.state⟩, rfl, rfl⟩

omit [GasMeter Meter] in
private theorem RebuildStep.trans {block : BlockState} {a b c : Evm fork Meter}
    (hab : RebuildStep block a b) (hbc : RebuildStep block b c) : RebuildStep block a c :=
  ⟨fun va => by
      obtain ⟨vb, kb⟩ := hab.1 va
      obtain ⟨vc, kc⟩ := hbc.1 vb
      exact ⟨vc, kb.trans kc⟩,
    hbc.2.1.trans hab.2.1, hbc.2.2.trans hab.2.2⟩

omit [GasMeter Meter] in
private theorem RebuildStep.of_sameWrites {block : BlockState} {a b : Evm fork Meter}
    (hsw : SameWrites b.state a.state) (hp : b.state.parent = a.state.parent)
    (hm : b.message = a.message) (hc : b.code = a.code) : RebuildStep block a b :=
  ⟨fun va => ⟨va.of_sameWrites hsw hp, hsw.keepsNonceOrCode hp⟩, hm, hc⟩

omit [GasMeter Meter] in
private theorem RebuildStep.of_sameContext {block : BlockState} {a b : Evm fork Meter}
    (h : SameContext a b) : RebuildStep block a b :=
  RebuildStep.of_sameWrites ⟨by rw [h.state], by rw [h.state], by rw [h.state], by rw [h.state],
    by rw [h.state]⟩ (by rw [h.state]) h.message h.code

omit [GasMeter Meter] in
private theorem RebuildStep.advance {block : BlockState} {a b : Evm fork Meter}
    (h : RebuildStep block a b) (n : Nat := 1) : RebuildStep block a (Evm.advance b n) :=
  h

omit [GasMeter Meter] in
private theorem rebuildStep_recordAccountRead {block : BlockState} (evm : Evm fork Meter)
    (address : Address) : RebuildStep block evm (recordAccountRead evm address) :=
  RebuildStep.of_sameWrites (SameWrites.recordAccountRead evm.state address) rfl rfl rfl

omit [GasMeter Meter] in
private theorem rebuildStep_recordStorageRead {block : BlockState} (evm : Evm fork Meter)
    (address : Address) (key : Bytes32) :
    RebuildStep block evm (recordStorageRead evm address key) :=
  RebuildStep.of_sameWrites (SameWrites.recordStorageRead evm.state address key) rfl rfl rfl

omit [GasMeter Meter] in
private theorem rebuildStep_accessAddress {block : BlockState} (evm : Evm fork Meter)
    (address : Address) : RebuildStep block evm (accessAddress evm address).2 := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  rw [h]
  exact .refl _

omit [GasMeter Meter] in
private theorem rebuildStep_accessStorageKey {block : BlockState} (evm : Evm fork Meter)
    (address : Address) (key : Bytes32) :
    RebuildStep block evm (accessStorageKey evm address key).2 := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm address key
  rw [h]
  exact .refl _

private theorem rebuildStep_exceptionalHalt {block : BlockState} (evm : Evm fork Meter)
    (e : EvmError) : RebuildStep block evm (exceptionalHalt evm e) :=
  RebuildStep.of_sameWrites ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl

private theorem rebuildStep_skipCall {block : BlockState} {evm after : Evm fork Meter}
    {gas reservoir : Nat} (h : skipCall evm gas reservoir = .ok after) :
    RebuildStep block evm after := by
  obtain ⟨_, -, rfl⟩ := skipCall_eq_ok h
  exact RebuildStep.of_sameWrites ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl

private theorem rebuildStep_runPrecompile {block : BlockState} {address : Nat}
    {evm after : Evm fork Meter} (h : runPrecompile fork address evm = some after) :
    RebuildStep block evm after := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    exact rebuildStep_exceptionalHalt evm .precompile
  · split at h
    · cases h
      exact rebuildStep_exceptionalHalt evm _
    · cases h
      exact RebuildStep.of_sameWrites ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl

private theorem rebuildStep_returnOpStep {block : BlockState} {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some run) {evm after : Evm fork Meter}
    (h : run evm = .ok after) : RebuildStep block evm after := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  case «return» =>
    subst hstep
    exact RebuildStep.of_sameContext (returnStep_sameContext h)
  case revert =>
    split at hstep
    · cases hstep
      exact RebuildStep.of_sameContext (revertStep_sameContext h)
    · cases hstep

private theorem rebuildStep_accountStep {block : BlockState} {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some run) {evm after : Evm fork Meter}
    (h : run evm = .ok after) : RebuildStep block evm after := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  case balance =>
    subst hstep
    obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
    simp only [hacc] at h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have ha : RebuildStep block e1 e2 := by
      have := rebuildStep_accessAddress (block := block) e1 (toAddressMasked w)
      rwa [hacc] at this
    exact ((((RebuildStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
      (.of_sameContext (chargeGas_sameContext h3))).trans
      (rebuildStep_recordAccountRead _ _)).trans
      (.of_sameContext (pushWord_sameContext h4)) |>.advance
  case extcodesize =>
    subst hstep
    obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
    simp only [hacc] at h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have ha : RebuildStep block e1 e2 := by
      have := rebuildStep_accessAddress (block := block) e1 (toAddressMasked w)
      rwa [hacc] at this
    exact ((((RebuildStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
      (.of_sameContext (chargeGas_sameContext h3))).trans
      (rebuildStep_recordAccountRead _ _)).trans
      (.of_sameContext (pushWord_sameContext h5)) |>.advance
  case extcodecopy =>
    subst hstep
    obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    rcases hacc : accessAddress e4 (toAddressMasked w) with ⟨cold, e5⟩
    simp only [hacc] at h
    obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have ha : RebuildStep block e4 e5 := by
      have := rebuildStep_accessAddress (block := block) e4 (toAddressMasked w)
      rwa [hacc] at this
    exact (((((((RebuildStep.of_sameContext (popWord_sameContext h1)).trans
      (.of_sameContext (popWord_sameContext h2))).trans
      (.of_sameContext (popWord_sameContext h3))).trans
      (.of_sameContext (popWord_sameContext h4))).trans ha).trans
      (.of_sameContext (chargeGasAndMemory_sameContext h6))).trans
      (rebuildStep_recordAccountRead _ _)).trans
      (RebuildStep.of_sameWrites ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl) |>.advance
  case selfbalance =>
    split at hstep
    · cases hstep
      exact (rebuildStep_recordAccountRead _ _).trans (.of_sameContext (readFrame_sameContext h))
    · cases hstep
  case extcodehash =>
    split at hstep
    · cases hstep
      obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
      simp only [hacc] at h
      obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      cases h
      have ha : RebuildStep block e1 e2 := by
        have := rebuildStep_accessAddress (block := block) e1 (toAddressMasked w)
        rwa [hacc] at this
      exact ((((RebuildStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
        (.of_sameContext (chargeGas_sameContext h3))).trans
        (rebuildStep_recordAccountRead _ _)).trans
        (.of_sameContext (pushWord_sameContext h4)) |>.advance
    · cases hstep

private theorem rebuildStep_sloadStep {block : BlockState} {evm after : Evm fork Meter}
    (h : sloadStep evm = .ok after) : RebuildStep block evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : RebuildStep block e1 e2 := by
    have := rebuildStep_accessStorageKey (block := block) e1 e1.message.currentTarget
      (U256.toBeBytes w)
    rwa [hacc] at this
  exact ((((RebuildStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (.of_sameContext (chargeGas_sameContext h3))).trans
    (rebuildStep_recordStorageRead _ _ _)).trans
    (.of_sameContext (pushWord_sameContext h4)) |>.advance

private theorem rebuildStep_sstoreStep {block : BlockState} {evm after : Evm fork Meter}
    (hnc : RebuildState block evm.state → HasNonceOrCode evm.state evm.message.currentTarget)
    (h : sstoreStep evm = .ok after) : RebuildStep block evm after := by
  unfold Evm.sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have sc2 := (popWord_sameContext h1).trans (popWord_sameContext h2)
  have c2 : RebuildStep block evm e2 := .of_sameContext sc2
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e3⟩
    have ha : RebuildStep block evm
        (recordStorageRead e3 e2.message.currentTarget (U256.toBeBytes k)) := by
      have := rebuildStep_accessStorageKey (block := block) e2 e2.message.currentTarget
        (U256.toBeBytes k)
      rw [hpair] at this
      exact (c2.trans this).trans (rebuildStep_recordStorageRead _ _ _)
    simp only [hpair] at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : RebuildStep block evm e5 :=
        ha.trans (.of_sameContext ((sameContext_refillStateGas _ _).trans
          ((chargeGas_sameContext h4).trans (chargeStateGas_sameContext h5))))
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
        cases h
        refine ⟨fun vevm => ?_, m5.2.1, m5.2.2⟩
        obtain ⟨ve5, ke5⟩ := m5.1 vevm
        have hcur : HasNonceOrCode e5.state e2.message.currentTarget :=
          ke5.2 _ (sc2.message.symm ▸ hnc vevm)
        obtain ⟨vst, kst⟩ := ve5.setStorage hcur (Base.mapError_ok_iff.mp hst)
        exact ⟨vst, ke5.trans kst⟩
    · exact ha.trans (rebuildStep_exceptionalHalt _ _)

private theorem rebuildStep_tstoreStep {block : BlockState} {evm after : Evm fork Meter}
    (h : tstoreStep evm = .ok after) : RebuildStep block evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    exact (RebuildStep.of_sameContext ((popWord_sameContext h1).trans
      ((popWord_sameContext h2).trans (chargeGas_sameContext h3)))).trans
      ⟨fun ve3 => ve3.setTransientStorage _ _ _, rfl, rfl⟩

private theorem rebuildStep_selfdestructStep {block : BlockState} {evm after : Evm fork Meter}
    (hnc : RebuildState block evm.state → HasNonceOrCode evm.state evm.message.currentTarget)
    (h : selfdestructStep fork evm = .ok after) : RebuildStep block evm after := by
  obtain ⟨word, -, paid, -, hpaid_static, hpaid_state, -, ⟨refund, finished⟩ | ⟨error, rfl⟩⟩ :=
    selfdestructStep_eq_ok h
  · have hpaid : RebuildStep block evm paid :=
      RebuildStep.of_sameWrites
        (hpaid_state ▸ SameWrites.recordAccountRead evm.state (toAddressMasked word))
        (by rw [hpaid_state]; rfl) hpaid_static.message hpaid_static.code
    unfold finishSelfdestruct at finished
    split at finished
    · cases finished
    · obtain ⟨state, hst, finished⟩ := Base.bind_ok_iff.mp finished
      cases finished
      refine ⟨fun vevm => ?_, hpaid.2.1, hpaid.2.2⟩
      obtain ⟨vpaid, kpaid⟩ := hpaid.1 vevm
      have hcur : HasNonceOrCode paid.state paid.message.currentTarget :=
        kpaid.2 _ (hpaid.2.1.symm ▸ hnc vevm)
      obtain ⟨vst, kst⟩ := vpaid.selfdestructTransfer hcur (Base.mapError_ok_iff.mp hst)
      exact ⟨vst, kpaid.trans kst⟩
  · have hpaid : RebuildStep block evm paid :=
      RebuildStep.of_sameWrites
        (hpaid_state ▸ SameWrites.recordAccountRead evm.state (toAddressMasked word))
        (by rw [hpaid_state]; rfl) hpaid_static.message hpaid_static.code
    exact hpaid.trans (rebuildStep_exceptionalHalt paid error)

private theorem rebuildStep_instruction {block : BlockState} {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hnc : RebuildState block evm.state → HasNonceOrCode evm.state evm.message.currentTarget)
    (hrun : instruction fork op = some run) (h : run evm = .ok after) :
    RebuildStep block evm after := by
  unfold Evm.instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact RebuildStep.of_sameContext (stackOnlyStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact RebuildStep.of_sameContext (controlFlowStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact RebuildStep.of_sameContext (memoryDataStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact rebuildStep_returnOpStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact RebuildStep.of_sameContext (environmentStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact rebuildStep_accountStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact rebuildStep_sloadStep h
    case sstore => subst hf; exact rebuildStep_sstoreStep hnc h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · exact RebuildStep.of_sameContext (tloadStep_sameContext h)
    · exact rebuildStep_tstoreStep h
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, hm, hc, hs, -⟩ := logStep_eq_ok h
    exact RebuildStep.of_sameWrites ⟨by rw [hs], by rw [hs], by rw [hs], by rw [hs], by rw [hs]⟩
      (by rw [hs]) hm hc
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact rebuildStep_selfdestructStep hnc h

private theorem rebuildStep_accessDelegation {block : BlockState} {evm after : Evm fork Meter}
    {address : Address} {known : Nat} {callee : Callee}
    (h : accessDelegation evm address known = .ok (callee, after)) :
    RebuildStep block evm after := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (rebuildStep_accessAddress _ _).trans (rebuildStep_recordAccountRead _ _)
  · cases h
    exact .refl _

private theorem rebuildStep_payCall {block : BlockState} {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    RebuildStep block evm after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((RebuildStep.of_sameContext (chargeGas_sameContext h1)).trans
      (.of_sameContext (chargeStateGas_sameContext h2))).trans
      (.of_sameContext (chargeGas_sameContext h3))
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact .of_sameContext (chargeGas_sameContext h1)

omit [GasMeter Meter] in
private theorem rebuildStep_popCallOperands {block : BlockState} {kind : CallKind}
    {evm after : Evm fork Meter} {call : CallOperands}
    (h : popCallOperands kind evm = .ok (call, after)) : RebuildStep block evm after := by
  have hs := (staticStep_popCallOperands h).1
  have hst : after.state = evm.state := by rw [popCallOperands_eq_ok h]
  exact RebuildStep.of_sameWrites ⟨by rw [hst], by rw [hst], by rw [hst], by rw [hst],
    by rw [hst]⟩ (by rw [hst]) hs.message hs.code

private theorem rebuildStep_incorporateChild {block : BlockState} {caller child : Evm fork Meter}
    (hc : RebuildState block caller.state →
      RebuildState block child.state ∧ KeepsNonceOrCode caller.state child.state) :
    RebuildStep block caller (incorporateChild fork caller child) :=
  ⟨fun vc => by
      rw [state_incorporateChild]
      exact hc vc,
    message_incorporateChild caller child, code_incorporateChild caller child⟩

private def RebuildChild (block : BlockState) (caller : Evm fork Meter) (message : Message fork)
    (child : Evm fork Meter) : Prop :=
  (message.shouldTransferValue = true → message.caller = caller.message.currentTarget) →
    RebuildState block caller.state →
      RebuildState block child.state ∧ KeepsNonceOrCode caller.state child.state

private theorem rebuildStep_finishCall {block : BlockState} {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall newAccount expandBy : Nat} {evm : Evm fork Meter}
    {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    result.Keeps (RebuildStep block) (RebuildChild block) evm := by
  unfold Evm.finishCall at h
  split at h
  · cases h
  dsimp only at h
  have pre : RebuildStep block evm (recordAccountRead { evm with
      memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
      evm.message.currentTarget) :=
    RebuildStep.of_sameWrites (SameWrites.recordAccountRead evm.state evm.message.currentTarget)
      rfl rfl rfl
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (pre.trans (.of_sameContext (sameContext_refillStateGas _ _))).trans
      (rebuildStep_skipCall hs)
  · unfold Evm.genericCall at h
    dsimp only at h
    split at h
    · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
      exact (((pre.trans (.of_sameContext (sameContext_returnData _ .empty))).trans
        (.of_sameContext (sameContext_refillStateGas _ newAccount))).trans
        (rebuildStep_skipCall hs))
    · cases h
      have callerStep : RebuildStep block evm _ :=
        pre.trans (.of_sameContext (sameContext_returnData _ .empty))
      refine ⟨callerStep, fun child after hres hc => ?_⟩
      obtain ⟨e, h1, hpure⟩ := Base.bind_ok_iff.mp hres
      cases hpure
      refine callerStep.trans ((rebuildStep_incorporateChild (hc fun htr => ?_)).trans
        (.of_sameContext (SameContext.trans ?_
          ((pushWord_sameContext h1).trans ⟨rfl, rfl, rfl, rfl⟩))))
      · have hk : kind ≠ .delegatecall := by
          intro heq
          subst heq
          simp at htr
        simp [hk]
        rfl
      · constructor <;> split <;> rfl

private theorem rebuildStep_callStep {block : BlockState} {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    result.Keeps (RebuildStep block) (RebuildChild block) evm := by
  unfold Evm.callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have c1 : RebuildStep block evm e1 := rebuildStep_popCallOperands h1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : RebuildStep block e1 e2 := by
    have := rebuildStep_accessAddress (block := block) e1 call.address
    rwa [hacc] at this
  have s3 : RebuildStep block evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (rebuildStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : RebuildStep block evm e4 := s3.trans (rebuildStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      exact StepResult.Keeps.lift (R := RebuildStep block) (C := RebuildChild block)
        RebuildStep.trans (s4.trans (rebuildStep_payCall h5)) (rebuildStep_finishCall h)
    · exact s4.trans (rebuildStep_exceptionalHalt _ _)
  · exact s3.trans (rebuildStep_exceptionalHalt _ _)

private theorem rebuildStep_launchCreate {block : BlockState} {evm : Evm fork Meter} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) :
    result.Keeps (RebuildStep block) (RebuildChild block) evm := by
  unfold Evm.launchCreate at h
  dsimp only at h
  have pre : RebuildStep block evm
      (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) :=
    (RebuildStep.of_sameContext (sameContext_returnData evm .empty)).trans
      (rebuildStep_recordAccountRead _ _)
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact pre.trans (rebuildStep_skipCall hs)
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 : RebuildStep block evm (recordAccountRead (accessAddress (recordAccountRead
      { evm with returnData := .empty } evm.message.currentTarget) address).2 address) :=
    (pre.trans (rebuildStep_accessAddress _ address)).trans
      (rebuildStep_recordAccountRead _ address)
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, hst, hr⟩ := Base.bind_ok_iff.mp hr
    have c2 : RebuildStep block evm e2 := c0.trans (.of_sameContext
      ((chargeStateGas_sameContext h1).trans (chargeGas_sameContext h2)))
    have ms : RebuildStep block evm { e2 with state } :=
      c2.trans ⟨fun ve2 => by
        obtain ⟨vst, kst, -⟩ := ve2.incrementNonce (Base.mapError_ok_iff.mp hst)
        exact ⟨vst, kst⟩, rfl, rfl⟩
    split at hr
    · cases hr
      have md : RebuildStep block evm { e2 with state, gas := GasMeter.drain e2.gas } :=
        ms.trans (.of_sameContext ⟨rfl, rfl, rfl, rfl⟩)
      refine ⟨md, fun child after hres hc => ?_⟩
      obtain ⟨e, hpush, hpure⟩ := Base.bind_ok_iff.mp hres
      cases hpure
      refine md.trans ((rebuildStep_incorporateChild (hc fun _ =>
        congrArg Message.currentTarget c2.2.1.symm)).trans
        (.of_sameContext (SameContext.trans ?_
          ((pushWord_sameContext hpush).trans ⟨rfl, rfl, rfl, rfl⟩))))
      constructor <;> split <;> rfl
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      exact ms.trans (.of_sameContext ((sameContext_refillStateGas _ _).trans
        ((pushWord_sameContext h3).trans ⟨rfl, rfl, rfl, rfl⟩)))
  · exact c0.trans (rebuildStep_exceptionalHalt _ _)

private theorem rebuildStep_createStep {block : BlockState} {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    result.Keeps (RebuildStep block) (RebuildChild block) evm := by
  obtain ⟨_, _, _, _, _, _, -, sc, -, -, -, launched⟩ := createStep_eq_ok h
  exact StepResult.Keeps.lift (R := RebuildStep block) (C := RebuildChild block)
    RebuildStep.trans (.of_sameContext sc) (rebuildStep_launchCreate launched)

private theorem rebuildStep_messageInstruction {block : BlockState} {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : result.Keeps (RebuildStep block) (RebuildChild block) evm := by
  unfold Evm.messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact rebuildStep_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact rebuildStep_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact rebuildStep_createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact rebuildStep_createStep h
         · cases hrun)

private theorem rebuildStep_step {block : BlockState} {evm : Evm fork Meter}
    {result : StepResult fork Meter}
    (hinv : evm.code.size ≠ 0 → RebuildState block evm.state →
      HasNonceOrCode evm.state evm.message.currentTarget)
    (h : step fork evm = .ok result) :
    result.Keeps (RebuildStep block) (RebuildChild block) evm ∧
      (∀ caller message resume, result = .child caller message resume →
        evm.code.size ≠ 0) := by
  unfold Evm.step at h
  split at h
  · rename_i within
    have hsize : evm.code.size ≠ 0 := by omega
    dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i run hop
        cases hr : run evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact ⟨rebuildStep_instruction (hinv hsize) hop hr, fun _ _ _ hc => by cases hc⟩
      · split at h
        · rename_i hcall
          exact ⟨rebuildStep_messageInstruction hcall h, fun _ _ _ _ => hsize⟩
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact ⟨RebuildStep.of_sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl),
      fun _ _ _ hc => by cases hc⟩

private theorem callStep_target_ne {kind : CallKind} {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : callStep kind evm = .ok (.child caller message resume)) : message.target ≠ none := by
  unfold Evm.callStep at h
  obtain ⟨⟨call, e1⟩, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h; cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨_, hc⟩
  · obtain ⟨⟨callee, e4⟩, -, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨_, hc⟩
    · obtain ⟨⟨subCall, e5⟩, -, h⟩ := Base.bind_ok_iff.mp h
      unfold Evm.finishCall at h
      split at h
      · cases h
      dsimp only at h
      split at h
      · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc
      · unfold Evm.genericCall at h
        dsimp only at h
        split at h
        · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc
        · cases h; simp
    · cases hc
  · cases hc

private theorem accountDeployable_of_create_step {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hnc : HasNonceOrCode evm.state evm.message.currentTarget)
    (h : step fork evm = .ok (.child caller message resume)) (ht : message.target = none) :
    caller.state.accountDeployable message.currentTarget = true ∧
      HasNonceOrCode caller.state message.caller := by
  have hdep : evm.state.accountDeployable message.currentTarget = true :=
    step_eq_child_deployable h ht
  unfold Evm.step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · rename_i op hop
      split at h
      · cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm <;>
          simp [hr, Functor.map, Except.map] at h
      · split at h
        · rename_i run hm
          unfold Evm.messageInstruction at hm
          cases hc : callInstruction (Meter := Meter) fork op with
          | some call =>
            simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hm
            subst hm
            have hcall_some : message.target ≠ none := by
              cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
              all_goals first
                | (subst hc; exact absurd ht (callStep_target_ne h))
                | (split at hc
                   · simp only [Option.some.injEq] at hc
                     subst hc
                     exact absurd ht (callStep_target_ne h)
                   · cases hc)
            exact absurd ht hcall_some
          | none =>
            simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hm
            have hcreate : ∃ b, run = createStep b := by
              cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hm
              all_goals first
                | (subst hm; exact ⟨_, rfl⟩)
                | (split at hm
                   · simp only [Option.some.injEq] at hm
                     subst hm
                     exact ⟨_, rfl⟩
                   · cases hm)
            obtain ⟨b, rfl⟩ := hcreate
            obtain ⟨_, _, _, _, _, paid, -, sc, -, -, -, launched⟩ := createStep_eq_ok h
            unfold Evm.launchCreate at launched
            dsimp only at launched
            split at launched
            · obtain ⟨_, _, hc'⟩ := Base.map_ok_iff.mp launched
              cases hc'
            obtain ⟨address, -, launched⟩ := Base.bind_ok_iff.mp launched
            rcases keepReads_eq_ok launched with hr | ⟨_, hc'⟩
            · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
              obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
              obtain ⟨state, hst, hr⟩ := Base.bind_ok_iff.mp hr
              split at hr
              · cases hr
                have hst' := Base.mapError_ok_iff.mp hst
                have sc_all := (chargeStateGas_sameContext h1).trans (chargeGas_sameContext h2)
                have hsw_e2 : SameWrites e2.state evm.state := by
                  rw [sc_all.state]
                  obtain ⟨_, ha⟩ := accessAddress_snd (recordAccountRead
                    { paid with returnData := .empty } paid.message.currentTarget) address
                  exact (SameWrites.recordAccountRead _ address).trans
                    (by
                      rw [ha]
                      exact (SameWrites.recordAccountRead paid.state _).trans
                        ⟨by rw [sc.state], by rw [sc.state], by rw [sc.state], by rw [sc.state],
                          by rw [sc.state]⟩)
                have hp_e2 : e2.state.parent = evm.state.parent := by
                  rw [sc_all.state]
                  obtain ⟨_, ha⟩ := accessAddress_snd (recordAccountRead
                    { paid with returnData := .empty } paid.message.currentTarget) address
                  change (recordAccountRead (accessAddress _ address).2 address).state.parent = _
                  rw [ha]
                  exact sc.state ▸ rfl
                obtain ⟨hself, hother⟩ := TransactionState.getAccount_incrementNonce hst'
                have hnc_caller : HasNonceOrCode state paid.message.currentTarget := by
                  left
                  rw [hself]
                  exact Nat.succ_le_succ (Nat.zero_le _)
                refine ⟨?_, hnc_caller⟩
                have hne : address ≠ evm.message.currentTarget := by
                  intro heq
                  subst heq
                  obtain ⟨hn0, hc0, -⟩ := TransactionState.accountDeployable_eq_true_iff.mp hdep
                  rcases hnc with hn | hc'
                  · exact absurd (hn0 ▸ hn) (by decide)
                  · exact hc' hc0
                have hne' : address ≠ paid.message.currentTarget := by
                  rwa [sc.message]
                have hacc_eq : state.getAccount address = evm.state.getAccount address := by
                  have ho : state.getAccountOptional address =
                      e2.state.getAccountOptional address := hother address hne'
                  exact (congrArg (Option.getD · EMPTY_ACCOUNT) ho).trans
                    (hsw_e2.getAccount hp_e2 address)
                have hst_eq : ∀ key, state.getStorage address key =
                    evm.state.getStorage address key := by
                  intro key
                  obtain ⟨acc, hf, hstate_eq⟩ :=
                    modifyState_eq_of_hasNonceOrCode hst' fun _ ha => by
                      cases ha
                      exact .inl (Nat.succ_le_succ (Nat.zero_le _))
                  have h1' : state.getStorage address key = e2.state.getStorage address key := by
                    rw [hstate_eq]
                    rfl
                  exact h1'.trans (hsw_e2.getStorage hp_e2 address key)
                rw [TransactionState.accountDeployable_congr hacc_eq hst_eq]
                exact hdep
              · obtain ⟨_, _, hr⟩ := Base.bind_ok_iff.mp hr
                cases hr
            · cases hc'
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    cases h

/-! ## Messages and creations -/

private def FrameInv (block : BlockState) (evm : Evm fork Meter) : Prop :=
  RebuildState block evm.state ∧
    (evm.code.size ≠ 0 → HasNonceOrCode evm.state evm.message.currentTarget)

/-- What a call keeps for `RebuildState`, nonces and code hashes, and its message. -/
def CallRebuild (block : BlockState) (message : Message fork) (state : TransactionState)
    (_substate : Substate) (_meter : Meter) (ended : Evm fork Meter) : Prop :=
  RebuildState block state →
    (message.code.size ≠ 0 → HasNonceOrCode state message.currentTarget) →
    (¬(message.shouldTransferValue = true ∧ message.value ≠ 0) ∨
      HasNonceOrCode state message.caller) →
    ended.message = message ∧ RebuildState block ended.state ∧ KeepsNonceOrCode state ended.state

/-- What a creation keeps for `RebuildState` and nonces and code hashes. -/
def CreateRebuild (block : BlockState) (message : Message fork) (state : TransactionState)
    (_substate : Substate) (_meter : Meter) (after : Evm fork Meter) : Prop :=
  RebuildState block state → state.accountDeployable message.currentTarget = true →
    (¬(message.shouldTransferValue = true ∧ message.value ≠ 0) ∨
      HasNonceOrCode state message.caller) →
    RebuildState block after.state ∧ KeepsNonceOrCode state after.state

private theorem rebuild_step_child {block : BlockState} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hinv : FrameInv block evm)
    (h : step fork evm = .ok result) :
    StepResult.Keeps (RebuildStep block)
      (ChildRelByKind (CallRebuild block) (CreateRebuild block)) evm result := by
  obtain ⟨hstep, hsize⟩ := rebuildStep_step (fun hs _ => hinv.2 hs) h
  cases result with
  | next after => exact hstep
  | child caller message resume =>
    obtain ⟨hcaller, hres⟩ := hstep
    have hcur : HasNonceOrCode evm.state evm.message.currentTarget :=
      hinv.2 (hsize caller message resume rfl)
    obtain ⟨vcaller, kcaller⟩ := hcaller.1 hinv.1
    have hcur_caller : HasNonceOrCode caller.state caller.message.currentTarget :=
      kcaller.2 _ (hcaller.2.1.symm ▸ hcur)
    refine ⟨hcaller, fun child after resumed hchild => hres child after resumed fun htr _ => ?_⟩
    unfold ChildRelByKind ChildRel at hchild
    rcases ht : message.target with _ | target
    · simp only [ht] at hchild
      obtain ⟨hdep, hnc_caller⟩ := accountDeployable_of_create_step hcur h ht
      exact hchild vcaller hdep (.inr hnc_caller)
    · simp only [ht] at hchild
      have hcode : message.code.size ≠ 0 → HasNonceOrCode caller.state message.currentTarget := by
        intro hne
        rcases step_eq_child_staticCode h (by simp [ht]) with heq | hstatic
        · rw [heq]
          exact kcaller.2 _ hcur
        · exact kcaller.2 _ (.inr (hstatic hne))
      have hval : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) ∨
          HasNonceOrCode caller.state message.caller := by
        by_cases hv : message.shouldTransferValue = true ∧ message.value ≠ 0
        · exact .inr (htr hv.1 ▸ hcur_caller)
        · exact .inl hv
      exact (hchild vcaller hcode hval).2

/-- Every call and creation from Spurious Dragon onward keeps `RebuildState` by gas induction. -/
theorem processMessage_rebuildState_induction [LawfulGasMeter Meter]
    (hfork : .spuriousDragon ≤ fork) {block : BlockState} (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        CallRebuild block message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CreateRebuild block message state substate meter ended.val) := by
  refine processMessage_rel_byKind (R := RebuildStep block) (Inv := FrameInv block)
    (Mcall := CallRebuild block) (Mcreate := CreateRebuild block)
    RebuildStep.refl RebuildStep.trans ?_ ?_ ?_ ?_ ?_ ?_ ?_ n
  · intro a b ⟨va, ha⟩ hab
    obtain ⟨vb, kb⟩ := hab.1 va
    exact ⟨vb, fun hs => kb.2 _ (hab.2.1.symm ▸ ha (hab.2.2 ▸ hs))⟩
  · intro evm error _
    exact rebuildStep_exceptionalHalt evm error
  · intro evm result hinv h
    exact rebuild_step_child hinv h
  · intro evm _
    exact RebuildStep.of_sameWrites ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
  · intro address evm after h _
    exact rebuildStep_runPrecompile h
  · intro message state entry substate entrySubstate meter ended hentered hrun vstate hcode hval
    obtain ⟨ventry, kentry⟩ : RebuildState block entry ∧ KeepsNonceOrCode state entry := by
      obtain ⟨vstart, kstart⟩ := vstate.startState message
      rcases hentered with ⟨_, rfl, _⟩ | ⟨ht, hmove, _⟩
      · exact ⟨vstart, kstart⟩
      · rcases hval with hno | hcaller
        · exact absurd ht hno
        · obtain ⟨ventry, kentry⟩ := vstart.moveEther (kstart.2 _ hcaller) hmove
          exact ⟨ventry, kstart.trans kentry⟩
    have hinv_start : FrameInv block (startFrame message entry entrySubstate meter) :=
      ⟨ventry, fun hs => kentry.2 _ (hcode hs)⟩
    have hstep_run := hrun hinv_start
    obtain ⟨vended, kended⟩ := hstep_run.1 ventry
    have hmsg : (rollbackOnError state ended).message = message := by
      have hm : (rollbackOnError state ended).message = ended.message := by
        unfold Evm.rollbackOnError
        split <;> rfl
      exact hm.trans hstep_run.2.1
    exact ⟨hmsg, vstate.rollbackOnError vended (kentry.trans kended)⟩
  · intro message state prepared substate meter evm after hprep hmcall hdep vstate hdeploy hval
    obtain ⟨vprep, kprep, hnonce_prep⟩ := vstate.prepareCreation hfork hdeploy hprep
    have hval_prep : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) ∨
        HasNonceOrCode prepared message.caller :=
      hval.imp id (kprep.2 _)
    obtain ⟨hmsg, vevm, kevm⟩ := hmcall vprep (fun _ => .inl hnonce_prep) hval_prep
    have hnonce_evm : 1 ≤ (evm.state.getAccount evm.message.currentTarget).nonce := by
      rw [hmsg]
      exact Nat.le_trans hnonce_prep (kevm.1 message.currentTarget)
    exact vstate.depositCode vevm (kprep.trans kevm) hnonce_evm hdep

/-- Every call from Spurious Dragon onward keeps `RebuildState`. -/
theorem processMessage_rebuildState [LawfulGasMeter Meter] (hfork : .spuriousDragon ≤ fork)
    {block : BlockState} {message : Message fork} {state : TransactionState} {substate : Substate}
    {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (valid : RebuildState block state)
    (hcode : message.code.size ≠ 0 → HasNonceOrCode state message.currentTarget)
    (hval : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) ∨
      HasNonceOrCode state message.caller)
    (h : processMessage fork message state substate meter held = .ok ended) :
    RebuildState block ended.val.state ∧ KeepsNonceOrCode state ended.val.state :=
  ((processMessage_rebuildState_induction hfork message.gas).1 message state substate meter held
    rfl ended h valid hcode hval).2

/-- Every creation from Spurious Dragon onward keeps `RebuildState`. -/
theorem processCreateMessage_rebuildState [LawfulGasMeter Meter] (hfork : .spuriousDragon ≤ fork)
    {block : BlockState} {message : Message fork} {state : TransactionState} {substate : Substate}
    {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (valid : RebuildState block state)
    (hdeploy : state.accountDeployable message.currentTarget = true)
    (hval : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) ∨
      HasNonceOrCode state message.caller)
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    RebuildState block ended.val.state ∧ KeepsNonceOrCode state ended.val.state :=
  (processMessage_rebuildState_induction hfork message.gas).2 message state substate meter held
    rfl ended h valid hdeploy hval

/-- Unwritten storage slots in `RebuildState` read the same value as in the block. -/
theorem RebuildState.getStorage_of_slot_eq_none {block : BlockState} {tx : TransactionState}
    (valid : RebuildState block tx) {address : Address} {key : Bytes32}
    (hslot : tx.storageWrites.slot address key = none) :
    tx.getStorage address key = (TransactionState.ofBlock block).getStorage address key := by
  have hof : ∀ addr k, (TransactionState.ofBlock block).getStorage addr k =
      match block.storageWrites.slot addr k with
      | some value => value
      | none =>
        if addr ∈ block.storageClears then 0 else block.preState.getStorage addr k := by
    intro addr k
    unfold TransactionState.getStorage TransactionState.ofBlock
    dsimp only
    have hempty : (∅ : State.StorageMap).slot addr k = none := rfl
    have hnot : addr ∉ (∅ : Std.ExtTreeSet Address) := Std.ExtTreeSet.not_mem_empty
    simp only [hempty, hnot, ↓reduceIte]
    rfl
  rw [hof address key]
  unfold TransactionState.getStorage
  simp only [hslot, valid.parent]
  split
  · rename_i hmem
    have h0 := valid.clears address hmem key
    rw [hof address key] at h0
    exact h0.symm
  · rfl

end EthLib.Execution.Evm

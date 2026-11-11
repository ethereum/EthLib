module

public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: transaction states that agree on accessed accounts, slots and code

Two block states agree on a set of addresses when they hold the same account at each.

They agree likewise on sets of slots and code hashes, and on every key at some addresses.

Two transaction states agree when their blocks agree and they carry the same writes and reads.

Lookups inside those sets, or at what the tracker wrote, give the same value in both.

Tracker writes, recorded reads, rollback and the end of a transaction keep that agreement.

The sets that matter are those a transaction read and wrote.

[EIP-7928, Scope and Inclusion][eip7928] asks a block access list to name them.

Agreement on whole storages and on code goes beyond that list, so it stays a hypothesis.

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base

/-! ## Agreement of two block states -/

/-- Two block states agree on four sets: of addresses, of whole storages, of slots, of code hashes.

At each address of the first set, they read the same optional account.

At each address of the second set, they read the same word at every key of storage.

At each slot of the third set, they read the same word of storage.

At each code hash of the fourth set, they fetch the same code.

A contract creation checks every storage key at a candidate address, by [EIP-7610][eip7610].

[eip7610]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7610.md#specification -/
structure BlockState.AgreesOn (account allStorage : Address → Prop)
    (slot : Address → Bytes32 → Prop) (code : Hash32 → Prop) (block other : BlockState) :
    Prop where
  /-- Each address of the first set has the same optional account in both block states. -/
  account : ∀ address, account address →
    (TransactionState.ofBlock other).getAccountOptional address =
      (TransactionState.ofBlock block).getAccountOptional address
  /-- Each address of the second set has the same word at every key in both block states. -/
  allStorage : ∀ address key, allStorage address →
    (TransactionState.ofBlock other).getStorage address key =
      (TransactionState.ofBlock block).getStorage address key
  /-- Each slot of the third set has the same storage word in both block states. -/
  slot : ∀ address key, slot address key →
    (TransactionState.ofBlock other).getStorage address key =
      (TransactionState.ofBlock block).getStorage address key
  /-- Each code hash of the fourth set fetches the same code in both block states. -/
  code : ∀ codeHash, code codeHash →
    (TransactionState.ofBlock other).getCode codeHash =
      (TransactionState.ofBlock block).getCode codeHash

namespace BlockState.AgreesOn

/-- Every block state agrees with itself on any predicates. -/
theorem refl (account allStorage : Address → Prop) (slot : Address → Bytes32 → Prop)
    (code : Hash32 → Prop) (block : BlockState) :
    AgreesOn account allStorage slot code block block :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- Agreement of block states is symmetric. -/
theorem symm {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
    {code : Hash32 → Prop} {block other : BlockState}
    (h : AgreesOn account allStorage slot code block other) :
    AgreesOn account allStorage slot code other block :=
  ⟨fun a ha => (h.account a ha).symm, fun a k he => (h.allStorage a k he).symm,
    fun a k hs => (h.slot a k hs).symm, fun c hc => (h.code c hc).symm⟩

/-- Agreement of block states is transitive. -/
theorem trans {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
    {code : Hash32 → Prop} {a b c : BlockState}
    (hab : AgreesOn account allStorage slot code a b)
    (hbc : AgreesOn account allStorage slot code b c) :
    AgreesOn account allStorage slot code a c :=
  ⟨fun x hx => (hbc.account x hx).trans (hab.account x hx),
    fun x k hx => (hbc.allStorage x k hx).trans (hab.allStorage x k hx),
    fun x k hx => (hbc.slot x k hx).trans (hab.slot x k hx),
    fun x hx => (hbc.code x hx).trans (hab.code x hx)⟩

/-- Agreement on some sets implies agreement on any of their subsets. -/
theorem mono {account account' allStorage allStorage' : Address → Prop}
    {slot slot' : Address → Bytes32 → Prop} {code code' : Hash32 → Prop}
    {block other : BlockState} (h : AgreesOn account allStorage slot code block other)
    (ha : ∀ x, account' x → account x) (he : ∀ x, allStorage' x → allStorage x)
    (hs : ∀ x k, slot' x k → slot x k) (hc : ∀ x, code' x → code x) :
    AgreesOn account' allStorage' slot' code' block other :=
  ⟨fun x hx => h.account x (ha x hx), fun x k hx => h.allStorage x k (he x hx),
    fun x k hx => h.slot x k (hs x k hx), fun x hx => h.code x (hc x hx)⟩

end BlockState.AgreesOn

namespace TransactionState

/-! ## Two states with the same tracker overlay -/

/-- Two transaction states carry the same writes, wipes, transient storage, creations and reads.

Only their parent block states may differ. -/
structure SameTracker (tx other : TransactionState) : Prop where
  /-- Both states have the same written accounts. -/
  accountWrites : other.accountWrites = tx.accountWrites
  /-- Both states have the same written storage words. -/
  storageWrites : other.storageWrites = tx.storageWrites
  /-- Both states have the same written codes. -/
  codeWrites : other.codeWrites = tx.codeWrites
  /-- Both states have the same created accounts. -/
  createdAccounts : other.createdAccounts = tx.createdAccounts
  /-- Both states have the same storage wipes. -/
  storageClears : other.storageClears = tx.storageClears
  /-- Both states have the same transient storage. -/
  transientStorage : other.transientStorage = tx.transientStorage
  /-- Both states have the same recorded account reads. -/
  accountReads : other.accountReads = tx.accountReads
  /-- Both states have the same recorded storage reads. -/
  storageReads : other.storageReads = tx.storageReads

namespace SameTracker

/-- Every transaction state has the same tracker as itself. -/
theorem refl (tx : TransactionState) : SameTracker tx tx :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Having the same tracker is symmetric. -/
theorem symm {tx other : TransactionState} (h : SameTracker tx other) : SameTracker other tx :=
  ⟨h.accountWrites.symm, h.storageWrites.symm, h.codeWrites.symm, h.createdAccounts.symm,
    h.storageClears.symm, h.transientStorage.symm, h.accountReads.symm, h.storageReads.symm⟩

/-- Having the same tracker is transitive. -/
theorem trans {a b c : TransactionState} (hab : SameTracker a b) (hbc : SameTracker b c) :
    SameTracker a c :=
  ⟨hbc.accountWrites.trans hab.accountWrites, hbc.storageWrites.trans hab.storageWrites,
    hbc.codeWrites.trans hab.codeWrites, hbc.createdAccounts.trans hab.createdAccounts,
    hbc.storageClears.trans hab.storageClears, hbc.transientStorage.trans hab.transientStorage,
    hbc.accountReads.trans hab.accountReads, hbc.storageReads.trans hab.storageReads⟩

/-- Two fresh transaction states have the same tracker. -/
theorem ofBlock (block other : BlockState) : SameTracker (.ofBlock block) (.ofBlock other) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SameTracker

/-! ## Agreement of two transaction states -/

/-- Two transaction states agree on four sets of addresses, slots and code hashes.

Their parent block states agree there, and both states carry the same tracker. -/
structure AgreesOn (account allStorage : Address → Prop) (slot : Address → Bytes32 → Prop)
    (code : Hash32 → Prop) (tx other : TransactionState) : Prop where
  /-- Their parent block states agree on the four sets. -/
  parent : BlockState.AgreesOn account allStorage slot code tx.parent other.parent
  /-- Both transaction states carry the same tracker. -/
  tracker : SameTracker tx other

/-- Two results agree when both fail with the same error or both succeed with agreeing states. -/
def AgreesOnExcept {ε : Type} (account allStorage : Address → Prop)
    (slot : Address → Bytes32 → Prop) (code : Hash32 → Prop)
    (res res' : Except ε TransactionState) : Prop :=
  match res, res' with
  | .error e, .error e' => e = e'
  | .ok tx, .ok other => AgreesOn account allStorage slot code tx other
  | _, _ => False

namespace AgreesOnExcept

variable {ε δ : Type} {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
  {code : Hash32 → Prop} {res res' : Except ε TransactionState}

/-- Mapping an error function across agreeing results preserves agreement. -/
theorem mapError (f : ε → δ) (h : AgreesOnExcept account allStorage slot code res res') :
    AgreesOnExcept account allStorage slot code (res.mapError f) (res'.mapError f) := by
  cases res <;> cases res' <;> simp_all [AgreesOnExcept, Except.mapError]

/-- Chaining two steps that keep agreement keeps agreement of the results. -/
theorem bind {k k' : TransactionState → Except ε TransactionState}
    (h : AgreesOnExcept account allStorage slot code res res')
    (hk : ∀ {tx other}, AgreesOn account allStorage slot code tx other →
      res = .ok tx → res' = .ok other →
      AgreesOnExcept account allStorage slot code (k tx) (k' other)) :
    AgreesOnExcept account allStorage slot code (res >>= k) (res' >>= k') := by
  cases res with
  | error _ =>
    cases res' with
    | error _ => simpa [AgreesOnExcept, Bind.bind, Except.bind] using h
    | ok _ => simp [AgreesOnExcept] at h
  | ok tx =>
    cases res' with
    | error _ => simp [AgreesOnExcept] at h
    | ok other => exact hk h rfl rfl

end AgreesOnExcept

namespace AgreesOn

variable {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
  {code : Hash32 → Prop} {tx other : TransactionState}

/-- Every transaction state agrees with itself on any predicates. -/
theorem refl (account allStorage : Address → Prop) (slot : Address → Bytes32 → Prop)
    (code : Hash32 → Prop) (tx : TransactionState) :
    AgreesOn account allStorage slot code tx tx :=
  ⟨.refl account allStorage slot code tx.parent, .refl tx⟩

/-- Agreement of transaction states is symmetric. -/
theorem symm (h : AgreesOn account allStorage slot code tx other) :
    AgreesOn account allStorage slot code other tx :=
  ⟨h.parent.symm, h.tracker.symm⟩

/-- Agreement of transaction states is transitive. -/
theorem trans {a b c : TransactionState}
    (hab : AgreesOn account allStorage slot code a b)
    (hbc : AgreesOn account allStorage slot code b c) :
    AgreesOn account allStorage slot code a c :=
  ⟨hab.parent.trans hbc.parent, hab.tracker.trans hbc.tracker⟩

/-- Agreement on some sets implies agreement on any of their subsets. -/
theorem mono {account' allStorage' : Address → Prop} {slot' : Address → Bytes32 → Prop}
    {code' : Hash32 → Prop} (h : AgreesOn account allStorage slot code tx other)
    (ha : ∀ x, account' x → account x) (he : ∀ x, allStorage' x → allStorage x)
    (hs : ∀ x k, slot' x k → slot x k) (hc : ∀ x, code' x → code x) :
    AgreesOn account' allStorage' slot' code' tx other :=
  ⟨h.parent.mono ha he hs hc, h.tracker⟩

/-- Two fresh transaction states agree when their block states do. -/
theorem ofBlock {block block' : BlockState}
    (h : BlockState.AgreesOn account allStorage slot code block block') :
    AgreesOn account allStorage slot code (.ofBlock block) (.ofBlock block') :=
  ⟨h, .ofBlock block block'⟩

/-! ## Lookups on agreeing states -/

/-- At an agreed address, both states read the same optional account before the transaction. -/
theorem getPreStateAccountOptional_eq (h : AgreesOn account allStorage slot code tx other)
    {address : Address} (ha : account address) :
    other.getPreStateAccountOptional address = tx.getPreStateAccountOptional address := by
  have hparent := h.parent.account address ha
  simpa [getAccountOptional, TransactionState.ofBlock, getPreStateAccountOptional] using hparent

/-- At an agreed address, both states read the same account before the transaction. -/
theorem getPreStateAccount_eq (h : AgreesOn account allStorage slot code tx other)
    {address : Address} (ha : account address) :
    other.getPreStateAccount address = tx.getPreStateAccount address := by
  simp [getPreStateAccount, h.getPreStateAccountOptional_eq ha]

/-- At a written or agreed address, both states read the same optional account. -/
theorem getAccountOptional_eq (h : AgreesOn account allStorage slot code tx other)
    {address : Address} (ha : address ∈ tx.accountWrites ∨ account address) :
    other.getAccountOptional address = tx.getAccountOptional address := by
  unfold getAccountOptional
  rw [h.tracker.accountWrites]
  cases hw : tx.accountWrites[address]? with
  | some _ => rfl
  | none =>
    rcases ha with hmem | ha
    · rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hw] at hmem
      cases hmem
    · exact h.getPreStateAccountOptional_eq ha

/-- At a written or agreed address, both states read the same account. -/
theorem getAccount_eq (h : AgreesOn account allStorage slot code tx other)
    {address : Address} (ha : address ∈ tx.accountWrites ∨ account address) :
    other.getAccount address = tx.getAccount address := by
  simp [getAccount, h.getAccountOptional_eq ha]

/-- At a written or agreed address, both states agree on whether the address has an account. -/
theorem accountExists_eq (h : AgreesOn account allStorage slot code tx other)
    {address : Address} (ha : address ∈ tx.accountWrites ∨ account address) :
    other.accountExists address = tx.accountExists address := by
  simp [accountExists, h.getAccountOptional_eq ha]

/-- At a written or agreed address, both states agree on whether the account is empty. -/
theorem accountExistsAndIsEmpty_eq (h : AgreesOn account allStorage slot code tx other)
    {address : Address} (ha : address ∈ tx.accountWrites ∨ account address) :
    other.accountExistsAndIsEmpty address = tx.accountExistsAndIsEmpty address := by
  simp [accountExistsAndIsEmpty, h.getAccountOptional_eq ha]

/-- At a written or agreed address, both states agree on whether the account is alive. -/
theorem isAccountAlive_eq (h : AgreesOn account allStorage slot code tx other)
    {address : Address} (ha : address ∈ tx.accountWrites ∨ account address) :
    other.isAccountAlive address = tx.isAccountAlive address := by
  simp [isAccountAlive, h.getAccountOptional_eq ha]

/-- At a written, wiped or agreed slot, both states read the same storage word. -/
theorem getStorage_eq (h : AgreesOn account allStorage slot code tx other)
    {address : Address} {key : Bytes32}
    (hs : (tx.storageWrites.slot address key).isSome ∨ address ∈ tx.storageClears ∨
      allStorage address ∨ slot address key) :
    other.getStorage address key = tx.getStorage address key := by
  unfold getStorage
  rw [h.tracker.storageWrites, h.tracker.storageClears]
  cases hw : tx.storageWrites.slot address key with
  | some _ => rfl
  | none =>
    by_cases hc : address ∈ tx.storageClears
    · simp [hc]
    · simp only [hc, ↓reduceIte]
      change (TransactionState.ofBlock other.parent).getStorage address key =
        (TransactionState.ofBlock tx.parent).getStorage address key
      rcases hs with hmem | hmem | he | hs
      · rw [hw] at hmem
        cases hmem
      · exact absurd hmem hc
      · exact h.parent.allStorage address key he
      · exact h.parent.slot address key hs

/-- At an agreed slot or a created account, both read the same word from before the transaction. -/
theorem getStorageOriginal_eq (h : AgreesOn account allStorage slot code tx other)
    {address : Address} {key : Bytes32}
    (hs : address ∈ tx.createdAccounts ∨ allStorage address ∨ slot address key) :
    other.getStorageOriginal address key = tx.getStorageOriginal address key := by
  unfold getStorageOriginal
  rw [h.tracker.createdAccounts]
  by_cases hc : address ∈ tx.createdAccounts
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    change (TransactionState.ofBlock other.parent).getStorage address key =
      (TransactionState.ofBlock tx.parent).getStorage address key
    rcases hs with hmem | he | hs
    · exact absurd hmem hc
    · exact h.parent.allStorage address key he
    · exact h.parent.slot address key hs

/-- Both states read the same transient storage word at every address and key. -/
theorem getTransientStorage_eq (h : AgreesOn account allStorage slot code tx other)
    (address : Address) (key : Bytes32) :
    other.getTransientStorage address key = tx.getTransientStorage address key := by
  simp [getTransientStorage, h.tracker.transientStorage]

/-- At a written or agreed hash, or the empty-code hash, both states fetch the same code. -/
theorem getCode_eq (h : AgreesOn account allStorage slot code tx other) {codeHash : Hash32}
    (hc : codeHash = EMPTY_CODE_HASH ∨ codeHash ∈ tx.codeWrites ∨ code codeHash) :
    other.getCode codeHash = tx.getCode codeHash := by
  unfold getCode
  by_cases hempty : codeHash = EMPTY_CODE_HASH
  · simp [hempty]
  · simp only [hempty, ↓reduceIte, h.tracker.codeWrites]
    cases hw : tx.codeWrites[codeHash]? with
    | some _ => rfl
    | none =>
      rcases hc with he | hmem | hc
      · exact absurd he hempty
      · rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hw] at hmem
        cases hmem
      · simpa [getCode, TransactionState.ofBlock, hempty] using h.parent.code codeHash hc

/-- At an address whose whole storage agrees, or that was wiped, storage emptiness agrees. -/
theorem accountHasStorage_eq (h : AgreesOn account allStorage slot code tx other)
    {address : Address} (he : address ∈ tx.storageClears ∨ allStorage address) :
    other.accountHasStorage address = tx.accountHasStorage address := by
  have hkey : ∀ key, other.getStorage address key = tx.getStorage address key := by
    intro key
    rcases he with hc | he
    · exact h.getStorage_eq (.inr (.inl hc))
    · exact h.getStorage_eq (.inr (.inr (.inl he)))
  rw [Bool.eq_iff_iff, accountHasStorage_eq_true_iff, accountHasStorage_eq_true_iff]
  simp only [hkey]

/--
At a written or agreed address, deployability agrees when a candidate's storage agrees.

When the nonce is nonzero or the code is nonempty, [EIP-684][eip684] refuses before reading storage.

[eip684]: https://eips.ethereum.org/EIPS/eip-684#specification
-/
theorem accountDeployable_eq (h : AgreesOn account allStorage slot code tx other)
    {address : Address} (ha : address ∈ tx.accountWrites ∨ account address)
    (he : (tx.getAccount address).nonce = 0 →
      (tx.getAccount address).codeHash = EMPTY_CODE_HASH →
      address ∈ tx.storageClears ∨ allStorage address) :
    other.accountDeployable address = tx.accountDeployable address := by
  unfold accountDeployable
  rw [h.getAccount_eq ha]
  by_cases hnonce : (tx.getAccount address).nonce = 0
  · by_cases hcode : (tx.getAccount address).codeHash = EMPTY_CODE_HASH
    · simp [hnonce, hcode, h.accountHasStorage_eq (he hnonce hcode)]
    · simp [hnonce, hcode]
  · simp [hnonce]

/-! ## Preservation under tracker updates -/

/-- Recording an account read preserves agreement. -/
theorem recordAccountRead (h : AgreesOn account allStorage slot code tx other)
    (address : Address) :
    AgreesOn account allStorage slot code (tx.recordAccountRead address)
      (other.recordAccountRead address) := by
  refine ⟨h.parent, ?_⟩
  obtain ⟨aw, sw, cw, ca, sc, ts, ar, sr⟩ := h.tracker
  exact ⟨aw, sw, cw, ca, sc, ts, by simp [TransactionState.recordAccountRead, ar], sr⟩

/-- Recording a storage read preserves agreement. -/
theorem recordStorageRead (h : AgreesOn account allStorage slot code tx other)
    (address : Address) (key : Bytes32) :
    AgreesOn account allStorage slot code (tx.recordStorageRead address key)
      (other.recordStorageRead address key) := by
  refine ⟨h.parent, ?_⟩
  obtain ⟨aw, sw, cw, ca, sc, ts, ar, sr⟩ := h.tracker
  exact ⟨aw, sw, cw, ca, sc, ts, ar, by simp [TransactionState.recordStorageRead, sr]⟩

/-- Taking the reads of two states with the same tracker preserves agreement. -/
theorem withReadsOf {reads reads' : TransactionState}
    (h : AgreesOn account allStorage slot code tx other) (hr : SameTracker reads reads') :
    AgreesOn account allStorage slot code (tx.withReadsOf reads) (other.withReadsOf reads') := by
  refine ⟨h.parent, ?_⟩
  obtain ⟨aw, sw, cw, ca, sc, ts, _, _⟩ := h.tracker
  exact ⟨aw, sw, cw, ca, sc, ts, hr.accountReads, hr.storageReads⟩

/-- Setting an account to the same value in both states preserves agreement. -/
theorem setAccount (h : AgreesOn account allStorage slot code tx other) (address : Address)
    (value : Option Account) :
    AgreesOn account allStorage slot code (tx.setAccount address value)
      (other.setAccount address value) := by
  refine ⟨h.parent, ?_⟩
  obtain ⟨aw, sw, cw, ca, sc, ts, ar, sr⟩ := h.tracker
  exact ⟨by simp [TransactionState.setAccount, aw], sw, cw, ca, sc, ts, ar, sr⟩

/-- Marking an account as created in both states preserves agreement. -/
theorem markAccountCreated (h : AgreesOn account allStorage slot code tx other)
    (address : Address) :
    AgreesOn account allStorage slot code (tx.markAccountCreated address)
      (other.markAccountCreated address) := by
  refine ⟨h.parent, ?_⟩
  obtain ⟨aw, sw, cw, ca, sc, ts, ar, sr⟩ := h.tracker
  exact ⟨aw, sw, cw, by simp [TransactionState.markAccountCreated, ca], sc, ts, ar, sr⟩

/-- Setting a transient storage word in both states preserves agreement. -/
theorem setTransientStorage (h : AgreesOn account allStorage slot code tx other)
    (address : Address) (key : Bytes32) (value : U256) :
    AgreesOn account allStorage slot code (tx.setTransientStorage address key value)
      (other.setTransientStorage address key value) := by
  refine ⟨h.parent, ?_⟩
  obtain ⟨aw, sw, cw, ca, sc, ts, ar, sr⟩ := h.tracker
  exact ⟨aw, sw, cw, ca, sc, by simp [TransactionState.setTransientStorage, ts], ar, sr⟩

/-- Wiping the storage of an address in both states preserves agreement. -/
theorem destroyStorage (h : AgreesOn account allStorage slot code tx other)
    (address : Address) :
    AgreesOn account allStorage slot code (tx.destroyStorage address)
      (other.destroyStorage address) := by
  refine ⟨h.parent, ?_⟩
  obtain ⟨aw, sw, cw, ca, sc, ts, ar, sr⟩ := h.tracker
  exact ⟨aw, by simp [TransactionState.destroyStorage, sw], cw, ca,
    by simp [TransactionState.destroyStorage, sc], ts, ar,
    by simp [TransactionState.destroyStorage, sw, sr]⟩

/-- Deleting an account in both states preserves agreement. -/
theorem destroyAccount (h : AgreesOn account allStorage slot code tx other)
    (address : Address) :
    AgreesOn account allStorage slot code (tx.destroyAccount address)
      (other.destroyAccount address) :=
  (h.destroyStorage address).setAccount address none

/-- Touching an agreed or written address in both states preserves agreement. -/
theorem touchAccount (h : AgreesOn account allStorage slot code tx other) {address : Address}
    (ha : address ∈ tx.accountWrites ∨ account address) :
    AgreesOn account allStorage slot code (tx.touchAccount address)
      (other.touchAccount address) := by
  unfold TransactionState.touchAccount
  rw [h.accountExists_eq ha]
  split
  · exact h
  · exact h.setAccount address (some EMPTY_ACCOUNT)

/-- Deleting touched empty accounts at written or agreed addresses preserves agreement. -/
theorem destroyTouchedEmptyAccounts (h : AgreesOn account allStorage slot code tx other)
    (fork : Fork) {touched : List Address}
    (ha : ∀ address ∈ touched, address ∈ tx.accountWrites ∨ account address) :
    AgreesOn account allStorage slot code (tx.destroyTouchedEmptyAccounts fork touched)
      (other.destroyTouchedEmptyAccounts fork touched) := by
  unfold TransactionState.destroyTouchedEmptyAccounts
  split
  · exact h
  · induction touched generalizing tx other with
    | nil => exact h
    | cons address rest ih =>
      have hhead : address ∈ tx.accountWrites ∨ account address := ha address List.mem_cons_self
      simp only [List.foldl_cons, h.accountExistsAndIsEmpty_eq hhead]
      split
      · refine ih (h.destroyAccount address) fun x hx => ?_
        rcases ha x (List.mem_cons_of_mem _ hx) with hw | hacc
        · by_cases heq : x = address
          · subst heq
            exact .inl (by simp [TransactionState.destroyAccount, TransactionState.setAccount,
              TransactionState.destroyStorage])
          · exact .inl (by simpa [TransactionState.destroyAccount, TransactionState.setAccount,
              TransactionState.destroyStorage, Std.ExtTreeMap.mem_insert, Ne.symm heq] using hw)
        · exact .inr hacc
      · exact ih h fun x hx => ha x (List.mem_cons_of_mem _ hx)

/-- Writing a storage word at a written or agreed address gives the same outcome and agrees. -/
theorem setStorage (h : AgreesOn account allStorage slot code tx other) {address : Address}
    (ha : address ∈ tx.accountWrites ∨ account address) (key : Bytes32) (value : U256) :
    AgreesOnExcept account allStorage slot code (tx.setStorage address key value)
      (other.setStorage address key value) := by
  unfold AgreesOnExcept TransactionState.setStorage
  rw [h.getAccountOptional_eq ha]
  by_cases hnone : (tx.getAccountOptional address).isNone = true
  · simp [hnone]
  · simp only [hnone]
    obtain ⟨aw, sw, cw, ca, sc, ts, ar, sr⟩ := (h.recordAccountRead address).tracker
    exact ⟨h.parent, aw, by simp [sw], cw, ca, sc, ts, ar, sr⟩

/-- Changing an account at a written or agreed address gives the same outcome and agrees. -/
theorem modifyState (h : AgreesOn account allStorage slot code tx other) (fork : Fork)
    {address : Address} (ha : address ∈ tx.accountWrites ∨ account address)
    (f : Account → Except StateError Account) :
    AgreesOnExcept account allStorage slot code (tx.modifyState fork address f)
      (other.modifyState fork address f) := by
  unfold AgreesOnExcept TransactionState.modifyState
  simp only [getAccount_recordAccountRead, h.getAccount_eq ha]
  cases f (tx.getAccount address) with
  | error _ => rfl
  | ok updated =>
    dsimp only [bind, Except.bind, pure, Except.pure]
    have hset := (h.recordAccountRead address).setAccount address (some updated)
    have hwritten : address ∈ ((tx.recordAccountRead address).setAccount address
        (some updated)).accountWrites := by
      simp [TransactionState.setAccount]
    rw [hset.accountExistsAndIsEmpty_eq (.inl hwritten)]
    by_cases hempty :
        (decide (fork ≥ Fork.paris) &&
          ((tx.recordAccountRead address).setAccount address
            (some updated)).accountExistsAndIsEmpty address) = true
    · simp only [hempty, ↓reduceIte]
      exact hset.destroyAccount address
    · simp only [hempty]
      exact hset

/-- Moving ether between written or agreed addresses gives the same outcome and agrees. -/
theorem moveEther (h : AgreesOn account allStorage slot code tx other) (fork : Fork)
    {sender recipient : Address} (hs : sender ∈ tx.accountWrites ∨ account sender)
    (hr : recipient ∈ tx.accountWrites ∨ account recipient) (amount : U256) :
    AgreesOnExcept account allStorage slot code (tx.moveEther fork sender recipient amount)
      (other.moveEther fork sender recipient amount) := by
  unfold TransactionState.moveEther
  refine (h.modifyState fork hs (Account.debit sender amount)).bind fun hmid hm1 _ => ?_
  refine hmid.modifyState fork ?_ (Account.credit recipient amount)
  rcases hr with hw | hacc
  · refine .inl ?_
    by_cases heq : recipient = sender
    · subst heq
      obtain ⟨_, -, rfl⟩ := modifyState_eq_ok_iff.mp hm1
      split <;> simp [TransactionState.destroyAccount, TransactionState.setAccount,
        TransactionState.destroyStorage]
    · obtain ⟨_, -, rfl⟩ := modifyState_eq_ok_iff.mp hm1
      split <;> simpa [TransactionState.destroyAccount, TransactionState.setAccount,
        TransactionState.destroyStorage, TransactionState.recordAccountRead,
        Std.ExtTreeMap.mem_insert, Ne.symm heq] using hw
  · exact .inr hacc

/-- Adding newly created ether at a written or agreed address gives the same outcome and agrees. -/
theorem createEther (h : AgreesOn account allStorage slot code tx other) (fork : Fork)
    {address : Address} (ha : address ∈ tx.accountWrites ∨ account address) (amount : U256) :
    AgreesOnExcept account allStorage slot code (tx.createEther fork address amount)
      (other.createEther fork address amount) :=
  h.modifyState fork ha (Account.credit address amount)

/-- Setting the balance at a written or agreed address gives the same outcome and agrees. -/
theorem setAccountBalance (h : AgreesOn account allStorage slot code tx other) (fork : Fork)
    {address : Address} (ha : address ∈ tx.accountWrites ∨ account address) (amount : U256) :
    AgreesOnExcept account allStorage slot code (tx.setAccountBalance fork address amount)
      (other.setAccountBalance fork address amount) :=
  h.modifyState fork ha _

/-- Adding one to the nonce at a written or agreed address gives the same outcome and agrees. -/
theorem incrementNonce (h : AgreesOn account allStorage slot code tx other) (fork : Fork)
    {address : Address} (ha : address ∈ tx.accountWrites ∨ account address) :
    AgreesOnExcept account allStorage slot code (tx.incrementNonce fork address)
      (other.incrementNonce fork address) :=
  h.modifyState fork ha _

/-- Setting code at a written or agreed address gives the same outcome and agrees. -/
theorem setCode (h : AgreesOn account allStorage slot code tx other) (fork : Fork)
    {address : Address} (ha : address ∈ tx.accountWrites ∨ account address) (bytes : ByteArray) :
    AgreesOnExcept account allStorage slot code (tx.setCode fork address bytes)
      (other.setCode fork address bytes) := by
  unfold TransactionState.setCode
  refine AgreesOn.modifyState ?_ fork ?_ _
  · split
    · exact h
    · obtain ⟨aw, sw, cw, ca, sc, ts, ar, sr⟩ := h.tracker
      exact ⟨h.parent, aw, sw, by simp [cw], ca, sc, ts, ar, sr⟩
  · split <;> exact ha

/-- Clearing an account at a written or agreed address keeps its balance, outcome and agreement. -/
theorem clearAccountPreservingBalance (h : AgreesOn account allStorage slot code tx other)
    (fork : Fork) {address : Address} (ha : address ∈ tx.accountWrites ∨ account address) :
    AgreesOnExcept account allStorage slot code (tx.clearAccountPreservingBalance fork address)
      (other.clearAccountPreservingBalance fork address) := by
  unfold TransactionState.clearAccountPreservingBalance
  exact (h.destroyStorage address).modifyState fork ha _

/-- Rolling back two agreeing states to snapshots with the same tracker preserves agreement. -/
theorem restoreTxState {snapshot snapshot' : TransactionState}
    (h : AgreesOn account allStorage slot code tx other) (hs : SameTracker snapshot snapshot') :
    AgreesOn account allStorage slot code (tx.restoreTxState snapshot)
      (other.restoreTxState snapshot') := by
  refine ⟨h.parent, ?_⟩
  obtain ⟨_, _, _, ca, _, _, ar, sr⟩ := h.tracker
  exact ⟨hs.accountWrites, hs.storageWrites, hs.codeWrites, ca, hs.storageClears,
    hs.transientStorage, ar, sr⟩

/-- Moving two agreeing transactions into their blocks gives agreeing states for the next one.

The new blocks also agree on everything the transaction wrote or wiped. -/
theorem incorporateTxIntoBlock (h : AgreesOn account allStorage slot code tx other) :
    AgreesOn (fun a => a ∈ tx.accountWrites ∨ account a)
      (fun a => a ∈ tx.storageClears ∨ allStorage a)
      (fun a k => (tx.storageWrites.slot a k).isSome ∨ a ∈ tx.storageClears ∨
        allStorage a ∨ slot a k)
      (fun c => c = EMPTY_CODE_HASH ∨ c ∈ tx.codeWrites ∨ code c)
      tx.incorporateTxIntoBlock other.incorporateTxIntoBlock := by
  refine ⟨⟨fun a ha => ?_, fun a k he => ?_, fun a k hs => ?_, fun c hc => ?_⟩, .ofBlock _ _⟩
  · change other.incorporateTxIntoBlock.getAccountOptional a =
      tx.incorporateTxIntoBlock.getAccountOptional a
    rw [getAccountOptional_incorporateTxIntoBlock, getAccountOptional_incorporateTxIntoBlock]
    exact h.getAccountOptional_eq ha
  · change other.incorporateTxIntoBlock.getStorage a k =
      tx.incorporateTxIntoBlock.getStorage a k
    rw [getStorage_incorporateTxIntoBlock, getStorage_incorporateTxIntoBlock]
    rcases he with hc | he
    · exact h.getStorage_eq (.inr (.inl hc))
    · exact h.getStorage_eq (.inr (.inr (.inl he)))
  · change other.incorporateTxIntoBlock.getStorage a k =
      tx.incorporateTxIntoBlock.getStorage a k
    rw [getStorage_incorporateTxIntoBlock, getStorage_incorporateTxIntoBlock]
    exact h.getStorage_eq hs
  · change other.incorporateTxIntoBlock.getCode c = tx.incorporateTxIntoBlock.getCode c
    rw [getCode_incorporateTxIntoBlock, getCode_incorporateTxIntoBlock]
    exact h.getCode_eq hc

end AgreesOn

/-! ## Agreement on the reads and writes of a tracker -/

/-- The addresses that a transaction state read or wrote. -/
def accessedAccount (endState : TransactionState) (address : Address) : Prop :=
  address ∈ endState.accountReads ∨ address ∈ endState.accountWrites

/-- The accessed addresses with nonce 0 and no code in the block, so deployment candidates. -/
def candidateStorage (block : BlockState) (endState : TransactionState)
    (address : Address) : Prop :=
  accessedAccount endState address ∧
    ((TransactionState.ofBlock block).getAccount address).nonce = 0 ∧
    ((TransactionState.ofBlock block).getAccount address).codeHash = EMPTY_CODE_HASH

/-- The storage slots that a transaction state read or wrote. -/
def accessedSlot (endState : TransactionState) (address : Address) (key : Bytes32) : Prop :=
  key ∈ endState.storageReads.getD address ∅ ∨
    (endState.storageWrites.slot address key).isSome

/-- The code hashes, before the transaction, of the addresses that a transaction read or wrote. -/
def accessedCode (block : BlockState) (endState : TransactionState) (codeHash : Hash32) : Prop :=
  ∃ address, accessedAccount endState address ∧
    ((TransactionState.ofBlock block).getAccount address).codeHash = codeHash

/-- Two block states agree on the accounts and slots that a transaction read or wrote.

They also agree on the whole storage of each accessed deployment candidate.

[EIP-7610][eip7610] reads that storage, and the tracker does not record it.

They also agree on the code under the code hash of each accessed address.

A block access list names neither, so they are assumptions beyond it.

[eip7610]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7610.md#specification -/
abbrev _root_.EthLib.Execution.State.BlockState.AgreesOnTracker (endState : TransactionState)
    (block other : BlockState) : Prop :=
  BlockState.AgreesOn
    (TransactionState.accessedAccount endState)
    (TransactionState.candidateStorage block endState)
    (TransactionState.accessedSlot endState)
    (TransactionState.accessedCode block endState)
    block other

/-- Two block states that agree on a transaction's accesses give agreeing fresh states. -/
theorem AgreesOn.ofTracker {block other : BlockState} {endState : TransactionState}
    (h : BlockState.AgreesOnTracker endState block other) :
    AgreesOn
      (accessedAccount endState)
      (candidateStorage block endState)
      (accessedSlot endState)
      (accessedCode block endState)
      (.ofBlock block) (.ofBlock other) :=
  .ofBlock h

/-! ## Satisfiability witness -/

/-- Two distinct block states can agree on every tracker predicate while differing outside them. -/
theorem exists_agreesOnTracker_ne :
    ∃ (address candidate unread : Address) (key unreadKey : Bytes32) (codeHash : Hash32)
      (endState : TransactionState) (block other : BlockState),
      block ≠ other ∧
      accessedAccount endState address ∧
      candidateStorage block endState candidate ∧
      accessedSlot endState address key ∧
      accessedCode block endState codeHash ∧
      BlockState.AgreesOnTracker endState block other ∧
      (TransactionState.ofBlock block).getAccount unread ≠
        (TransactionState.ofBlock other).getAccount unread ∧
      (TransactionState.ofBlock block).getStorage address unreadKey ≠
        (TransactionState.ofBlock other).getStorage address unreadKey := by
  let address : Address := toAddressMasked 0
  let candidate : Address := toAddressMasked 2
  let unread : Address := toAddressMasked 1
  let key : Bytes32 := Vector.replicate 32 0
  let unreadKey : Bytes32 := Vector.replicate 32 1
  let bytes : ByteArray := ⟨#[0x00]⟩
  let codeHash : Hash32 := Cryptography.Hash.Keccak.keccak256 bytes
  let contract : Account := { nonce := 1, balance := 0, codeHash }
  let rich : Account := { EMPTY_ACCOUNT with balance := 1 }
  let baseAccounts : Std.ExtTreeMap Address Account :=
    (∅ : Std.ExtTreeMap Address Account).insert address contract
  let baseCode : Std.ExtTreeMap Hash32 ByteArray :=
    (∅ : Std.ExtTreeMap Hash32 ByteArray).insert codeHash bytes
  let otherSlots : Std.ExtTreeMap Bytes32 U256 :=
    (∅ : Std.ExtTreeMap Bytes32 U256).insert unreadKey 1
  let block : BlockState := ⟨⟨baseAccounts, ∅, baseCode⟩, ∅, ∅, ∅, ∅⟩
  let other : BlockState :=
    ⟨⟨baseAccounts.insert unread rich,
      (∅ : StorageMap).insert address otherSlots, baseCode⟩, ∅, ∅, ∅, ∅⟩
  let endState : TransactionState :=
    (((TransactionState.ofBlock block).recordAccountRead address).recordAccountRead
      candidate).recordStorageRead address key
  have hne_unread_addr : unread ≠ address := by decide
  have hne_unread_cand : unread ≠ candidate := by decide
  have hne_cand_addr : candidate ≠ address := by decide
  have hne_key : unreadKey ≠ key := by decide
  have hacc_eq : ∀ a, accessedAccount endState a ↔ a = address ∨ a = candidate := by
    intro a
    simp only [accessedAccount, endState, TransactionState.ofBlock, recordAccountRead,
      recordStorageRead, Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.not_mem_empty,
      Std.ExtTreeMap.not_mem_empty, Std.compare_eq_iff_eq, or_false]
    exact ⟨fun h => h.elim (fun h1 => .inr h1.symm) (fun h2 => .inl h2.symm),
      fun h => h.elim (fun h1 => .inr h1.symm) (fun h2 => .inl h2.symm)⟩
  have hget_addr_block : (TransactionState.ofBlock block).getAccount address = contract := by
    simp [block, baseAccounts, TransactionState.ofBlock, getAccount, getAccountOptional,
      State.getAccountOptional]
  have hget_cand_block : (TransactionState.ofBlock block).getAccount candidate = EMPTY_ACCOUNT := by
    simp [block, baseAccounts, TransactionState.ofBlock, getAccount, getAccountOptional,
      State.getAccountOptional, Ne.symm hne_cand_addr]
  have hcand_iff : ∀ a, candidateStorage block endState a ↔ a = candidate := by
    intro a
    constructor
    · rintro ⟨ha, hnonce, _⟩
      rcases (hacc_eq a).mp ha with rfl | rfl
      · rw [hget_addr_block] at hnonce
        simp [contract] at hnonce
      · rfl
    · rintro rfl
      exact ⟨(hacc_eq candidate).mpr (.inr rfl), by simp [hget_cand_block, EMPTY_ACCOUNT],
        by simp [hget_cand_block, EMPTY_ACCOUNT]⟩
  have hslot_eq : ∀ a k, accessedSlot endState a k ↔ a = address ∧ k = key := by
    intro a k
    simp only [accessedSlot, endState, TransactionState.ofBlock, recordAccountRead,
      recordStorageRead, StorageMap.slot, Std.ExtTreeMap.getElem?_empty, Option.bind_none,
      Option.isSome_none, Bool.false_eq_true, or_false]
    by_cases ha : a = address
    · subst ha
      simp only [Std.ExtTreeMap.getD_eq_getD_getElem?, Std.ExtTreeMap.getElem?_insert_self,
        Std.ExtTreeMap.getElem?_empty, Option.getD_some, Option.getD_none,
        Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.not_mem_empty, Std.compare_eq_iff_eq,
        or_false, true_and]
      exact ⟨Eq.symm, Eq.symm⟩
    · simp [Std.ExtTreeMap.getD_eq_getD_getElem?, Ne.symm ha, ha]
  have hagree : BlockState.AgreesOnTracker endState block other := by
    refine ⟨fun a ha => ?_, fun a k he => ?_, fun a k hs => ?_, fun h hc => ?_⟩
    · rcases (hacc_eq a).mp ha with rfl | rfl
      · simp only [block, other, baseAccounts, TransactionState.ofBlock, getAccountOptional,
          State.getAccountOptional, Std.ExtTreeMap.getElem?_empty,
          Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq]
        simp [hne_unread_addr]
      · simp only [block, other, baseAccounts, TransactionState.ofBlock, getAccountOptional,
          State.getAccountOptional, Std.ExtTreeMap.getElem?_empty,
          Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq]
        simp [hne_unread_cand, Ne.symm hne_cand_addr]
    · rw [(hcand_iff a).mp he]
      simp [block, other, TransactionState.ofBlock, getStorage, State.getStorage, StorageMap.slot,
        Option.bind_none, Std.ExtTreeSet.not_mem_empty, Ne.symm hne_cand_addr]
    · obtain ⟨rfl, rfl⟩ := (hslot_eq a k).mp hs
      simp [block, other, otherSlots, TransactionState.ofBlock, getStorage, State.getStorage,
        StorageMap.slot, Option.bind_none, Std.ExtTreeSet.not_mem_empty, hne_key]
    · obtain ⟨a, ha, rfl⟩ := hc
      rcases (hacc_eq a).mp ha with rfl | rfl
      · rw [hget_addr_block]
        by_cases hempty : contract.codeHash = EMPTY_CODE_HASH
        · simp [getCode, hempty]
        · simp [block, other, baseCode, contract, TransactionState.ofBlock, getCode, State.getCode,
            hempty]
      · rw [hget_cand_block]
        simp [getCode, EMPTY_ACCOUNT]
  have hdiff_acc : (TransactionState.ofBlock block).getAccount unread ≠
      (TransactionState.ofBlock other).getAccount unread := by
    intro heq
    have hbal := congrArg Account.balance heq
    simp [block, other, baseAccounts, rich, TransactionState.ofBlock, getAccount,
      getAccountOptional, State.getAccountOptional, EMPTY_ACCOUNT, Ne.symm hne_unread_addr] at hbal
  have hdiff_slot : (TransactionState.ofBlock block).getStorage address unreadKey ≠
      (TransactionState.ofBlock other).getStorage address unreadKey := by
    intro heq
    simp [block, other, otherSlots, TransactionState.ofBlock, getStorage, State.getStorage,
      StorageMap.slot, Option.bind_none, Std.ExtTreeSet.not_mem_empty] at heq
  refine ⟨address, candidate, unread, key, unreadKey, codeHash, endState, block, other,
    fun hblk => hdiff_acc (by rw [hblk]),
    (hacc_eq address).mpr (.inl rfl),
    (hcand_iff candidate).mpr rfl,
    (hslot_eq address key).mpr ⟨rfl, rfl⟩,
    ⟨address, (hacc_eq address).mpr (.inl rfl), hget_addr_block ▸ rfl⟩,
    hagree, hdiff_acc, hdiff_slot⟩

end TransactionState

end EthLib.Execution.State

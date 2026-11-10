module

public import EthLib.Execution.Proofs.Blocks.AccessListCoverage
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the builder follows the last value of each field

The builder of a block access list records a change of a field at the position that made it.

A field is the balance, the nonce or the code of an account, or a word of its storage.

This file shows that the change at the greatest position holds the present value of the field.

A field with no change still holds its value from before the body.

Three facts about a call make this hold when the call joins the body.

The call ran on the block state of the body.

A key that the call did not write keeps its word, so the call wipes no word that the list misses.

The code that the call reads for an account it wrote has the code hash of that account.

The list keeps the code of each change, so it gives the code hash by its Keccak-256 hash.

It keeps a nonce in 64 bits, as EIP-2681 bounds it.

The list holds the changes of each field sorted by position, so the last one is the present value.

Source: [EIP-7928, Recording Semantics by Change Type][eip7928].

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#recording-semantics-by-change-type
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State (Account BlockState EMPTY_ACCOUNT TransactionState)
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-! ## The values that a list gives -/

namespace BlockAccessList

/-- The entry of an account in the list, if it has one. -/
def entry? (bal : BlockAccessList) (address : Address) : Option AccountChanges :=
  bal.find? (·.address = address)

/-- The balance of an account after the block: its last change in the list, or `base`. -/
def balanceAfter (bal : BlockAccessList) (address : Address) (base : U256) : U256 :=
  (((bal.entry? address).bind (·.balanceChanges.getLast?)).map (·.balance)).getD base

/-- The nonce of an account after the block: its last change in the list, or `base`. -/
def nonceAfter (bal : BlockAccessList) (address : Address) (base : UInt64) : UInt64 :=
  (((bal.entry? address).bind (·.nonceChanges.getLast?)).map (·.nonce)).getD base

/-- The code hash of an account after the block, or `base`.

It is the hash of the code of its last code change in the list. -/
def codeHashAfter (bal : BlockAccessList) (address : Address) (base : Hash32) : Hash32 :=
  (((bal.entry? address).bind (·.codeChanges.getLast?)).map fun c => keccak256 c.code).getD base

/-- The word at a key of an account after the block: its last change in the list, or `base`. -/
def storageAfter (bal : BlockAccessList) (address : Address) (key : Bytes32) (base : U256) :
    U256 :=
  ((((bal.entry? address).bind fun e => e.storageChanges.find? (·.slot = U256.fromBeBytes key)).bind
    (·.changes.getLast?)).map (·.value)).getD base

end BlockAccessList

/-! ## The calls that the builder follows -/

/-- The builder follows a call that ran on the block state `block` and ends with the state `tx`.

The call ran on `block`.

A key that the call did not write reads as it did in `block`, so a wipe hides no word.

The code that the call reads for an account it wrote has the code hash of that account. -/
structure Followable (block : BlockState) (tx : TransactionState) : Prop where
  /-- The call ran on the block state. -/
  parent : tx.parent = block
  /-- A key that the call did not write keeps its word. -/
  storage : ∀ address key, tx.storageWrites.slot address key = none →
    tx.getStorage address key = (TransactionState.ofBlock block).getStorage address key
  /-- The code of each account that the call wrote has the code hash of that account. -/
  code : ∀ (address : Address) (written : Option Account) code,
    tx.accountWrites[address]? = some written →
    tx.getCode (written.getD EMPTY_ACCOUNT).codeHash = .ok code →
    keccak256 code = (written.getD EMPTY_ACCOUNT).codeHash

namespace AccessListBuilder

/-! ## The changes of one field -/

/-- The value of the change at the greatest position, read through `view`, or `base` if none. -/
def lastOr {α β : Type} (view : α → β) (changes : Std.ExtTreeMap UInt32 α) (base : β) : β :=
  (changes.toList.getLast?.map fun change => view change.2).getD base

/-- The balance changes of an account. -/
def balances (b : AccessListBuilder) (address : Address) : Std.ExtTreeMap UInt32 U256 :=
  (b.accounts[address]?.map (·.balanceChanges)).getD ∅

/-- The nonce changes of an account. -/
def nonces (b : AccessListBuilder) (address : Address) : Std.ExtTreeMap UInt32 Nat :=
  (b.accounts[address]?.map (·.nonceChanges)).getD ∅

/-- The code changes of an account. -/
def codes (b : AccessListBuilder) (address : Address) : Std.ExtTreeMap UInt32 ByteArray :=
  (b.accounts[address]?.map (·.codeChanges)).getD ∅

/-- The changes of the word at a key of an account. -/
def slotChanges (b : AccessListBuilder) (address : Address) (key : Bytes32) :
    Std.ExtTreeMap UInt32 U256 :=
  (b.accounts[address]?.bind (·.storageChanges[key]?)).getD ∅

/-- The changes `changes` of a field follow it, read through `view`, up to the position `index`.

The field is `base` before the body, `start` when the position began, and `now` at present.

No change is past the position.

The last change before the position, or `base`, is `start`.

The position holds a change when the field differs from `start`, and the change is `now`. -/
structure FieldTracks {α β : Type} (view : α → β) (changes : Std.ExtTreeMap UInt32 α)
    (index : UInt32) (base start now : β) : Prop where
  /-- No change is past the position. -/
  le : ∀ j ∈ changes, j ≤ index
  /-- The last change before the position, or `base`, is the value when the position began. -/
  before : lastOr view (changes.erase index) base = start
  /-- The position holds no change when the field is as it began. -/
  unchanged : now = start → changes[index]? = none
  /-- The position holds the present value when the field differs from its start. -/
  changed : now ≠ start → changes[index]?.map view = some now

/-- Erasing a position with no change leaves the changes as they are. -/
private theorem erase_eq_self_of_getElem? {α : Type} {changes : Std.ExtTreeMap UInt32 α}
    {index : UInt32} (h : changes[index]? = none) : changes.erase index = changes := by
  apply Std.ExtTreeMap.ext_getElem?
  intro j
  rw [Std.ExtTreeMap.getElem?_erase]
  split
  · rename_i hj
    rw [Std.compare_eq_iff_eq] at hj
    subst hj
    exact h.symm
  · rfl

/-- The last change of a field that the builder follows, or its value before the body, is now. -/
theorem FieldTracks.lastOr_eq {α β : Type} {view : α → β} {changes : Std.ExtTreeMap UInt32 α}
    {index : UInt32} {base start now : β}
    (h : FieldTracks view changes index base start now) : lastOr view changes base = now := by
  cases hat : changes[index]? with
  | none =>
    have herase := erase_eq_self_of_getElem? hat
    have hnow : now = start := by
      refine Classical.byContradiction fun hne => ?_
      have := h.changed hne
      rw [hat] at this
      cases this
    rw [hnow, ← h.before, herase]
  | some v =>
    have hne : now ≠ start := fun heq => by
      have := h.unchanged heq
      rw [hat] at this
      cases this
    have hview := h.changed hne
    rw [hat] at hview
    have hmax : changes.maxKey? = some index := by
      rw [Std.ExtTreeMap.maxKey?_eq_some_iff_mem_and_forall]
      refine ⟨Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hat]), fun j hj => ?_⟩
      have := h.le j hj
      simp only [Ordering.isLE_iff_ne_gt, Std.compare_eq_gt]
      exact UInt32.not_lt.mpr this
    rw [Std.ExtTreeMap.maxKey?_eq_getLast?_keys, ← Std.ExtTreeMap.map_fst_toList_eq_keys,
      List.getLast?_map] at hmax
    obtain ⟨⟨k, w⟩, hlast, hk⟩ := Option.map_eq_some_iff.mp hmax
    cases hk
    have hmem := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_of_getLast? hlast)
    rw [hat] at hmem
    cases hmem
    simpa [lastOr, hlast] using hview

/-- A field with no change follows itself at any position. -/
private theorem FieldTracks.empty {α β : Type} (view : α → β) (index : UInt32) (value : β) :
    FieldTracks view ∅ index value value value :=
  ⟨fun _ h => absurd h Std.ExtTreeMap.not_mem_empty,
    by simp [lastOr, Std.ExtTreeMap.toList_eq_nil_iff.mpr rfl],
    fun _ => Std.ExtTreeMap.getElem?_empty, fun h => absurd rfl h⟩

/-- A later position starts each field from its present value. -/
private theorem FieldTracks.begin {α β : Type} {view : α → β} {changes : Std.ExtTreeMap UInt32 α}
    {index index' : UInt32} {base start now : β}
    (h : FieldTracks view changes index base start now) (hindex : index < index') :
    FieldTracks view changes index' base now now := by
  have hnone : changes[index']? = none := by
    refine Std.ExtTreeMap.getElem?_eq_none fun hmem => ?_
    exact absurd (h.le _ hmem) (UInt32.not_le.mpr hindex)
  refine ⟨fun j hj => UInt32.le_of_lt (UInt32.lt_of_le_of_lt (h.le j hj) hindex), ?_,
    fun _ => hnone, fun h => absurd rfl h⟩
  rw [erase_eq_self_of_getElem? hnone]
  exact h.lastOr_eq

/-- Changes that differ only at the position follow a field that is new only there. -/
private theorem FieldTracks.step {α β : Type} {view : α → β}
    {changes changes' : Std.ExtTreeMap UInt32 α} {index : UInt32} {base start now now' : β}
    (h : FieldTracks view changes index base start now)
    (hother : ∀ j, j ≠ index → changes'[j]? = changes[j]?)
    (hunchanged : now' = start → changes'[index]? = none)
    (hchanged : now' ≠ start → changes'[index]?.map view = some now') :
    FieldTracks view changes' index base start now' := by
  refine ⟨fun j hj => ?_, ?_, hunchanged, hchanged⟩
  · by_cases hji : j = index
    · exact hji ▸ UInt32.le_refl _
    · refine h.le j (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr ?_)
      rw [← hother j hji]
      exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hj
  · have : changes'.erase index = changes.erase index := by
      apply Std.ExtTreeMap.ext_getElem?
      intro j
      simp only [Std.ExtTreeMap.getElem?_erase, Std.compare_eq_iff_eq]
      split
      · rfl
      · exact hother j (Ne.symm ‹_›)
    rw [this]
    exact h.before

/-! ## The builder -/

/-- The builder follows each field of each account, from the block state `base` to `now`.

The balance and the nonce are followed as they are.

The code is followed by its hash.

The block state when the current position began is the start of the builder. -/
structure Tracks (b : AccessListBuilder) (base now : BlockState) : Prop where
  /-- The builder follows each balance. -/
  balance : ∀ address, FieldTracks id (b.balances address) b.index
    ((TransactionState.ofBlock base).getAccount address).balance
    (b.startAccount address).balance ((TransactionState.ofBlock now).getAccount address).balance
  /-- The builder follows each nonce. -/
  nonce : ∀ address, FieldTracks id (b.nonces address) b.index
    ((TransactionState.ofBlock base).getAccount address).nonce
    (b.startAccount address).nonce ((TransactionState.ofBlock now).getAccount address).nonce
  /-- The builder follows each code by its hash. -/
  code : ∀ address, FieldTracks keccak256 (b.codes address) b.index
    ((TransactionState.ofBlock base).getAccount address).codeHash
    (b.startAccount address).codeHash
    ((TransactionState.ofBlock now).getAccount address).codeHash
  /-- The builder follows each word of storage. -/
  storage : ∀ address key, FieldTracks id (b.slotChanges address key) b.index
    ((TransactionState.ofBlock base).getStorage address key) (b.startStorage address key)
    ((TransactionState.ofBlock now).getStorage address key)

/-- A builder at its start follows the block state that it starts from. -/
theorem Tracks.init (block : BlockState) : (init block).Tracks block block :=
  ⟨fun _ => FieldTracks.empty _ _ _, fun _ => FieldTracks.empty _ _ _,
    fun _ => FieldTracks.empty _ _ _, fun _ _ => FieldTracks.empty _ _ _⟩

/-- A builder that begins a later position from the present block state still follows it. -/
theorem Tracks.beginIndex {b : AccessListBuilder} {base now : BlockState} {index : UInt32}
    (h : b.Tracks base now) (hindex : b.index < index) :
    (b.beginIndex index now).Tracks base now :=
  ⟨fun a => (h.balance a).begin hindex, fun a => (h.nonce a).begin hindex,
    fun a => (h.code a).begin hindex, fun a k => (h.storage a k).begin hindex⟩

/-! ## One call -/

/-- Changes equal at every position follow the same field, now at the same value. -/
private theorem FieldTracks.congr {α β : Type} {view : α → β}
    {changes changes' : Std.ExtTreeMap UInt32 α} {index : UInt32} {base start now : β}
    (h : FieldTracks view changes index base start now)
    (hchanges : ∀ j : UInt32, changes'[j]? = changes[j]?) :
    FieldTracks view changes' index base start now := by
  rw [Std.ExtTreeMap.ext_getElem? hchanges]
  exact h

/-- Changes that hold the new value at the position, when it differs, follow the field there. -/
private theorem FieldTracks.write {α β : Type} [DecidableEq β] {view : α → β}
    {changes changes' : Std.ExtTreeMap UInt32 α} {index : UInt32} {base start now : β}
    (h : FieldTracks view changes index base start now) (after : β)
    (hother : ∀ j, j ≠ index → changes'[j]? = changes[j]?)
    (hat : changes'[index]?.map view = if start ≠ after then some after else none) :
    FieldTracks view changes' index base start after := by
  refine h.step hother (fun he => ?_) (fun hne => ?_)
  · simp only [he, ne_eq, not_true_eq_false, ↓reduceIte] at hat
    exact Option.map_eq_none_iff.mp hat
  · simp [hat, Ne.symm hne]

/-- A fold whose every step keeps a value keeps it. -/
private theorem foldl_keep {α β γ : Type} (f : β → α → β) (g : β → γ)
    (hf : ∀ b x, g (f b x) = g b) : ∀ (l : List α) (b : β), g (l.foldl f b) = g b
  | [], _ => rfl
  | x :: l, b => (foldl_keep f g hf l (f b x)).trans (hf b x)

/-- A fold that can fail, over distinct keys, whose step changes a value only at its own key. -/
private theorem foldlM_point {α β γ ε κ : Type} {f : β → α → Except ε β} (P : β → Prop)
    (g : β → γ) (key : α → κ) (k : κ) (H : α → γ → γ) :
    ∀ (l : List α), l.Pairwise (fun x y => key x ≠ key y) →
    (∀ x ∈ l, ∀ b b', P b → f b x = .ok b' → P b') →
    (∀ x ∈ l, ∀ b b', P b → f b x = .ok b' → key x ≠ k → g b' = g b) →
    (∀ x ∈ l, ∀ b b', P b → f b x = .ok b' → key x = k → g b' = H x (g b)) →
    ∀ b b', P b → l.foldlM f b = .ok b' →
      P b' ∧ ((∀ x ∈ l, key x ≠ k) → g b' = g b) ∧ (∀ x ∈ l, key x = k → g b' = H x (g b))
  | [], _, _, _, _, b, b', hb, h => by
    cases h
    exact ⟨hb, fun _ => rfl, fun _ hx => absurd hx List.not_mem_nil⟩
  | x :: l, hl, hP, hother, hself, b, b', hb, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b₁, h₁, h⟩ := bind_ok_iff.mp h
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hl
    have hb₁ := hP x List.mem_cons_self b b₁ hb h₁
    obtain ⟨hb', hnone, hsome⟩ := foldlM_point P g key k H l htail
      (fun y hy => hP y (List.mem_cons_of_mem _ hy))
      (fun y hy => hother y (List.mem_cons_of_mem _ hy))
      (fun y hy => hself y (List.mem_cons_of_mem _ hy)) b₁ b' hb₁ h
    refine ⟨hb', fun hall => ?_, fun y hy hky => ?_⟩
    · rw [hnone fun y hy => hall y (List.mem_cons_of_mem _ hy)]
      exact hother x List.mem_cons_self b b₁ hb h₁ (hall x List.mem_cons_self)
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [hnone fun z hz hkz => hhead z hz (hky.trans hkz.symm)]
        exact hself y List.mem_cons_self b b₁ hb h₁ hky
      · rw [hsome y hy hky]
        rw [hother x List.mem_cons_self b b₁ hb h₁ fun hkx => hhead y hy (hkx.trans hky.symm)]

/-- A fold over distinct keys whose step changes a value only at its own key. -/
private theorem foldl_point {α β γ κ : Type} (f : β → α → β) (P : β → Prop)
    (g : β → γ) (key : α → κ) (k : κ) (H : α → γ → γ) (l : List α)
    (hl : l.Pairwise (fun x y => key x ≠ key y))
    (hP : ∀ x ∈ l, ∀ b, P b → P (f b x))
    (hother : ∀ x ∈ l, ∀ b, P b → key x ≠ k → g (f b x) = g b)
    (hself : ∀ x ∈ l, ∀ b, P b → key x = k → g (f b x) = H x (g b)) (b : β) (hb : P b) :
    P (l.foldl f b) ∧ ((∀ x ∈ l, key x ≠ k) → g (l.foldl f b) = g b) ∧
      (∀ x ∈ l, key x = k → g (l.foldl f b) = H x (g b)) :=
  foldlM_point (ε := Empty) (f := fun b x => .ok (f b x)) P g key k H l hl
    (fun x hx b b' hb h => by cases h; exact hP x hx b hb)
    (fun x hx b b' hb h => by cases h; exact hother x hx b hb)
    (fun x hx b b' hb h => by cases h; exact hself x hx b hb) b _ hb
    (foldlM_eq_ok_foldl (fun _ _ _ => rfl) b)

/-- The entries of a map have distinct keys. -/
private theorem pairwise_toList {κ β : Type} [Ord κ] [Std.TransOrd κ] [Std.LawfulEqOrd κ]
    (m : Std.ExtTreeMap κ β) : m.toList.Pairwise (fun x y => x.1 ≠ y.1) :=
  Std.ExtTreeMap.distinct_keys_toList.imp fun h heq => h (Std.compare_eq_iff_eq.mpr heq)

/-- A field of the record of an account, read at a position. -/
private theorem getElem?_field {β : Type} (b : AccessListBuilder) (address : Address)
    (get : AccountRecord → Std.ExtTreeMap UInt32 β) (j : UInt32) :
    ((b.accounts[address]?.map get).getD ∅)[j]? =
      b.accounts[address]?.bind fun r => (get r)[j]? := by
  cases b.accounts[address]? <;> simp

/-- The changes of a key of an account, read at a position. -/
private theorem getElem?_slotChanges (b : AccessListBuilder) (address : Address)
    (key : Bytes32) (j : UInt32) :
    (b.slotChanges address key)[j]? =
      b.accounts[address]?.bind fun r => (r.storageChanges.getD key ∅)[j]? := by
  unfold slotChanges
  cases b.accounts[address]? with
  | none => simp
  | some r => cases h : r.storageChanges[key]? <;> simp [Std.ExtTreeMap.getD_eq_getD_getElem?, h]

/-- The changes of a key, read through the map of keys or through its default, agree. -/
private theorem slot_bind (x : Option AccountRecord) (key : Bytes32) (j : UInt32) :
    ((x.bind fun r => r.storageChanges[key]?).bind (·[j]?)) =
      x.bind fun r => (r.storageChanges.getD key ∅)[j]? := by
  cases x with
  | none => rfl
  | some r => cases h : r.storageChanges[key]? <;> simp [Std.ExtTreeMap.getD_eq_getD_getElem?, h]

/-- A change of a record that keeps a field keeps each value of that field. -/
private theorem record_keep {β : Type} (b : AccessListBuilder) (address other : Address)
    (f : AccountRecord → AccountRecord) (get : AccountRecord → Std.ExtTreeMap UInt32 β)
    (hget : ∀ r, get (f r) = get r) (hempty : get {} = ∅) (index : UInt32) :
    ((b.record address f).accounts[other]?.bind fun r => (get r)[index]?) =
      b.accounts[other]?.bind fun r => (get r)[index]? := by
  unfold record
  cases h : b.accounts[address]? <;> cases h' : b.accounts[other]? <;>
    simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getD_eq_getD_getElem?, h, h', hempty,
      hget] <;>
    first | (rintro rfl; simp_all) | (split <;> simp_all)

/-- A change of the record of an account keeps the record of every other account. -/
private theorem record_ne (b : AccessListBuilder) {address other : Address}
    (f : AccountRecord → AccountRecord) (hne : address ≠ other) :
    (b.record address f).accounts[other]? = b.accounts[other]? := by
  simp [record, Std.ExtTreeMap.getElem?_insert, hne]

/-- A field change keeps the record of every other account. -/
private theorem setField_ne {α : Type} (b : AccessListBuilder) {address other : Address}
    (changed : Bool) (value : α) (field : AccountRecord → Std.ExtTreeMap UInt32 α)
    (update : AccountRecord → Std.ExtTreeMap UInt32 α → AccountRecord) (hne : address ≠ other) :
    (b.setField address changed value field update).accounts[other]? = b.accounts[other]? := by
  unfold setField
  split
  · exact record_ne _ _ hne
  · simp [amend, Std.ExtTreeMap.getElem?_modify, hne]

/-- A field change keeps the position and its start. -/
private theorem setField_index {α : Type} (b : AccessListBuilder) (address : Address)
    (changed : Bool) (value : α) (field : AccountRecord → Std.ExtTreeMap UInt32 α)
    (update : AccountRecord → Std.ExtTreeMap UInt32 α → AccountRecord) :
    (b.setField address changed value field update).index = b.index ∧
      (b.setField address changed value field update).start = b.start := by
  unfold setField
  split <;> exact ⟨rfl, rfl⟩

/-- An account write keeps the position and its start. -/
private theorem recordAccountWrite_index {b b' : AccessListBuilder} {tx : TransactionState}
    {address : Address} {written : Option Account}
    (h : b.recordAccountWrite tx address written = .ok b') :
    b'.index = b.index ∧ b'.start = b.start := by
  unfold recordAccountWrite at h
  dsimp only at h
  split at h
  all_goals
    obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    cases h
    refine ⟨(setField_index _ _ _ _ _ _).1.trans ?_, (setField_index _ _ _ _ _ _).2.trans ?_⟩
    · exact ((setField_index _ _ _ _ _ _).1.trans (setField_index _ _ _ _ _ _).1)
    · exact ((setField_index _ _ _ _ _ _).2.trans (setField_index _ _ _ _ _ _).2)

/-- An account write keeps the record of every other account. -/
private theorem recordAccountWrite_ne {b b' : AccessListBuilder} {tx : TransactionState}
    {address other : Address} {written : Option Account}
    (h : b.recordAccountWrite tx address written = .ok b') (hne : address ≠ other) :
    b'.accounts[other]? = b.accounts[other]? := by
  unfold recordAccountWrite at h
  dsimp only at h
  split at h
  all_goals
    obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    cases h
    rw [setField_ne _ _ _ _ _ hne, setField_ne _ _ _ _ _ hne, setField_ne _ _ _ _ _ hne,
      record_ne _ _ hne]

/-- An account write keeps the changes of every storage key. -/
private theorem recordAccountWrite_slot {b b' : AccessListBuilder} {tx : TransactionState}
    {address : Address} {written : Option Account}
    (h : b.recordAccountWrite tx address written = .ok b') (other : Address) (key : Bytes32)
    (index : UInt32) :
    (b'.accounts[other]?.bind fun r => (r.storageChanges.getD key ∅)[index]?) =
      b.accounts[other]?.bind fun r => (r.storageChanges.getD key ∅)[index]? := by
  unfold recordAccountWrite at h
  dsimp only at h
  split at h
  all_goals
    obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    cases h
    rw [setField_other (get := fun r => r.storageChanges.getD key ∅) (hget := by intros; rfl)
        (hempty := rfl),
      setField_other (get := fun r => r.storageChanges.getD key ∅) (hget := by intros; rfl)
        (hempty := rfl),
      setField_other (get := fun r => r.storageChanges.getD key ∅) (hget := by intros; rfl)
        (hempty := rfl),
      record_id_at (get := fun r => r.storageChanges.getD key ∅) (hempty := rfl)]

/-- An account write records its nonce at the current position when the nonce changed. -/
private theorem recordAccountWrite_nonce_at {b b' : AccessListBuilder} {tx : TransactionState}
    {address : Address} {written : Option Account}
    (h : b.recordAccountWrite tx address written = .ok b') (index : UInt32) :
    (b'.accounts[address]?.bind fun r => r.nonceChanges[index]?) =
      let before := (b.startAccount address).nonce
      let after := (written.getD EMPTY_ACCOUNT).nonce
      if index = b.index then (if before ≠ after then some after else none)
      else b.accounts[address]?.bind fun r => r.nonceChanges[index]? := by
  unfold recordAccountWrite at h
  dsimp only at h
  split at h
  all_goals
    obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    cases h
    rw [setField_other (get := fun r => r.nonceChanges) (hget := by intros; rfl) (hempty := rfl),
      setField_at (hfield := by intros; rfl) (hempty := rfl),
      setField_other (get := fun r => r.nonceChanges) (hget := by intros; rfl) (hempty := rfl),
      record_id_at (get := fun r => r.nonceChanges) (hempty := rfl),
      (setField_index _ _ _ _ _ _).1]
    simp only [decide_eq_true_eq]
    rfl

/-- An account write records its code at the current position when the code hash changed. -/
private theorem recordAccountWrite_code_at {b b' : AccessListBuilder} {tx : TransactionState}
    {address : Address} {written : Option Account}
    (h : b.recordAccountWrite tx address written = .ok b') (index : UInt32) :
    (b'.accounts[address]?.bind fun r => r.codeChanges[index]?) =
      if index = b.index then
        (if (b.startAccount address).codeHash ≠ (written.getD EMPTY_ACCOUNT).codeHash then
          (tx.getCode (written.getD EMPTY_ACCOUNT).codeHash).toOption else none)
      else b.accounts[address]?.bind fun r => r.codeChanges[index]? := by
  unfold recordAccountWrite at h
  dsimp only at h
  split at h
  all_goals
    obtain ⟨code, hcode, h⟩ := bind_ok_iff.mp h
    cases h
    rw [setField_at (hfield := by intros; rfl) (hempty := rfl),
      setField_other (get := fun r => r.codeChanges) (hget := by intros; rfl) (hempty := rfl),
      setField_other (get := fun r => r.codeChanges) (hget := by intros; rfl) (hempty := rfl),
      record_id_at (get := fun r => r.codeChanges) (hempty := rfl),
      (setField_index _ _ _ _ _ _).1, (setField_index _ _ _ _ _ _).1]
    rename_i hc
    simp only [show (b.record address id).index = b.index from rfl,
      show (b.record address id).startAccount address = b.startAccount address from rfl] at hc ⊢
    first | simp [hc, hcode, Except.toOption] | simp [hc]

/-- An account write whose code hash changed found the new code. -/
private theorem recordAccountWrite_getCode {b b' : AccessListBuilder} {tx : TransactionState}
    {address : Address} {written : Option Account}
    (h : b.recordAccountWrite tx address written = .ok b')
    (hne : (b.startAccount address).codeHash ≠ (written.getD EMPTY_ACCOUNT).codeHash) :
    ∃ code, tx.getCode (written.getD EMPTY_ACCOUNT).codeHash = .ok code := by
  unfold recordAccountWrite at h
  dsimp only at h
  split at h
  · obtain ⟨code, hcode, -⟩ := bind_ok_iff.mp h
    exact ⟨code, hcode⟩
  · exact absurd hne ‹_›

/-- A storage write keeps the position and its start. -/
private theorem recordStorageWrite_index (b : AccessListBuilder) (address : Address)
    (key : Bytes32) (value : U256) :
    (b.recordStorageWrite address key value).index = b.index ∧
      (b.recordStorageWrite address key value).start = b.start := by
  unfold recordStorageWrite
  split <;> exact ⟨rfl, rfl⟩

/-- A storage write keeps each field outside the storage. -/
private theorem recordStorageWrite_keep {β : Type} (b : AccessListBuilder)
    (address other : Address) (key : Bytes32) (value : U256)
    (get : AccountRecord → Std.ExtTreeMap UInt32 β)
    (hget : ∀ r s c, get { r with storageChanges := s, storageReads := c } = get r)
    (hempty : get {} = ∅) (index : UInt32) :
    ((b.recordStorageWrite address key value).accounts[other]?.bind fun r => (get r)[index]?) =
      b.accounts[other]?.bind fun r => (get r)[index]? := by
  unfold recordStorageWrite
  split
  · exact record_keep _ _ _ _ _ (fun r => hget r _ r.storageReads) hempty _
  · exact record_keep _ _ _ _ _ (fun r => hget r _ _) hempty _

/-- A storage write records its value at its own key and position, and keeps every other. -/
private theorem recordStorageWrite_slot (b : AccessListBuilder) (address : Address)
    (key : Bytes32) (value : U256) (other : Address) (k : Bytes32) (j : UInt32) :
    ((b.recordStorageWrite address key value).accounts[other]?.bind
        fun r => (r.storageChanges.getD k ∅)[j]?) =
      if other = address ∧ k = key ∧ j = b.index then
        (if b.startStorage address key ≠ value then some value else none)
      else b.accounts[other]?.bind fun r => (r.storageChanges.getD k ∅)[j]? := by
  by_cases ha : other = address
  · subst ha
    by_cases hk : k = key
    · subst hk
      rw [← slot_bind, ← slot_bind, recordStorageWrite_at]
      simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hk h.2.1)]
      unfold recordStorageWrite
      split
      · exact record_keep _ _ _ _ (fun r => r.storageChanges.getD k ∅)
          (fun r => by simp [Std.ExtTreeMap.getD_insert, Ne.symm hk]) (by simp) _
      · exact record_keep _ _ _ _ (fun r => r.storageChanges.getD k ∅)
          (fun r => dropSlotChange_getD_of_ne _ _ (Ne.symm hk)) (by simp) _
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => ha h.1)]
    unfold recordStorageWrite
    split <;> rw [record_ne _ _ (Ne.symm ha)]

/-- A fold that can fail, whose every step keeps a value, keeps it. -/
private theorem foldlM_keep {α β γ ε : Type} {f : β → α → Except ε β} (g : β → γ)
    (hf : ∀ b x b', f b x = .ok b' → g b' = g b) :
    ∀ (l : List α) (b b' : β), l.foldlM f b = .ok b' → g b' = g b
  | [], _, _, h => by cases h; rfl
  | x :: l, b, b', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b₁, h₁, h⟩ := bind_ok_iff.mp h
    exact (foldlM_keep g hf l b₁ b' h).trans (hf b x b₁ h₁)

/-- Every step of a fold that succeeds succeeds, from a value that keeps an invariant. -/
private theorem foldlM_each {α β ε : Type} {f : β → α → Except ε β} (P : β → Prop)
    (hP : ∀ b x b', P b → f b x = .ok b' → P b') :
    ∀ (l : List α) (b b' : β), P b → l.foldlM f b = .ok b' →
      ∀ x ∈ l, ∃ c c', P c ∧ f c x = .ok c'
  | [], _, _, _, _, x, hx => absurd hx List.not_mem_nil
  | y :: l, b, b', hb, h, x, hx => by
    rw [List.foldlM_cons] at h
    obtain ⟨b₁, h₁, h⟩ := bind_ok_iff.mp h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, b₁, hb, h₁⟩
    · exact foldlM_each P hP l b₁ b' (hP b y b₁ hb h₁) h x hx

/-- The steps of the record of a call: the reads, then the account writes, then the storage. -/
private theorem recordTransaction_eq {b b' : AccessListBuilder} {tx : TransactionState}
    (h : b.recordTransaction tx = .ok b') :
    ∃ b₂ b₃ : AccessListBuilder,
      (∀ {γ : Type} (g : AccessListBuilder → γ), (∀ c a, g (c.record a id) = g c) →
        (∀ c a (keys : List Bytes32), g (c.record a fun r =>
          { r with storageReads := r.storageReads.insertMany keys }) = g c) → g b₂ = g b) ∧
      tx.accountWrites.toList.foldlM (fun c x => c.recordAccountWrite tx x.1 x.2) b₂ = .ok b₃ ∧
      b' = tx.storageWrites.toList.foldl
        (fun c x => x.2.toList.foldl (fun c y => c.recordStorageWrite x.1 y.1 y.2) c) b₃ := by
  unfold recordTransaction at h
  obtain ⟨b₃, h₃, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeMap.foldlM_eq_foldlM_toList] at h₃
  refine ⟨_, b₃, fun g h₁ h₂ => ?_, h₃, ?_⟩
  · rw [Std.ExtTreeMap.foldl_eq_foldl_toList, Std.ExtTreeSet.foldl_eq_foldl_toList,
      foldl_keep _ g (fun c (x : Address × Std.ExtTreeSet Bytes32) => h₂ c x.1 x.2.toList),
      foldl_keep _ g (fun c x => h₁ c x)]
  · simp only [Std.ExtTreeMap.foldl_eq_foldl_toList]

/-- The storage writes of a call keep every value that each storage write keeps. -/
private theorem storageWrites_keep {γ : Type} (tx : TransactionState) (c : AccessListBuilder)
    (g : AccessListBuilder → γ) (hg : ∀ d a k v, g (d.recordStorageWrite a k v) = g d) :
    g (tx.storageWrites.toList.foldl
      (fun c x => x.2.toList.foldl (fun c y => c.recordStorageWrite x.1 y.1 y.2) c) c) = g c :=
  foldl_keep _ g (fun d (x : Address × Std.ExtTreeMap Bytes32 U256) =>
    foldl_keep _ g (fun d (y : Bytes32 × U256) => hg d x.1 y.1 y.2) x.2.toList d) _ _

/-- The start of a builder gives the account at an address. -/
private theorem startAccount_eq {c d : AccessListBuilder} (h : c.start = d.start)
    (address : Address) : c.startAccount address = d.startAccount address := by
  unfold startAccount
  rw [h]

/-- The start of a builder gives the word at a key. -/
private theorem startStorage_eq {c d : AccessListBuilder} (h : c.start = d.start)
    (address : Address) (key : Bytes32) :
    c.startStorage address key = d.startStorage address key := by
  unfold startStorage
  rw [h]

/-- The storage writes of a call record each written word at its key, and nothing else. -/
private theorem storageWrites_slot (tx : TransactionState) (c : AccessListBuilder)
    (a : Address) (k : Bytes32) (j : UInt32) :
    ((tx.storageWrites.toList.foldl
        (fun c x => x.2.toList.foldl (fun c y => c.recordStorageWrite x.1 y.1 y.2) c)
        c).accounts[a]?.bind fun r => (r.storageChanges.getD k ∅)[j]?) =
      match tx.storageWrites.slot a k with
      | some v => if j = c.index then (if c.startStorage a k ≠ v then some v else none)
        else c.accounts[a]?.bind fun r => (r.storageChanges.getD k ∅)[j]?
      | none => c.accounts[a]?.bind fun r => (r.storageChanges.getD k ∅)[j]? := by
  let P : AccessListBuilder → Prop := fun d => d.index = c.index ∧ d.start = c.start
  let g : AccessListBuilder → Option U256 :=
    fun d => d.accounts[a]?.bind fun r => (r.storageChanges.getD k ∅)[j]?
  let H : Bytes32 × U256 → Option U256 → Option U256 := fun y old =>
    if j = c.index then (if c.startStorage a k ≠ y.2 then some y.2 else none) else old
  have hindex : ∀ (x : Address × Std.ExtTreeMap Bytes32 U256) d, P d →
      P (x.2.toList.foldl (fun c y => c.recordStorageWrite x.1 y.1 y.2) d) := by
    intro x d hd
    have := foldl_keep _ (fun d : AccessListBuilder => (d.index, d.start))
      (fun d y => Prod.ext (recordStorageWrite_index d x.1 y.1 y.2).1
        (recordStorageWrite_index d x.1 y.1 y.2).2) x.2.toList d
    exact ⟨(Prod.mk.inj this).1.trans hd.1, (Prod.mk.inj this).2.trans hd.2⟩
  have inner : ∀ slots : Std.ExtTreeMap Bytes32 U256, ∀ d, P d →
      ((∀ y ∈ slots.toList, y.1 ≠ k) →
        g (slots.toList.foldl (fun c y => c.recordStorageWrite a y.1 y.2) d) = g d) ∧
      (∀ y ∈ slots.toList, y.1 = k →
        g (slots.toList.foldl (fun c y => c.recordStorageWrite a y.1 y.2) d) = H y (g d)) := by
    intro slots d hd
    refine (foldl_point (fun c y => c.recordStorageWrite a y.1 y.2) P g Prod.fst k H
      slots.toList (pairwise_toList _) (fun y _ e he => ?_) (fun y _ e _ hne => ?_)
      (fun y _ e he hy => ?_) d hd).2
    · exact ⟨(recordStorageWrite_index e a y.1 y.2).1.trans he.1,
        (recordStorageWrite_index e a y.1 y.2).2.trans he.2⟩
    · simp only [g]
      rw [recordStorageWrite_slot, ite_eq_right_of_eq_false _ _ (eq_false fun h => hne h.2.1.symm)]
    · simp only [g, H]
      rw [recordStorageWrite_slot, he.1, startStorage_eq he.2, hy]
      simp
  have outer := foldl_point
    (fun c x => x.2.toList.foldl (fun c y => c.recordStorageWrite x.1 y.1 y.2) c) P g Prod.fst a
    (fun x old => match x.2[k]? with
      | some v => H (k, v) old
      | none => old)
    tx.storageWrites.toList (pairwise_toList _) (fun x _ d hd => hindex x d hd)
    (fun x _ d _ hne => foldl_keep _ g (fun e y => by
      simp only [g]
      rw [recordStorageWrite_slot,
        ite_eq_right_of_eq_false _ _ (eq_false fun h => hne h.1.symm)]) x.2.toList d)
    (fun x _ d hd hx => by
      obtain ⟨x, slots⟩ := x
      dsimp only at hx
      subst hx
      dsimp only
      cases hk : slots[k]? with
      | some v =>
        exact (inner slots d hd).2 (k, v)
          (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hk) rfl
      | none =>
        refine (inner slots d hd).1 fun y hy hyk => ?_
        rw [← hyk, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hy] at hk
        cases hk)
    c ⟨rfl, rfl⟩
  simp only [State.StorageMap.slot]
  cases hw : tx.storageWrites[a]? with
  | none =>
    refine outer.2.1 fun x hx hxa => ?_
    rw [← hxa, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hx] at hw
    cases hw
  | some slots =>
    refine (outer.2.2 (a, slots)
      (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hw) rfl).trans ?_
    simp only [Option.bind_some]
    cases slots[k]? <;> rfl

/-- The account writes of a call record each written field at its account, and nothing else. -/
private theorem accountWrites_point {β : Type} {tx : TransactionState}
    {b b₂ b₃ : AccessListBuilder} (hP₂ : b₂.index = b.index ∧ b₂.start = b.start)
    (h₃ : tx.accountWrites.toList.foldlM (fun c x => c.recordAccountWrite tx x.1 x.2) b₂ =
      .ok b₃)
    (get : AccountRecord → Std.ExtTreeMap UInt32 β) (V : Address → Option Account → Option β)
    (hat : ∀ (c c' : AccessListBuilder) (a : Address) (w : Option Account),
      c.index = b.index → c.start = b.start →
      c.recordAccountWrite tx a w = .ok c' → ∀ j,
        (c'.accounts[a]?.bind fun r => (get r)[j]?) =
          if j = b.index then V a w else c.accounts[a]?.bind fun r => (get r)[j]?)
    (a : Address) (j : UInt32) :
    (b₃.accounts[a]?.bind fun r => (get r)[j]?) =
      match tx.accountWrites[a]? with
      | some w => if j = b.index then V a w else b₂.accounts[a]?.bind fun r => (get r)[j]?
      | none => b₂.accounts[a]?.bind fun r => (get r)[j]? := by
  have point := foldlM_point (fun c => c.index = b.index ∧ c.start = b.start)
    (fun c => c.accounts[a]?.bind fun r => (get r)[j]?) Prod.fst a
    (fun x old => if j = b.index then V a x.2 else old) tx.accountWrites.toList
    (pairwise_toList _)
    (fun _ _ c c' hc h => ⟨(recordAccountWrite_index h).1.trans hc.1,
      (recordAccountWrite_index h).2.trans hc.2⟩)
    (fun _ _ c c' _ h hne => by simp only [recordAccountWrite_ne h hne])
    (fun x _ c c' hc h hx => by
      obtain ⟨x, w⟩ := x
      dsimp only at hx h ⊢
      subst hx
      exact hat c c' x w hc.1 hc.2 h j)
    b₂ b₃ hP₂ h₃
  cases hw : tx.accountWrites[a]? with
  | none =>
    refine point.2.1 fun x hx hxa => ?_
    rw [← hxa, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hx] at hw
    cases hw
  | some w =>
    exact point.2.2 (a, w) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hw) rfl

/-- After a call joins the block, a written account reads as the call left it. -/
private theorem getAccount_incorporate_some {tx : TransactionState} {address : Address}
    {written : Option Account} (hw : tx.accountWrites[address]? = some written) :
    (TransactionState.ofBlock tx.incorporateTxIntoBlock.parent).getAccount address =
      written.getD EMPTY_ACCOUNT := by
  show tx.incorporateTxIntoBlock.getAccount address = _
  unfold TransactionState.getAccount
  rw [TransactionState.getAccountOptional_incorporateTxIntoBlock]
  simp [TransactionState.getAccountOptional, hw]

/-- After a call joins the block, an account it did not write reads as in its block. -/
private theorem getAccount_incorporate_none {tx : TransactionState} {address : Address}
    (hw : tx.accountWrites[address]? = none) :
    (TransactionState.ofBlock tx.incorporateTxIntoBlock.parent).getAccount address =
      (TransactionState.ofBlock tx.parent).getAccount address := by
  show tx.incorporateTxIntoBlock.getAccount address = _
  unfold TransactionState.getAccount
  rw [TransactionState.getAccountOptional_incorporateTxIntoBlock]
  simp [TransactionState.getAccountOptional, TransactionState.ofBlock, hw]

/-- A builder that records a call it can follow then follows the block state after the call. -/
theorem Tracks.recordTransaction {b b' : AccessListBuilder} {base block : BlockState}
    {tx : TransactionState} (h : b.Tracks base block) (hfollow : Followable block tx)
    (hrecord : b.recordTransaction tx = .ok b') :
    b'.Tracks base tx.incorporateTxIntoBlock.parent := by
  obtain ⟨b₂, b₃, hkeep, h₃, hb'⟩ := recordTransaction_eq hrecord
  -- The position and its start stay.
  have hP₂ : b₂.index = b.index ∧ b₂.start = b.start :=
    Prod.mk.inj (hkeep (fun c => (c.index, c.start)) (fun _ _ => rfl) (fun _ _ _ => rfl))
  have hP₃ : b₃.index = b.index ∧ b₃.start = b.start := by
    have := foldlM_keep (fun c : AccessListBuilder => (c.index, c.start))
      (fun _ _ _ h => Prod.ext (recordAccountWrite_index h).1 (recordAccountWrite_index h).2)
      _ b₂ b₃ h₃
    exact ⟨(Prod.mk.inj this).1.trans hP₂.1, (Prod.mk.inj this).2.trans hP₂.2⟩
  have hidx : b'.index = b.index ∧ b'.start = b.start := by
    have := storageWrites_keep tx b₃ (fun c => (c.index, c.start))
      (fun d a k v => Prod.ext (recordStorageWrite_index d a k v).1
        (recordStorageWrite_index d a k v).2)
    rw [← hb'] at this
    exact ⟨(Prod.mk.inj this).1.trans hP₃.1, (Prod.mk.inj this).2.trans hP₃.2⟩
  -- The reads and the storage writes keep the balance, nonce and code changes.
  have hacc : ∀ {β : Type} (get : AccountRecord → Std.ExtTreeMap UInt32 β), get {} = ∅ →
      (∀ r s c, get { r with storageChanges := s, storageReads := c } = get r) →
      ∀ (a : Address) (j : UInt32), (b'.accounts[a]?.bind fun r => (get r)[j]?) =
          b₃.accounts[a]?.bind (fun r => (get r)[j]?) ∧
        (b₂.accounts[a]?.bind fun r => (get r)[j]?) =
          b.accounts[a]?.bind fun r => (get r)[j]? := by
    intro β get hempty hget a j
    refine ⟨?_, ?_⟩
    · rw [hb']
      exact storageWrites_keep tx b₃ (fun c => c.accounts[a]?.bind fun r => (get r)[j]?)
        (fun d a' k v => recordStorageWrite_keep d a' a k v get hget hempty j)
    · exact hkeep (fun c => c.accounts[a]?.bind fun r => (get r)[j]?)
        (fun c a' => record_keep c a' a id get (fun _ => rfl) hempty j)
        (fun c a' _ => record_keep c a' a _ get (fun r => hget r r.storageChanges _) hempty j)
  -- Only the storage writes change the storage changes.
  have hslot : ∀ (a : Address) (k : Bytes32) (j : UInt32), (b'.slotChanges a k)[j]? =
      match tx.storageWrites.slot a k with
      | some v => if j = b.index then (if b.startStorage a k ≠ v then some v else none)
        else (b.slotChanges a k)[j]?
      | none => (b.slotChanges a k)[j]? := by
    intro a k j
    have h3 := foldlM_keep
      (fun c : AccessListBuilder => c.accounts[a]?.bind fun r => (r.storageChanges.getD k ∅)[j]?)
      (fun _ _ _ h => recordAccountWrite_slot h a k j) _ b₂ b₃ h₃
    have h2 := hkeep
      (fun c => c.accounts[a]?.bind fun r => (r.storageChanges.getD k ∅)[j]?)
      (fun c a' => record_keep c a' a id (fun r => r.storageChanges.getD k ∅) (fun _ => rfl)
        (by simp) j)
      (fun c a' keys => record_keep c a' a
        (fun r => { r with storageReads := r.storageReads.insertMany keys })
        (fun r => r.storageChanges.getD k ∅) (fun _ => rfl) (by simp) j)
    rw [getElem?_slotChanges, getElem?_slotChanges, hb', storageWrites_slot, hP₃.1,
      startStorage_eq hP₃.2]
    rw [h3, h2]
  refine ⟨fun a => ?_, fun a => ?_, fun a => ?_, fun a k => ?_⟩
  · -- The balance.
    rw [hidx.1, startAccount_eq hidx.2]
    have hdata : ∀ j, (b'.balances a)[j]? =
        b₃.accounts[a]?.bind fun r => r.balanceChanges[j]? := fun j => by
      unfold balances
      rw [getElem?_field]
      exact (hacc (fun r => r.balanceChanges) rfl (fun _ _ _ => rfl) a j).1
    have hold : ∀ j, (b₂.accounts[a]?.bind fun r => r.balanceChanges[j]?) =
        (b.balances a)[j]? := fun j => by
      unfold balances
      rw [getElem?_field]
      exact (hacc (fun r => r.balanceChanges) rfl (fun _ _ _ => rfl) a j).2
    have hpoint := accountWrites_point hP₂ h₃ (fun r => r.balanceChanges)
      (fun a w => if (b.startAccount a).balance ≠ (w.getD EMPTY_ACCOUNT).balance then
        some (w.getD EMPTY_ACCOUNT).balance else none)
      (fun c c' a w hi hs h j => by
        simp only [recordAccountWrite_balance_at h j, hi, startAccount_eq hs]) a
    cases hw : tx.accountWrites[a]? with
    | none =>
      rw [getAccount_incorporate_none hw, hfollow.parent]
      exact (h.balance a).congr fun j => by simp only [hdata, hpoint j, hw, hold]
    | some w =>
      rw [getAccount_incorporate_some hw]
      refine (h.balance a).write _ (fun j hj => ?_) ?_
      · simp only [hdata, hpoint j, hw, hold, hj, ↓reduceIte]
      · simp [hdata, hpoint b.index, hw]
  · -- The nonce.
    rw [hidx.1, startAccount_eq hidx.2]
    have hdata : ∀ j, (b'.nonces a)[j]? =
        b₃.accounts[a]?.bind fun r => r.nonceChanges[j]? := fun j => by
      unfold nonces
      rw [getElem?_field]
      exact (hacc (fun r => r.nonceChanges) rfl (fun _ _ _ => rfl) a j).1
    have hold : ∀ j, (b₂.accounts[a]?.bind fun r => r.nonceChanges[j]?) =
        (b.nonces a)[j]? := fun j => by
      unfold nonces
      rw [getElem?_field]
      exact (hacc (fun r => r.nonceChanges) rfl (fun _ _ _ => rfl) a j).2
    have hpoint := accountWrites_point hP₂ h₃ (fun r => r.nonceChanges)
      (fun a w => if (b.startAccount a).nonce ≠ (w.getD EMPTY_ACCOUNT).nonce then
        some (w.getD EMPTY_ACCOUNT).nonce else none)
      (fun c c' a w hi hs h j => by
        simp only [recordAccountWrite_nonce_at h j, hi, startAccount_eq hs]) a
    cases hw : tx.accountWrites[a]? with
    | none =>
      rw [getAccount_incorporate_none hw, hfollow.parent]
      exact (h.nonce a).congr fun j => by simp only [hdata, hpoint j, hw, hold]
    | some w =>
      rw [getAccount_incorporate_some hw]
      refine (h.nonce a).write _ (fun j hj => ?_) ?_
      · simp only [hdata, hpoint j, hw, hold, hj, ↓reduceIte]
      · simp [hdata, hpoint b.index, hw]
  · -- The code, by its hash.
    rw [hidx.1, startAccount_eq hidx.2]
    have hdata : ∀ j, (b'.codes a)[j]? =
        b₃.accounts[a]?.bind fun r => r.codeChanges[j]? := fun j => by
      unfold codes
      rw [getElem?_field]
      exact (hacc (fun r => r.codeChanges) rfl (fun _ _ _ => rfl) a j).1
    have hold : ∀ j, (b₂.accounts[a]?.bind fun r => r.codeChanges[j]?) =
        (b.codes a)[j]? := fun j => by
      unfold codes
      rw [getElem?_field]
      exact (hacc (fun r => r.codeChanges) rfl (fun _ _ _ => rfl) a j).2
    have hpoint := accountWrites_point hP₂ h₃ (fun r => r.codeChanges)
      (fun a w => if (b.startAccount a).codeHash ≠ (w.getD EMPTY_ACCOUNT).codeHash then
        (tx.getCode (w.getD EMPTY_ACCOUNT).codeHash).toOption else none)
      (fun c c' a w hi hs h j => by
        simp only [recordAccountWrite_code_at h j, hi, startAccount_eq hs]) a
    cases hw : tx.accountWrites[a]? with
    | none =>
      rw [getAccount_incorporate_none hw, hfollow.parent]
      exact (h.code a).congr fun j => by simp only [hdata, hpoint j, hw, hold]
    | some w =>
      rw [getAccount_incorporate_some hw]
      refine (h.code a).write _ (fun j hj => ?_) ?_
      · simp only [hdata, hpoint j, hw, hold, hj, ↓reduceIte]
      · simp only [hdata, hpoint b.index, hw, ↓reduceIte]
        by_cases hc : (b.startAccount a).codeHash ≠ (w.getD EMPTY_ACCOUNT).codeHash
        · -- The write ran, so it found the code, whose hash is the new code hash.
          obtain ⟨c, c', hc', hstep⟩ := foldlM_each
            (fun c : AccessListBuilder => c.index = b.index ∧ c.start = b.start)
            (fun _ _ _ hc h => ⟨(recordAccountWrite_index h).1.trans hc.1,
              (recordAccountWrite_index h).2.trans hc.2⟩)
            _ b₂ b₃ hP₂ h₃ (a, w) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hw)
          obtain ⟨code, hcode⟩ := recordAccountWrite_getCode hstep
            (by rw [startAccount_eq hc'.2]; exact hc)
          have hcode' : tx.getCode (w.getD EMPTY_ACCOUNT).codeHash = .ok code := hcode
          rw [hcode']
          -- The two conditions agree; the hash type differs only by its name.
          split <;> split <;>
            first
            | exact congrArg some (hfollow.code a w code hw hcode')
            | exact absurd hc ‹_›
        · simp only [hc, ↓reduceIte, Option.map_none]
          split
          · exact absurd ‹_› hc
          · rfl
  · -- The word at a key.
    rw [hidx.1, startStorage_eq hidx.2]
    have hnow : (TransactionState.ofBlock tx.incorporateTxIntoBlock.parent).getStorage a k =
        tx.getStorage a k := TransactionState.getStorage_incorporateTxIntoBlock tx a k
    cases hs : tx.storageWrites.slot a k with
    | none =>
      rw [hnow, hfollow.storage a k hs]
      exact (h.storage a k).congr fun j => by simp only [hslot, hs]
    | some v =>
      have hv : tx.getStorage a k = v := by
        unfold TransactionState.getStorage
        rw [hs]
      rw [hnow, hv]
      refine (h.storage a k).write v (fun j hj => ?_) ?_
      · simp only [hslot, hs, hj, ↓reduceIte]
      · simp [hslot, hs]

/-! ## The list -/

/-- A map with no entry lists nothing. -/
private theorem toList_empty {α : Type} : (∅ : Std.ExtTreeMap UInt32 α).toList = [] :=
  Std.ExtTreeMap.toList_eq_nil_iff.mpr rfl

/-- The entry of an account in the built list comes from its record, if it has one. -/
private theorem entry?_build (b : AccessListBuilder) (address : Address) :
    b.build.entry? address = b.accounts[address]?.map (AccountRecord.toChanges address) := by
  have hmem : ∀ e, e ∈ b.build ↔
      ∃ (a : Address) (r : AccountRecord), b.accounts[a]? = some r ∧ r.toChanges a = e := by
    intro e
    simp [build, List.mem_mergeSort, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
  cases hr : b.accounts[address]? with
  | none =>
    simp only [Option.map_none, BlockAccessList.entry?]
    rw [List.find?_eq_none]
    intro e he heq
    obtain ⟨a, r, ha, rfl⟩ := (hmem e).mp he
    replace heq : a = address := of_decide_eq_true heq
    subst heq
    simp_all
  | some r =>
    simp only [Option.map_some, BlockAccessList.entry?]
    cases hf : b.build.find? (·.address = address) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simp [AccountRecord.toChanges])
        (hf _ ((hmem _).mpr ⟨address, r, hr, rfl⟩))
    | some e =>
      have hp := List.find?_some hf
      obtain ⟨a, r', ha, rfl⟩ := (hmem e).mp (List.mem_of_find?_eq_some hf)
      replace hp : a = address := of_decide_eq_true hp
      subst hp
      rw [hr] at ha
      cases ha
      rfl

/-- The changes of the slot of a key in the entry of a record are the changes of that key. -/
private theorem storage_find (r : AccountRecord) (address : Address) (key : Bytes32) :
    (((r.toChanges address).storageChanges.find? (·.slot = U256.fromBeBytes key)).bind
        (·.changes.getLast?)).map (·.value) =
      ((r.storageChanges.getD key ∅).toList.getLast?).map (·.2) := by
  cases hf : (r.toChanges address).storageChanges.find? (·.slot = U256.fromBeBytes key) with
  | some s =>
    have hp := List.find?_some hf
    have hs := List.mem_of_find?_eq_some hf
    simp only [AccountRecord.toChanges] at hs
    obtain ⟨⟨k, vs⟩, hmem, rfl⟩ := List.mem_map.mp (List.mem_mergeSort.mp hs)
    obtain ⟨hmem, -⟩ := List.mem_filter.mp hmem
    simp only [decide_eq_true_eq] at hp
    have hk := U256.fromBeBytes_injective hp
    subst hk
    rw [Std.ExtTreeMap.getD_eq_getD_getElem?,
      Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem]
    simp only [Option.bind_some, Option.getD_some, List.getLast?_map, Option.map_map]
    rfl
  | none =>
    rw [List.find?_eq_none] at hf
    simp only [Option.bind_none, Option.map_none, Std.ExtTreeMap.getD_eq_getD_getElem?]
    cases hk : r.storageChanges[key]? with
    | none => simp [toList_empty]
    | some vs =>
      cases he : vs.isEmpty
      · refine absurd (by simp) (hf ⟨U256.fromBeBytes key,
          vs.toList.map fun (index, value) => ⟨index, value⟩⟩ ?_)
        simp only [AccountRecord.toChanges]
        refine List.mem_mergeSort.mpr (List.mem_map.mpr ⟨(key, vs), ?_, rfl⟩)
        exact List.mem_filter.mpr
          ⟨Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hk, by simp [he]⟩
      · simp [Std.ExtTreeMap.isEmpty_iff.mp he, toList_empty]

/-- The list of a builder that follows the block gives each field as it is now.

A field whose list entry has no change is as it was in `base`.

The nonce is in 64 bits, as the list holds it. -/
theorem Tracks.build {b : AccessListBuilder} {base now : BlockState} (h : b.Tracks base now)
    (address : Address) :
    ((TransactionState.ofBlock now).getAccount address).balance =
        b.build.balanceAfter address ((TransactionState.ofBlock base).getAccount address).balance ∧
      UInt64.ofNat ((TransactionState.ofBlock now).getAccount address).nonce =
        b.build.nonceAfter address
          (UInt64.ofNat ((TransactionState.ofBlock base).getAccount address).nonce) ∧
      ((TransactionState.ofBlock now).getAccount address).codeHash =
        b.build.codeHashAfter address
          ((TransactionState.ofBlock base).getAccount address).codeHash ∧
      ∀ key, (TransactionState.ofBlock now).getStorage address key =
        b.build.storageAfter address key
          ((TransactionState.ofBlock base).getStorage address key) := by
  refine ⟨?_, ?_, ?_, fun key => ?_⟩
  · rw [← (h.balance address).lastOr_eq]
    simp only [BlockAccessList.balanceAfter, entry?_build, balances, lastOr]
    cases b.accounts[address]? <;>
      simp [AccountRecord.toChanges, List.getLast?_map, toList_empty] <;>
      rfl
  · rw [← (h.nonce address).lastOr_eq]
    simp only [BlockAccessList.nonceAfter, entry?_build, nonces, lastOr]
    cases b.accounts[address]? with
    | none => simp [toList_empty]
    | some r =>
      simp only [Option.map_some, Option.getD_some, Option.bind_some, AccountRecord.toChanges,
        List.getLast?_map, Option.map_map]
      cases r.nonceChanges.toList.getLast? <;> rfl
  · rw [← (h.code address).lastOr_eq]
    simp only [BlockAccessList.codeHashAfter, entry?_build, codes, lastOr]
    cases b.accounts[address]? <;>
      simp [AccountRecord.toChanges, List.getLast?_map, toList_empty] <;>
      rfl
  · rw [← (h.storage address key).lastOr_eq]
    simp only [BlockAccessList.storageAfter, entry?_build, slotChanges, lastOr]
    cases b.accounts[address]? with
    | none => simp [toList_empty]
    | some r =>
      simp only [Option.map_some, Option.bind_some]
      rw [storage_find, Std.ExtTreeMap.getD_eq_getD_getElem?]
      cases (r.storageChanges[key]?.getD ∅).toList.getLast? <;> rfl

end AccessListBuilder

end EthLib.Execution.Blocks

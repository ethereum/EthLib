module

public import EthLib.Execution.Proofs.Blocks.AccessListBuilder
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the builder follows the last value of each field

A field is the balance, the nonce or the code of an account, or a word of its storage.

The last change of each field in a built list, or its value before the body, is its present value.

This holds for every call that meets three conditions, which the builder cannot check itself.

The list keeps code, not code hashes, so the code hash is the Keccak-256 hash of the last code.

The list keeps a nonce in 64 bits, so the nonce is compared in 64 bits.

A nonce is below 2^64 by [EIP-2681][eip2681], so this loses nothing.

Source: [EIP-7928, Recording Semantics by Change Type][eip7928].

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#recording-semantics-by-change-type
[eip2681]: https://eips.ethereum.org/EIPS/eip-2681#specification
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State (Account BlockState EMPTY_ACCOUNT TransactionState)
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-! ## The values that a list gives -/

namespace BlockAccessList

/-! These read a list in its own order.

On a list that passes the checks of EIP-7928, an account has one entry.

Its changes are sorted by position there, so the last change is the one at the greatest position.
-/

/-- The first entry of an account in the list, if it has one. -/
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

These are assumptions on the call, which the builder cannot check itself.

The call ran on `block`.

A key that the call did not write reads as it did in `block`, so a wipe hides no word.

This excludes a creation at an address with storage but no nonce and no code.

EthLib wipes that storage, since it does not apply [EIP-7610][eip7610].

It also excludes a change that deletes an empty account with storage, which wipes it too.

The code that the call reads for an account it wrote has the code hash of that account.

A code map is a plain map, so nothing else ties the code that it gives to its hash.

[eip7610]: https://eips.ethereum.org/EIPS/eip-7610#specification -/
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

/-- The changes of a field follow it, read through `view`, up to the position `index`.

The field is `base` before the body, `start` when the position began, and `now` at present.

No change is past the position.

The last change before the position, or `base`, is `start`.

The position holds a change exactly when the field differs from `start`, and it is `now`. -/
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

/-- A field that the builder follows has its present value as its last change.

With no change, its value before the body is its present value. -/
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

/-- No changes follow a field that kept one value, at any position. -/
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

/-- A builder follows a block state with the same accounts and storage as one it follows. -/
theorem Tracks.congr {b : AccessListBuilder} {base now now' : BlockState}
    (h : b.Tracks base now)
    (hacc : ∀ address, (TransactionState.ofBlock now').getAccount address =
      (TransactionState.ofBlock now).getAccount address)
    (hsto : ∀ address key, (TransactionState.ofBlock now').getStorage address key =
      (TransactionState.ofBlock now).getStorage address key) :
    b.Tracks base now' :=
  ⟨fun a => by rw [hacc a]; exact h.balance a, fun a => by rw [hacc a]; exact h.nonce a,
    fun a => by rw [hacc a]; exact h.code a, fun a k => by rw [hsto a k]; exact h.storage a k⟩

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
  rw [← bind_storageChanges_getD, slotChanges]
  cases b.accounts[address]?.bind fun r => r.storageChanges[key]? <;> simp

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
  · rw [Std.ExtTreeMap.foldl_eq_foldl_toList, Std.ExtTreeSet.foldl_eq_foldl_toList]
    refine List.foldlRecOn _ _ (motive := fun c => g c = g b) ?_
      fun c hc (x : Address × Std.ExtTreeSet Bytes32) _ => (h₂ c x.1 x.2.toList).trans hc
    exact List.foldlRecOn _ _ (motive := fun c => g c = g b) rfl fun c hc x _ => (h₁ c x).trans hc
  · simp only [Std.ExtTreeMap.foldl_eq_foldl_toList]

/-- The storage writes of a call keep every value that each storage write keeps. -/
private theorem storageWrites_keep {γ : Type} (tx : TransactionState) (c : AccessListBuilder)
    (g : AccessListBuilder → γ) (hg : ∀ d a k v, g (d.recordStorageWrite a k v) = g d) :
    g (tx.storageWrites.toList.foldl
      (fun c x => x.2.toList.foldl (fun c y => c.recordStorageWrite x.1 y.1 y.2) c) c) = g c :=
  List.foldlRecOn _ _ (motive := fun d => g d = g c) rfl fun d hd x _ =>
    (List.foldlRecOn _ _ (motive := fun e => g e = g d) rfl fun e he y _ =>
      (hg e x.1 y.1 y.2).trans he).trans hd

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
  have hstep : ∀ d (address : Address) (y : Bytes32 × U256), P d →
      P (d.recordStorageWrite address y.1 y.2) := fun d address y hd =>
    ⟨(recordStorageWrite_index d address y.1 y.2).1.trans hd.1,
      (recordStorageWrite_index d address y.1 y.2).2.trans hd.2⟩
  have inner : ∀ slots : Std.ExtTreeMap Bytes32 U256, ∀ d, P d →
      ((∀ y ∈ slots.toList, y.1 ≠ k) →
        g (slots.toList.foldl (fun c y => c.recordStorageWrite a y.1 y.2) d) = g d) ∧
      (∀ y ∈ slots.toList, y.1 = k →
        g (slots.toList.foldl (fun c y => c.recordStorageWrite a y.1 y.2) d) = H y (g d)) := by
    intro slots d hd
    refine (foldl_pointwise (fun c y => c.recordStorageWrite a y.1 y.2) P g Prod.fst k H
      (Std.ExtTreeMap.map_fst_toList_eq_keys (t := slots) ▸ slots.nodup_keys)
      (fun y _ e he => hstep e a y he) (fun y _ e _ hne => ?_) (fun y _ e he hy => ?_) hd).2
    · simp only [g]
      rw [recordStorageWrite_slot, ite_eq_right_of_eq_false _ _ (eq_false fun h => hne h.2.1.symm)]
    · simp only [g, H]
      rw [recordStorageWrite_slot, he.1, hy]
      unfold startStorage
      rw [he.2]
      simp
  have outer := foldl_pointwise
    (fun c x => x.2.toList.foldl (fun c y => c.recordStorageWrite x.1 y.1 y.2) c) P g Prod.fst a
    (fun x old => match x.2[k]? with
      | some v => H (k, v) old
      | none => old)
    (Std.ExtTreeMap.map_fst_toList_eq_keys (t := tx.storageWrites) ▸ tx.storageWrites.nodup_keys)
    (fun x _ d hd => List.foldlRecOn _ _ hd fun e he y _ => hstep e x.1 y he)
    (fun x _ d _ hne => List.foldlRecOn _ _ (motive := fun e => g e = g d) rfl fun e he y _ => by
      simp only [g] at he ⊢
      rw [recordStorageWrite_slot,
        ite_eq_right_of_eq_false _ _ (eq_false fun h => hne h.1.symm)]
      exact he)
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
    (b := c) ⟨rfl, rfl⟩
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
  have point := foldlM_ok_pointwise (fun c => c.index = b.index ∧ c.start = b.start)
    (fun c => c.accounts[a]?.bind fun r => (get r)[j]?) Prod.fst a
    (fun x old => if j = b.index then V a x.2 else old)
    (Std.ExtTreeMap.map_fst_toList_eq_keys (t := tx.accountWrites) ▸ tx.accountWrites.nodup_keys)
    (fun _ _ c c' hc h => ⟨(recordAccountWrite_index h).1.trans hc.1,
      (recordAccountWrite_index h).2.trans hc.2⟩)
    (fun _ _ c c' _ h hne => by simp only [recordAccountWrite_ne h hne])
    (fun x _ c c' hc h hx => by
      obtain ⟨x, w⟩ := x
      dsimp only at hx h ⊢
      subst hx
      exact hat c c' x w hc.1 hc.2 h j)
    hP₂ h₃
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

/-- An account write keeps the position of the builder and its start. -/
private theorem accountWrite_index {b c c' : AccessListBuilder} {tx : TransactionState}
    {x : Address × Option Account} (hc : c.index = b.index ∧ c.start = b.start)
    (h : c.recordAccountWrite tx x.1 x.2 = .ok c') : c'.index = b.index ∧ c'.start = b.start :=
  ⟨(recordAccountWrite_index h).1.trans hc.1, (recordAccountWrite_index h).2.trans hc.2⟩

/-- Recording a call keeps the position of the builder and its start. -/
theorem recordTransaction_index {b b' : AccessListBuilder} {tx : TransactionState}
    (h : b.recordTransaction tx = .ok b') : b'.index = b.index ∧ b'.start = b.start := by
  obtain ⟨b₂, b₃, hkeep, h₃, hb'⟩ := recordTransaction_eq h
  have hP₂ : b₂.index = b.index ∧ b₂.start = b.start :=
    Prod.mk.inj (hkeep (fun c => (c.index, c.start)) (fun _ _ => rfl) (fun _ _ _ => rfl))
  have hP₃ : b₃.index = b.index ∧ b₃.start = b.start :=
    foldlM_ok_invariant (fun c : AccessListBuilder => c.index = b.index ∧ c.start = b.start)
      (fun _ _ _ => accountWrite_index) hP₂ h₃
  have := storageWrites_keep tx b₃ (fun c => (c.index, c.start))
    (fun d a k v => Prod.ext (recordStorageWrite_index d a k v).1
      (recordStorageWrite_index d a k v).2)
  rw [← hb'] at this
  exact ⟨(Prod.mk.inj this).1.trans hP₃.1, (Prod.mk.inj this).2.trans hP₃.2⟩

/-- A builder that records a call it can follow then follows the block state after the call. -/
theorem Tracks.recordTransaction {b b' : AccessListBuilder} {base block : BlockState}
    {tx : TransactionState} (h : b.Tracks base block) (hfollow : Followable block tx)
    (hrecord : b.recordTransaction tx = .ok b') :
    b'.Tracks base tx.incorporateTxIntoBlock.parent := by
  obtain ⟨b₂, b₃, hkeep, h₃, hb'⟩ := recordTransaction_eq hrecord
  -- The position and its start stay.
  have hP₂ : b₂.index = b.index ∧ b₂.start = b.start :=
    Prod.mk.inj (hkeep (fun c => (c.index, c.start)) (fun _ _ => rfl) (fun _ _ _ => rfl))
  have hstepP : ∀ (c : AccessListBuilder) (x : Address × Option Account) c',
      c.index = b.index ∧ c.start = b.start → c.recordAccountWrite tx x.1 x.2 = .ok c' →
      c'.index = b.index ∧ c'.start = b.start := fun _ _ _ => accountWrite_index
  have hP₃ : b₃.index = b.index ∧ b₃.start = b.start :=
    foldlM_ok_invariant (fun c : AccessListBuilder => c.index = b.index ∧ c.start = b.start)
      hstepP hP₂ h₃
  have hidx := recordTransaction_index hrecord
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
        (fun c a' => record_id_at c a' a get hempty j)
        (fun c a' _ => record_at_of_get c a' a _ get (fun r => hget r r.storageChanges _) hempty j)
  -- Only the storage writes change the storage changes.
  have hslot : ∀ (a : Address) (k : Bytes32) (j : UInt32), (b'.slotChanges a k)[j]? =
      match tx.storageWrites.slot a k with
      | some v => if j = b.index then (if b.startStorage a k ≠ v then some v else none)
        else (b.slotChanges a k)[j]?
      | none => (b.slotChanges a k)[j]? := by
    intro a k j
    have h3 := foldlM_ok_invariant
      (fun c : AccessListBuilder => (c.accounts[a]?.bind fun r =>
        (r.storageChanges.getD k ∅)[j]?) = b₂.accounts[a]?.bind fun r =>
          (r.storageChanges.getD k ∅)[j]?)
      (fun _ _ _ hc h => (recordAccountWrite_slot h a k j).trans hc) rfl h₃
    have h2 := hkeep
      (fun c => c.accounts[a]?.bind fun r => (r.storageChanges.getD k ∅)[j]?)
      (fun c a' => record_id_at c a' a (fun r => r.storageChanges.getD k ∅) (by simp) j)
      (fun c a' keys => record_at_of_get c a' a
        (fun r => { r with storageReads := r.storageReads.insertMany keys })
        (fun r => r.storageChanges.getD k ∅) (fun _ => rfl) (by simp) j)
    rw [getElem?_slotChanges, getElem?_slotChanges, hb', storageWrites_slot, hP₃.1]
    unfold startStorage
    rw [hP₃.2, h3, h2]
  -- A field of an account follows the block, given what the account writes record for it.
  have hfield : ∀ {β γ : Type} [DecidableEq γ] (view : β → γ)
      (get : AccountRecord → Std.ExtTreeMap UInt32 β) (F : Account → γ)
      (V : Address → Option Account → Option β) (a : Address) (old : γ),
      get {} = ∅ → (∀ r s c, get { r with storageChanges := s, storageReads := c } = get r) →
      (∀ (c c' : AccessListBuilder) (a : Address) (w : Option Account), c.index = b.index →
        c.start = b.start → c.recordAccountWrite tx a w = .ok c' →
        ∀ j, (c'.accounts[a]?.bind fun r => (get r)[j]?) =
          if j = b.index then V a w else c.accounts[a]?.bind fun r => (get r)[j]?) →
      (∀ w, tx.accountWrites[a]? = some w → (V a w).map view =
        if F (b.startAccount a) ≠ F (w.getD EMPTY_ACCOUNT) then some (F (w.getD EMPTY_ACCOUNT))
        else none) →
      FieldTracks view ((b.accounts[a]?.map get).getD ∅) b.index old (F (b.startAccount a))
        (F ((TransactionState.ofBlock block).getAccount a)) →
      FieldTracks view ((b'.accounts[a]?.map get).getD ∅) b.index old (F (b.startAccount a))
        (F ((TransactionState.ofBlock tx.incorporateTxIntoBlock.parent).getAccount a)) := by
    intro β γ _ view get F V a old hempty hget hat hV ht
    have hdata : ∀ j, ((b'.accounts[a]?.map get).getD ∅)[j]? =
        b₃.accounts[a]?.bind fun r => (get r)[j]? := fun j => by
      rw [getElem?_field]
      exact (hacc get hempty hget a j).1
    have hold : ∀ j, (b₂.accounts[a]?.bind fun r => (get r)[j]?) =
        ((b.accounts[a]?.map get).getD ∅)[j]? := fun j => by
      rw [getElem?_field]
      exact (hacc get hempty hget a j).2
    have hpoint := accountWrites_point hP₂ h₃ get V hat a
    cases hw : tx.accountWrites[a]? with
    | none =>
      rw [getAccount_incorporate_none hw, hfollow.parent]
      exact ht.congr fun j => by simp only [hdata, hpoint j, hw, hold]
    | some w =>
      rw [getAccount_incorporate_some hw]
      refine ht.write _ (fun j hj => ?_) ?_
      · simp only [hdata, hpoint j, hw, hold, hj, ↓reduceIte]
      · simp only [hdata, hpoint b.index, hw, ↓reduceIte]
        exact hV w hw
  refine ⟨fun a => ?_, fun a => ?_, fun a => ?_, fun a k => ?_⟩
  · -- The balance.
    simp only [hidx.1, startAccount, hidx.2]
    refine hfield id (·.balanceChanges) (·.balance)
      (fun a w => if (b.startAccount a).balance ≠ (w.getD EMPTY_ACCOUNT).balance then
        some (w.getD EMPTY_ACCOUNT).balance else none) a _ rfl (fun _ _ _ => rfl)
      (fun c c' a w hi hs h j => ?_) (fun _ _ => by simp) (h.balance a)
    simp only [recordAccountWrite_balance_at h j, hi]
    unfold startAccount
    rw [hs]
  · -- The nonce.
    simp only [hidx.1, startAccount, hidx.2]
    refine hfield id (·.nonceChanges) (·.nonce)
      (fun a w => if (b.startAccount a).nonce ≠ (w.getD EMPTY_ACCOUNT).nonce then
        some (w.getD EMPTY_ACCOUNT).nonce else none) a _ rfl (fun _ _ _ => rfl)
      (fun c c' a w hi hs h j => ?_) (fun _ _ => by simp) (h.nonce a)
    simp only [recordAccountWrite_nonce_at h j, hi]
    unfold startAccount
    rw [hs]
  · -- The code, by its hash.
    simp only [hidx.1, startAccount, hidx.2]
    refine hfield keccak256 (·.codeChanges) (·.codeHash)
      (fun a w => if (b.startAccount a).codeHash ≠ (w.getD EMPTY_ACCOUNT).codeHash then
        (tx.getCode (w.getD EMPTY_ACCOUNT).codeHash).toOption else none) a _ rfl
      (fun _ _ _ => rfl) (fun c c' a w hi hs h j => ?_) (fun w hw => ?_) (h.code a)
    · simp only [recordAccountWrite_code_at h j, hi]
      unfold startAccount
      rw [hs]
    · by_cases hc : (b.startAccount a).codeHash ≠ (w.getD EMPTY_ACCOUNT).codeHash
      · -- The write ran, so it found the code, whose hash is the new code hash.
        obtain ⟨i, hi, hx⟩ :=
          List.getElem_of_mem (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hw)
        obtain ⟨c, c', hc₁, hstep, -⟩ := (foldlM_ok_steps (fun _ _ => True)
          (fun _ => trivial) (fun _ _ => trivial) (fun _ _ _ _ => trivial) h₃).2 i hi
        have hc' := foldlM_ok_invariant _ hstepP hP₂ hc₁
        simp only [hx] at hstep
        obtain ⟨code, hcode⟩ := recordAccountWrite_getCode hstep
          (by simpa only [startAccount, hc'.2] using hc)
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
    simp only [hidx.1, startStorage, hidx.2]
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

/-- The list of a builder that follows the block gives each balance as it is now.

An account with no balance change in the list keeps its balance from `base`. -/
theorem Tracks.balance_build {b : AccessListBuilder} {base now : BlockState}
    (h : b.Tracks base now) (address : Address) :
    ((TransactionState.ofBlock now).getAccount address).balance =
      b.build.balanceAfter address
        ((TransactionState.ofBlock base).getAccount address).balance := by
  rw [← (h.balance address).lastOr_eq]
  simp only [BlockAccessList.balanceAfter, entry?_build, balances, lastOr]
  cases b.accounts[address]? <;>
    simp [AccountRecord.toChanges, List.getLast?_map, toList_empty] <;>
    rfl

/-- The list of a builder that follows the block gives each nonce as it is now.

An account with no nonce change in the list keeps its nonce from `base`.

The nonce is in 64 bits, as the list holds it. -/
theorem Tracks.nonce_build {b : AccessListBuilder} {base now : BlockState}
    (h : b.Tracks base now) (address : Address) :
    UInt64.ofNat ((TransactionState.ofBlock now).getAccount address).nonce =
      b.build.nonceAfter address
        (UInt64.ofNat ((TransactionState.ofBlock base).getAccount address).nonce) := by
  rw [← (h.nonce address).lastOr_eq]
  simp only [BlockAccessList.nonceAfter, entry?_build, nonces, lastOr]
  cases b.accounts[address]? with
  | none => simp [toList_empty]
  | some r =>
    simp only [Option.map_some, Option.getD_some, Option.bind_some, AccountRecord.toChanges,
      List.getLast?_map, Option.map_map]
    cases r.nonceChanges.toList.getLast? <;> rfl

/-- The list of a builder that follows the block gives each code hash as it is now.

It is the hash of the last code in the list.

An account with no code change in the list keeps its code hash from `base`. -/
theorem Tracks.codeHash_build {b : AccessListBuilder} {base now : BlockState}
    (h : b.Tracks base now) (address : Address) :
    ((TransactionState.ofBlock now).getAccount address).codeHash =
      b.build.codeHashAfter address
        ((TransactionState.ofBlock base).getAccount address).codeHash := by
  rw [← (h.code address).lastOr_eq]
  simp only [BlockAccessList.codeHashAfter, entry?_build, codes, lastOr]
  cases b.accounts[address]? <;>
    simp [AccountRecord.toChanges, List.getLast?_map, toList_empty] <;>
    rfl

/-- The list of a builder that follows the block gives each word of storage as it is now.

A key with no change in the list keeps its word from `base`. -/
theorem Tracks.storage_build {b : AccessListBuilder} {base now : BlockState}
    (h : b.Tracks base now) (address : Address) (key : Bytes32) :
    (TransactionState.ofBlock now).getStorage address key =
      b.build.storageAfter address key
        ((TransactionState.ofBlock base).getStorage address key) := by
  rw [← (h.storage address key).lastOr_eq]
  simp only [BlockAccessList.storageAfter, entry?_build, slotChanges, lastOr]
  cases b.accounts[address]? with
  | none => simp [toList_empty]
  | some r =>
    simp only [Option.map_some, Option.bind_some]
    rw [storage_find, Std.ExtTreeMap.getD_eq_getD_getElem?]
    cases (r.storageChanges[key]?.getD ∅).toList.getLast? <;> rfl

end AccessListBuilder

end EthLib.Execution.Blocks

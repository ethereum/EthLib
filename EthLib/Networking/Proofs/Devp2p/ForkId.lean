module

public import EthLib.Cryptography.Proofs.Hash.Crc
public import EthLib.Networking.Devp2p.ForkId
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the fork identifier

An identifier reads back from its RLP item.

Each fork continues the CRC from the hash before it, as a node updates its hash fork by fork.

A node accepts its own identifier.

It accepts the identifier of a peer at an earlier or a later head of its chain.

It refuses a peer at its fork that announces a fork it has passed, and a hash it never had.

A head has passed a next fork exactly when the fork is not 0 and the head has reached it.

The head reaches it when it is at most the block number.

It also reaches it when it is above the timestamp threshold and at most the timestamp.
-/

@[expose] public section

namespace EthLib.Networking.Devp2p

open EthLib.Base
open EthLib.Cryptography.Hash
open EthLib.Serialization.Rlp

instance : LawfulCodec ForkId where
  ofItem_toItem id := by
    show ForkId.ofItem (ForkId.toItem id) = _
    simp [ForkId.ofItem, ForkId.toItem, Item.fields, Item.toItems, Item.field_toItem, bind,
      Except.bind, pure, Except.pure]
  toItem_of_ofItem {item id} h := by
    change ForkId.ofItem item = .ok id at h
    unfold ForkId.ofItem at h
    obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp h
    rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    obtain ⟨x, rfl, h1⟩ := Item.field_bind_eq_ok.mp hrest
    obtain ⟨y, rfl, h2⟩ := Item.field_bind_eq_ok.mp h1
    cases h2
    rfl

/-- Two errors with one code come from one constructor. -/
theorem ForkIdError.code_injective : Function.Injective ForkIdError.code := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [ForkIdError.code] at h)

/-- One more fork continues the CRC of the hash before it with the 8 bytes of the fork. -/
theorem Schedule.remainder_checksumInput_append (g : Hash32) (forks : List Activation)
    (a : Activation) :
    Crc.remainder Crc32.generator (Schedule.checksumInput g (forks ++ [a]))
      = (natToBytes 8 (activationValue a)).foldl (Crc.shiftByte Crc32.generator)
          (Crc.remainder Crc32.generator (Schedule.checksumInput g forks)) := by
  have : Schedule.checksumInput g (forks ++ [a])
      = Schedule.checksumInput g forks ++ ⟨(natToBytes 8 (activationValue a)).toArray⟩ := by
    simp [Schedule.checksumInput, ByteArray.ext_iff, ByteArray.data_append]
  rw [this, Crc.remainder_append]

/-! ## The passed forks -/

/-- A prefix that a predicate keeps is the first elements, as many as it keeps. -/
theorem _root_.List.takeWhile_eq_take {α : Type} (p : α → Bool) :
    ∀ l : List α, l.takeWhile p = l.take (l.takeWhile p).length
  | [] => rfl
  | a :: l => by
    cases h : p a
    · simp [h]
    · simp only [List.takeWhile_cons, h, ↓reduceIte, List.length_cons, List.take_succ_cons]
      exact congrArg _ (List.takeWhile_eq_take p l)

/-- What a predicate drops from the front is the rest after the prefix it keeps. -/
theorem _root_.List.dropWhile_eq_drop {α : Type} (p : α → Bool) :
    ∀ l : List α, l.dropWhile p = l.drop (l.takeWhile p).length
  | [] => rfl
  | a :: l => by
    cases h : p a
    · simp [h]
    · simp only [List.takeWhile_cons, List.dropWhile_cons, h, ↓reduceIte, List.length_cons,
        List.drop_succ_cons]
      exact List.dropWhile_eq_drop p l

/-- In a list without repeats, the first index of the element at `j` is `j`. -/
theorem _root_.List.findIdx?_eq_of_nodup {α : Type} [DecidableEq α] {l : List α}
    (hl : l.Nodup) {j : Nat} (hj : j < l.length) : l.findIdx? (· = l[j]) = some j := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hj, by simp, fun k hk => ?_⟩
  simp only [decide_eq_true_eq]
  intro h
  have := hl.eq_of_getElem_eq (by omega) hj h
  omega

namespace Schedule

variable (s : Schedule) (number timestamp : Nat)

/-- A head never passes more forks than the chain has. -/
theorem length_passed_le : (s.passed number timestamp).length ≤ s.forks.length :=
  (List.takeWhile_sublist _).length_le

/-- The list of hashes has one more element than the chain has forks. -/
theorem length_checksums : s.checksums.length = s.forks.length + 1 := by
  simp [checksums]

/-- The hash after `k` forks, for each `k` up to the number of forks. -/
theorem checksums_getElem? {k : Nat} (hk : k ≤ s.forks.length) :
    s.checksums[k]? = some (checksum s.genesisHash (s.forks.take k)) := by
  simp [checksums, Nat.lt_succ_of_le hk]

/-- The hash of a node is the hash after as many forks as it has passed. -/
theorem checksums_passed :
    s.checksums[(s.passed number timestamp).length]? = some (s.forkId number timestamp).hash := by
  rw [checksums_getElem? s (length_passed_le s number timestamp)]
  simp only [forkId, passed, ← List.takeWhile_eq_take]

/-- `FORK_NEXT` is the first fork that the head has not reached, or 0. -/
theorem forkId_next :
    (s.forkId number timestamp).next =
      match s.forks[(s.passed number timestamp).length]? with
      | none => 0
      | some a => UInt64.ofNat (activationValue a) := by
  simp only [forkId, passed, List.dropWhile_eq_drop]
  cases h : s.forks[(s.forks.takeWhile (·.reached number timestamp)).length]? <;>
    cases hd : s.forks.drop (s.forks.takeWhile (·.reached number timestamp)).length <;>
    simp_all [← List.head?_drop]

/-- The first fork after the passed ones is a fork that the head has not reached. -/
theorem not_reached_of_next {a : Activation}
    (h : s.forks[(s.passed number timestamp).length]? = some a) :
    a.reached number timestamp = false ∧ a ∈ s.forks := by
  have hd := List.head?_dropWhile_not (·.reached number timestamp) s.forks
  rw [List.dropWhile_eq_drop, List.head?_drop] at hd
  simp only [passed] at h
  rw [h] at hd
  exact ⟨hd, List.mem_of_getElem? h⟩

/-- A fork of the chain is a fork block or a fork timestamp. -/
theorem mem_forks {a : Activation} (h : a ∈ s.forks) :
    (∃ b ∈ s.blocks, a = .block b) ∨ (∃ t ∈ s.times, a = .time t) := by
  simp only [forks, List.mem_append, List.mem_map] at h
  rcases h with ⟨b, hb, rfl⟩ | ⟨t, ht, rfl⟩
  · exact .inl ⟨b, hb, rfl⟩
  · exact .inr ⟨t, ht, rfl⟩

/-! ## Validation -/

/-- A head has passed a next fork exactly when the fork is not 0 and the head has reached it.

The head reaches it when it is at most the block number.

It also reaches it when it is above the timestamp threshold and at most the timestamp. -/
theorem passedNext_iff {number timestamp next : Nat} :
    passedNext number timestamp next = true ↔
      0 < next ∧ (next ≤ number ∨ (TIMESTAMP_THRESHOLD < next ∧ next ≤ timestamp)) := by
  simp [passedNext]

/-- A next fork of 0 announces nothing, so no head has passed it. -/
theorem passedNext_zero (number timestamp : Nat) : passedNext number timestamp 0 = false := by
  simp [passedNext]

/-- Rule 1: at one fork, a node refuses a peer exactly when it has passed the peer's next fork. -/
theorem validate_of_hash_eq {remote : ForkId}
    (h : (s.forkId number timestamp).hash = remote.hash) :
    s.validate number timestamp remote =
      if passedNext number timestamp remote.next.toNat then .error .localIncompatibleOrStale
      else .ok () := by
  simp only [validate, h, ↓reduceIte]
  split <;> rfl

/--
The forks fit rule 1a, which tells a block from a timestamp by its size.

Each fork block is at most the threshold, and each fork timestamp is above it and below 2^64.
-/
def Separated : Prop :=
  (∀ b ∈ s.blocks, b ≤ TIMESTAMP_THRESHOLD) ∧
    ∀ t ∈ s.times, TIMESTAMP_THRESHOLD < t ∧ t < 2 ^ 64

instance : Decidable s.Separated := inferInstanceAs (Decidable (_ ∧ _))

/-- A node accepts its own identifier, when its forks fit rule 1a and its head is a real block. -/
theorem validate_forkId_self (hs : s.Separated) (hn : number ≤ TIMESTAMP_THRESHOLD) :
    s.validate number timestamp (s.forkId number timestamp) = .ok () := by
  rw [validate_of_hash_eq s number timestamp rfl, forkId_next]
  split
  · simp [passedNext]
  · rename_i a ha
    obtain ⟨hr, hmem⟩ := not_reached_of_next s number timestamp ha
    have hT : TIMESTAMP_THRESHOLD < 2 ^ 64 := by decide
    rcases mem_forks s hmem with ⟨b, hb, rfl⟩ | ⟨t, ht, rfl⟩
    · have := hs.1 b hb
      simp only [Activation.reached, decide_eq_false_iff_not, Nat.not_le] at hr
      simp [passedNext, activationValue, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
      omega
    · have := hs.2 t ht
      simp only [Activation.reached, decide_eq_false_iff_not, Nat.not_le] at hr
      simp [passedNext, activationValue, Nat.mod_eq_of_lt this.2]
      omega

/--
Rule 2: a node accepts a peer of its chain whose head is behind its own.

The hashes of the chain must differ, and the forks must be below 2^64.
-/
theorem validate_behind (hnd : s.checksums.Nodup)
    (hfit : ∀ a ∈ s.forks, activationValue a < 2 ^ 64) {number' timestamp' : Nat}
    (hlt : (s.passed number' timestamp').length < (s.passed number timestamp).length) :
    s.validate number timestamp (s.forkId number' timestamp') = .ok () := by
  have hi := length_passed_le s number timestamp
  have hlen := length_checksums s
  obtain ⟨hi', hci⟩ := List.getElem?_eq_some_iff.mp (checksums_passed s number timestamp)
  obtain ⟨hj', hcj⟩ := List.getElem?_eq_some_iff.mp (checksums_passed s number' timestamp')
  have hne : (s.forkId number timestamp).hash ≠ (s.forkId number' timestamp').hash := by
    rw [← hci, ← hcj]
    intro h
    have := hnd.eq_of_getElem_eq (by omega) (by omega) h
    omega
  have hfind : (s.checksums.take (s.passed number timestamp).length).findIdx?
      (· = (s.forkId number' timestamp').hash) = some (s.passed number' timestamp').length := by
    have hj : (s.passed number' timestamp').length
        < (s.checksums.take (s.passed number timestamp).length).length := by simp; omega
    have := List.findIdx?_eq_of_nodup (hnd.sublist (List.take_sublist _ _)) hj
    rwa [List.getElem_take, hcj] at this
  have hfj : s.forks[(s.passed number' timestamp').length]?
      = some s.forks[(s.passed number' timestamp').length] :=
    List.getElem?_eq_getElem (by omega)
  have hv := hfit _ (List.getElem_mem (l := s.forks) (n := (s.passed number' timestamp').length)
    (by omega))
  simp only [validate, hne, hfind, forkId_next s number' timestamp', hfj, Option.map_some,
    UInt64.toNat_ofNat', Nat.mod_eq_of_lt hv, ↓reduceIte]
  rfl

/-- Rule 3: a node accepts a peer of its chain whose head is ahead of its own.

The hashes of the chain must differ. -/
theorem validate_ahead (hnd : s.checksums.Nodup) {number' timestamp' : Nat}
    (hlt : (s.passed number timestamp).length < (s.passed number' timestamp').length) :
    s.validate number timestamp (s.forkId number' timestamp') = .ok () := by
  obtain ⟨hi', hci⟩ := List.getElem?_eq_some_iff.mp (checksums_passed s number timestamp)
  obtain ⟨hj', hcj⟩ := List.getElem?_eq_some_iff.mp (checksums_passed s number' timestamp')
  have hne : (s.forkId number timestamp).hash ≠ (s.forkId number' timestamp').hash := by
    rw [← hci, ← hcj]
    intro h
    have := hnd.eq_of_getElem_eq (by omega) (by omega) h
    omega
  have hfind : (s.checksums.take (s.passed number timestamp).length).findIdx?
      (· = (s.forkId number' timestamp').hash) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.getElem_take, decide_eq_false_iff_not, ← hcj]
    have hk' := List.length_take_le (s.passed number timestamp).length s.checksums
    intro h
    have := hnd.eq_of_getElem_eq (by omega) (by omega) h
    omega
  have hmem : (s.forkId number' timestamp').hash
      ∈ s.checksums.drop ((s.passed number timestamp).length + 1) := by
    rw [List.mem_iff_getElem]
    refine ⟨(s.passed number' timestamp').length - ((s.passed number timestamp).length + 1),
      by simp; omega, ?_⟩
    rw [List.getElem_drop, ← hcj]
    congr 1
    omega
  simp [validate, hne, hfind, hmem]
  rfl

/-- Rule 4: a node refuses a hash that it never had. -/
theorem validate_unknown {remote : ForkId} (h : remote.hash ∉ s.checksums) :
    s.validate number timestamp remote = .error .localIncompatibleOrStale := by
  have hne : (s.forkId number timestamp).hash ≠ remote.hash := by
    intro he
    exact h (he ▸ List.mem_of_getElem? (checksums_passed s number timestamp))
  have hfind : (s.checksums.take (s.passed number timestamp).length).findIdx?
      (· = remote.hash) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    simp only [decide_eq_false_iff_not]
    rintro rfl
    exact h (List.mem_of_mem_take hx)
  have hdrop : (s.checksums.drop ((s.passed number timestamp).length + 1)).contains remote.hash
      = false := by
    rw [Bool.eq_false_iff]
    intro hc
    exact h (List.mem_of_mem_drop (List.contains_iff_mem.mp hc))
  simp only [validate, hne, ↓reduceIte, hfind, hdrop, Bool.false_eq_true]
  rfl

/-- A fork block is a block of the configuration other than Paris, or `FORK_NEXT_VALUE`. -/
theorem mem_blocks {b : Nat} (h : b ∈ s.blocks) :
    (∃ f, f ≠ .paris ∧ (f, Activation.block b) ∈ s.config.activations) ∨
      s.mergeForkBlock = some b := by
  simp only [blocks, List.mem_eraseDups, List.mem_mergeSort, List.mem_filter, List.mem_append,
    List.mem_filterMap, Option.mem_toList] at h
  obtain ⟨⟨⟨f, a⟩, ha, he⟩ | hm, -⟩ := h
  · left
    cases a with
    | block n =>
      by_cases hp : f = .paris
      · simp [hp] at he
      · simp only [hp, ↓reduceIte, Option.some.injEq] at he
        subst he
        exact ⟨f, hp, ha⟩
    | time _ => simp at he
  · exact .inr (by simpa [eq_comm] using hm)

/-- A fork timestamp is a timestamp of the configuration after the genesis time. -/
theorem mem_times {t : Nat} (h : t ∈ s.times) :
    (∃ f, (f, Activation.time t) ∈ s.config.activations) ∧ s.genesisTime < t := by
  simp only [times, List.mem_eraseDups, List.mem_mergeSort, List.mem_filter,
    List.mem_filterMap] at h
  obtain ⟨⟨⟨f, a⟩, ha, he⟩, hg⟩ := h
  cases a with
  | block _ => simp at he
  | time n => simp at he; subst he; exact ⟨⟨f, ha⟩, by simpa using hg⟩

/-- The forks of mainnet fit rule 1a. -/
theorem mainnet_separated : mainnet.Separated := by
  constructor
  · intro b hb
    rcases mem_blocks mainnet hb with ⟨f, -, hf⟩ | hm
    · simp only [mainnet, ChainConfig.mainnet, List.mem_cons, Prod.mk.injEq,
        reduceCtorEq, Activation.block.injEq, List.not_mem_nil] at hf
      repeat' (first | (obtain ⟨-, rfl⟩ | hf := hf) | (obtain ⟨-, rfl⟩ := hf))
      all_goals simp_all [TIMESTAMP_THRESHOLD]
    · simp [mainnet] at hm
  · intro t ht
    obtain ⟨⟨f, hf⟩, -⟩ := mem_times mainnet ht
    simp only [mainnet, ChainConfig.mainnet, List.mem_cons, Prod.mk.injEq,
      reduceCtorEq, Activation.time.injEq, List.not_mem_nil, and_false, false_or, or_false] at hf
    rcases hf with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      simp [TIMESTAMP_THRESHOLD]

end Schedule

end EthLib.Networking.Devp2p


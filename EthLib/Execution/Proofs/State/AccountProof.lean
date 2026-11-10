module

public import EthLib.Execution.State.AccountProof
public import EthLib.Execution.Proofs.State.Root
public import EthLib.Execution.Proofs.Trie.Binding
public import EthLib.Execution.Trie.Range

/-!
# Proofs: the check of an answer of `eth_getProof`

Soundness: take a secured trie with distinct keys and the root that the answer is checked against.

If the account check passes, the trie gives the address the account of the answer.

When the check reports the account absent, the trie gives the address no value.

The fields of the answer then fit an address with no account.

Otherwise a search finds a collision between the account proof and the trie's own proof.

Or it finds two keys of the trie with one hash.

The same holds for each slot, against the storage trie.

A slot that the check reports absent also has the word `0` in the answer.

Completeness: the proof that the trie builds for the address passes the check.

It passes with the fields of the account that the trie holds.

It reports an address without a value as absent, when the fields fit an address with no account.

The same holds for each slot, when the answer gives the word `0` to a slot without a value.

The state and storage tries of a state have distinct keys, so soundness holds for them as stated.

Completeness needs distinct paths, which in a secured trie means keys with distinct hashes.

Each of the two checks passes exactly when the proof gives no value, or a value matching the answer.

An address without a value also needs fields that fit an address with no account.

A slot without a value also needs the word `0` in the answer.

The slot checks of a whole answer pass exactly when each slot passes at its own index.
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Serialization.Rlp

namespace AccountProof

variable {hash : ByteArray → Hash32}

/-- The value that the account check reads, and the outcome that it gives on that value. -/
theorem verifyAccount_eq_ok {stateRoot : Hash32} {p : AccountProof} {present : Bool}
    (h : p.verifyAccount hash stateRoot = .ok present) :
    ∃ value,
      verifyProof hash stateRoot true ⟨p.address.toArray⟩ p.accountProof = .ok value ∧
      match value with
      | some bytes => decodeAccount bytes = .ok (p.account, p.storageHash) ∧ present = true
      | none =>
        p.absentFields hash = true ∧ present = false := by
  unfold verifyAccount at h
  cases hv : verifyProof hash stateRoot true ⟨p.address.toArray⟩ p.accountProof with
  | error e => simp [hv, Except.mapError, bind, Except.bind] at h
  | ok value =>
    refine ⟨value, rfl, ?_⟩
    simp only [hv, Except.mapError, bind, Except.bind] at h
    cases value with
    | none =>
      by_cases hm : p.absentFields hash = true
      · simp only [hm, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
        exact ⟨hm, h.symm⟩
      · simp [hm, throw, throwThe, MonadExceptOf.throw] at h
    | some bytes =>
      cases hd : decodeAccount bytes with
      | error e => simp [hd] at h
      | ok decoded =>
        obtain ⟨account, storageRoot⟩ := decoded
        simp only [hd] at h
        by_cases hm : account = p.account ∧ storageRoot = p.storageHash
        · obtain ⟨rfl, rfl⟩ := hm
          simp only [and_self, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
          exact ⟨hd, h.symm⟩
        · simp [hm, throw, throwThe, MonadExceptOf.throw] at h

/-- The account check passes exactly when the proof gives no value, or a matching value.

A value must decode to the account and the storage root of the answer.

The check then reports the account present.

No value means the account is absent.

The fields of the answer must then fit an address with no account. -/
theorem verifyAccount_eq_ok_iff {stateRoot : Hash32} {p : AccountProof} {present : Bool} :
    p.verifyAccount hash stateRoot = .ok present ↔
      ∃ value,
        verifyProof hash stateRoot true ⟨p.address.toArray⟩ p.accountProof = .ok value ∧
        match value with
        | some bytes => decodeAccount bytes = .ok (p.account, p.storageHash) ∧ present = true
        | none =>
          p.absentFields hash = true ∧ present = false := by
  refine ⟨verifyAccount_eq_ok, fun ⟨value, hv, hmatch⟩ => ?_⟩
  unfold verifyAccount
  cases value with
  | none =>
    obtain ⟨ha, rfl⟩ := hmatch
    simp [hv, ha, Except.mapError, bind, Except.bind, pure, Except.pure]
  | some bytes =>
    obtain ⟨hd, rfl⟩ := hmatch
    simp [hv, hd, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- The value that the slot check reads, and the outcome that it gives on that value. -/
theorem verifySlot_eq_ok {storageRoot : Hash32} {index : Nat} {s : StorageProof}
    {outcome : SlotOutcome} (h : verifySlot hash storageRoot index s = .ok outcome) :
    ∃ value, verifyProof hash storageRoot true ⟨s.key.toArray⟩ s.proof = .ok value ∧
      match value with
      | some bytes => (Codec.decode bytes : Except RlpError U256) = .ok s.value ∧ outcome = .set
      | none => s.value = 0 ∧ outcome = .absent := by
  unfold verifySlot at h
  cases hv : verifyProof hash storageRoot true ⟨s.key.toArray⟩ s.proof with
  | error e => simp [hv, Except.mapError, bind, Except.bind] at h
  | ok value =>
    refine ⟨value, rfl, ?_⟩
    simp only [hv, Except.mapError, bind, Except.bind] at h
    cases value with
    | none =>
      by_cases hz : s.value = 0
      · simp [hz, pure, Except.pure] at h
        exact ⟨hz, h.symm⟩
      · -- The simp set writes the literal of the definition as `0#256`.
        have hz' : ¬s.value = 0#256 := hz
        simp [hz', throw, throwThe, MonadExceptOf.throw] at h
    | some bytes =>
      cases hd : (Codec.decode bytes : Except RlpError U256) with
      | error e => simp [hd] at h
      | ok word =>
        simp only [hd] at h
        by_cases hm : word = s.value
        · subst hm
          simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
          exact ⟨hd, h.symm⟩
        · simp [hm, throw, throwThe, MonadExceptOf.throw] at h

/-- The slot check passes exactly when the proof gives a matching value, or none and the word `0`.

A value must decode to the word of the answer, and the check reports the slot set.

No value means the slot is absent, and the answer must give it the word `0`. -/
theorem verifySlot_eq_ok_iff {storageRoot : Hash32} {index : Nat} {s : StorageProof}
    {outcome : SlotOutcome} :
    verifySlot hash storageRoot index s = .ok outcome ↔
      ∃ value, verifyProof hash storageRoot true ⟨s.key.toArray⟩ s.proof = .ok value ∧
        match value with
        | some bytes => (Codec.decode bytes : Except RlpError U256) = .ok s.value ∧ outcome = .set
        | none => s.value = 0 ∧ outcome = .absent := by
  refine ⟨verifySlot_eq_ok, fun ⟨value, hv, hmatch⟩ => ?_⟩
  unfold verifySlot
  cases value with
  | none =>
    obtain ⟨hz, rfl⟩ := hmatch
    simp [hv, hz, Except.mapError, bind, Except.bind, pure, Except.pure]
  | some bytes =>
    obtain ⟨hd, rfl⟩ := hmatch
    simp [hv, hd, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- An account whose proven fields differ from those of the answer fails with `accountMismatch`. -/
theorem verifyAccount_eq_accountMismatch {stateRoot : Hash32} {p : AccountProof}
    {bytes : ByteArray} {account : Account} {storageRoot : Hash32}
    (hv : verifyProof hash stateRoot true ⟨p.address.toArray⟩ p.accountProof = .ok (some bytes))
    (hd : decodeAccount bytes = .ok (account, storageRoot))
    (hne : ¬(account = p.account ∧ storageRoot = p.storageHash)) :
    p.verifyAccount hash stateRoot = .error .accountMismatch := by
  simp [verifyAccount, hv, hd, hne, Except.mapError, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- An absent account whose fields do not fit an address with no account fails with a mismatch. -/
theorem verifyAccount_eq_accountMismatch_absent {stateRoot : Hash32} {p : AccountProof}
    (hv : verifyProof hash stateRoot true ⟨p.address.toArray⟩ p.accountProof = .ok none)
    (ha : p.absentFields hash = false) :
    p.verifyAccount hash stateRoot = .error .accountMismatch := by
  simp [verifyAccount, hv, ha, Except.mapError, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- A slot whose proven word differs from that of the answer fails with `slotMismatch`. -/
theorem verifySlot_eq_slotMismatch {storageRoot : Hash32} {index : Nat} {s : StorageProof}
    {bytes : ByteArray} {word : U256}
    (hv : verifyProof hash storageRoot true ⟨s.key.toArray⟩ s.proof = .ok (some bytes))
    (hd : (Codec.decode bytes : Except RlpError U256) = .ok word) (hne : word ≠ s.value) :
    verifySlot hash storageRoot index s = .error (.slotMismatch index) := by
  simp [verifySlot, hv, hd, hne, Except.mapError, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- The slot checks pass exactly when each slot passes its check at its own index.

The slots are numbered from `index`, and there is one outcome for each slot, in order. -/
theorem verifySlots_eq_ok_iff {storageRoot : Hash32} :
    ∀ {index : Nat} {slots : List StorageProof} {outcomes : List SlotOutcome},
      verifySlots hash storageRoot index slots = .ok outcomes ↔
        ∃ hlen : outcomes.length = slots.length, ∀ (i : Nat) (hi : i < slots.length),
          verifySlot hash storageRoot (index + i) slots[i] = .ok (outcomes[i]'(hlen ▸ hi))
  | index, [], outcomes => by
    cases outcomes <;> simp [verifySlots, pure, Except.pure]
  | index, s :: rest, outcomes => by
    simp only [verifySlots, bind, Except.bind]
    cases hs : verifySlot hash storageRoot index s with
    | error e =>
      simp only [reduceCtorEq, false_iff, not_exists]
      intro _ h
      have := h 0 (by simp)
      simp [hs] at this
    | ok o =>
      cases hr : verifySlots hash storageRoot (index + 1) rest with
      | error e =>
        simp only [reduceCtorEq, false_iff, not_exists]
        intro hlen h
        cases outcomes with
        | nil => simp at hlen
        | cons o' os =>
          -- The checks of the rest pass too, so the recursive call cannot fail.
          have hrest := (verifySlots_eq_ok_iff (index := index + 1) (slots := rest)
            (outcomes := os)).mpr ⟨by simpa using hlen, fun i hi => by
              have := h (i + 1) (by simp [hi])
              simpa [Nat.add_assoc, Nat.add_comm 1 i] using this⟩
          rw [hr] at hrest
          cases hrest
      | ok os =>
        simp only [pure, Except.pure, Except.ok.injEq]
        constructor
        · rintro rfl
          obtain ⟨hlen, h⟩ := (verifySlots_eq_ok_iff (index := index + 1)).mp hr
          refine ⟨by simp [hlen], fun i hi => ?_⟩
          cases i with
          | zero => simpa using hs
          | succ i =>
            have := h i (by simpa using hi)
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
        · rintro ⟨hlen, h⟩
          cases outcomes with
          | nil => simp at hlen
          | cons o' os' =>
            have h0 := h 0 (by simp)
            simp only [Nat.add_zero, List.getElem_cons_zero, hs, Except.ok.injEq] at h0
            have hrest := (verifySlots_eq_ok_iff (index := index + 1) (slots := rest)
              (outcomes := os')).mpr ⟨by simpa using hlen, fun i hi => by
                have := h (i + 1) (by simp [hi])
                simpa [Nat.add_assoc, Nat.add_comm 1 i] using this⟩
            rw [hr] at hrest
            cases hrest
            rw [h0]

/-- The slot checks of an absent account pass exactly when each slot gives the word `0`. -/
theorem verifyAbsentSlots_eq_ok_iff :
    ∀ {index : Nat} {slots : List StorageProof},
      verifyAbsentSlots index slots = .ok () ↔ ∀ s ∈ slots, s.value = 0
  | _, [] => by simp [verifyAbsentSlots, pure, Except.pure]
  | index, s :: rest => by
    have ih := verifyAbsentSlots_eq_ok_iff (index := index + 1) (slots := rest)
    by_cases hs : s.value = 0
    · simp [verifyAbsentSlots, hs, ih]
    · simp only [verifyAbsentSlots, ite_eq_right hs]
      simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq, false_iff]
      exact fun h => hs (h s List.mem_cons_self)

/-- A whole answer shows the account exactly when the account check passes with it present.

The slots then come out of the slot checks, from index 0. -/
theorem verify_eq_ok_present_iff {stateRoot : Hash32} {p : AccountProof}
    {slots : List SlotOutcome} :
    p.verify hash stateRoot = .ok (.present slots) ↔
      p.verifyAccount hash stateRoot = .ok true ∧
        verifySlots hash p.storageHash 0 p.storageProof = .ok slots := by
  unfold verify
  cases ha : p.verifyAccount hash stateRoot with
  | error e => simp [bind, Except.bind]
  | ok present =>
    cases present with
    | false =>
      cases verifyAbsentSlots 0 p.storageProof <;> simp [bind, Except.bind, pure, Except.pure]
    | true =>
      cases verifySlots hash p.storageHash 0 p.storageProof <;>
        simp [bind, Except.bind, pure, Except.pure]

/-- A whole answer shows the address absent exactly when the account check passes with it absent.

Each slot of the answer must then give the word `0`. -/
theorem verify_eq_ok_absent_iff {stateRoot : Hash32} {p : AccountProof} :
    p.verify hash stateRoot = .ok .absent ↔
      p.verifyAccount hash stateRoot = .ok false ∧ ∀ s ∈ p.storageProof, s.value = 0 := by
  rw [← verifyAbsentSlots_eq_ok_iff (index := 0)]
  unfold verify
  cases ha : p.verifyAccount hash stateRoot with
  | error e => simp [bind, Except.bind]
  | ok present =>
    cases present with
    | false =>
      cases h : verifyAbsentSlots 0 p.storageProof <;>
        simp [bind, Except.bind, pure, Except.pure]
    | true =>
      cases verifySlots hash p.storageHash 0 p.storageProof <;>
        simp [bind, Except.bind, pure, Except.pure]

/-! ## Soundness -/

/-- Soundness of the account check against a secured trie with distinct keys and its root.

When the check passes, the trie gives the address the account of the answer.

When it reports the account absent, the trie gives the address no value.

The fields of the answer then fit an address with no account.

Otherwise a search finds a collision with the trie's own proof, or two keys with one hash. -/
theorem verifyAccount_sound {trie : Trie} {stateRoot : Hash32} {honest : List ByteArray}
    {p : AccountProof} {present : Bool}
    (hroot : root hash trie = .ok stateRoot) (hsecured : trie.secured = true)
    (hhonest : getProof hash trie ⟨p.address.toArray⟩ = .ok honest)
    (hkeys : (trie.data.map Prod.fst).Nodup)
    (h : p.verifyAccount hash stateRoot = .ok present) :
    (match valueAt hash trie ⟨p.address.toArray⟩ with
      | some bytes => decodeAccount bytes = .ok (p.account, p.storageHash) ∧ present = true
      | none =>
        p.absentFields hash = true ∧ present = false) ∨
      (∃ pair,
        findProofCollision hash p.accountProof honest = some pair ∧ IsCollision hash pair) ∨
      ∃ pair, findPathCollision hash trie = some pair ∧ IsCollision hash pair := by
  obtain ⟨value, hverify, hvalue⟩ := verifyAccount_eq_ok h
  rw [← hsecured] at hverify
  rcases verifyProof_sound hash hroot hhonest hkeys hverify with ⟨-, hv⟩ | hfound | hfound
  · exact .inl (hv ▸ hvalue)
  · exact .inr (.inl hfound)
  · exact .inr (.inr hfound)

/-- Soundness of the slot check against a secured storage trie with distinct keys and its root.

When the check passes, the trie gives the slot the encoding of the word of the answer.

When it reports the slot absent, the trie gives the slot no value, and the answer gives it `0`.

Otherwise a search finds a collision with the trie's own proof, or two keys with one hash. -/
theorem verifySlot_sound {trie : Trie} {storageRoot : Hash32} {honest : List ByteArray}
    {index : Nat} {s : StorageProof} {outcome : SlotOutcome}
    (hroot : root hash trie = .ok storageRoot) (hsecured : trie.secured = true)
    (hhonest : getProof hash trie ⟨s.key.toArray⟩ = .ok honest)
    (hkeys : (trie.data.map Prod.fst).Nodup)
    (h : verifySlot hash storageRoot index s = .ok outcome) :
    (match valueAt hash trie ⟨s.key.toArray⟩ with
      | some bytes => (Codec.decode bytes : Except RlpError U256) = .ok s.value ∧ outcome = .set
      | none => s.value = 0 ∧ outcome = .absent) ∨
      (∃ pair, findProofCollision hash s.proof honest = some pair ∧ IsCollision hash pair) ∨
      ∃ pair, findPathCollision hash trie = some pair ∧ IsCollision hash pair := by
  obtain ⟨value, hverify, hvalue⟩ := verifySlot_eq_ok h
  rw [← hsecured] at hverify
  rcases verifyProof_sound hash hroot hhonest hkeys hverify with ⟨-, hv⟩ | hfound | hfound
  · exact .inl (hv ▸ hvalue)
  · exact .inr (.inl hfound)
  · exact .inr (.inr hfound)

/-- Soundness of the account check against the state trie of a state. -/
theorem verifyAccount_sound_state {state : State} {entries : List (ByteArray × ByteArray)}
    {stateRoot : Hash32} {honest : List ByteArray} {p : AccountProof} {present : Bool}
    (hentries : stateEntries hash state = .ok entries)
    (hroot : root hash ⟨true, entries⟩ = .ok stateRoot)
    (hhonest : getProof hash ⟨true, entries⟩ ⟨p.address.toArray⟩ = .ok honest)
    (h : p.verifyAccount hash stateRoot = .ok present) :
    (match valueAt hash ⟨true, entries⟩ ⟨p.address.toArray⟩ with
      | some bytes => decodeAccount bytes = .ok (p.account, p.storageHash) ∧ present = true
      | none =>
        p.absentFields hash = true ∧ present = false) ∨
      (∃ pair,
        findProofCollision hash p.accountProof honest = some pair ∧ IsCollision hash pair) ∨
      ∃ pair, findPathCollision hash ⟨true, entries⟩ = some pair ∧ IsCollision hash pair :=
  verifyAccount_sound hroot rfl hhonest (stateEntries_nodup hentries) h

/-- Soundness of the slot check against the storage trie of a storage. -/
theorem verifySlot_sound_storage {storage : Std.ExtTreeMap Bytes32 U256}
    {entries : List (ByteArray × ByteArray)} {storageRoot : Hash32} {honest : List ByteArray}
    {index : Nat} {s : StorageProof} {outcome : SlotOutcome}
    (hentries : storageEntries storage = .ok entries)
    (hroot : root hash ⟨true, entries⟩ = .ok storageRoot)
    (hhonest : getProof hash ⟨true, entries⟩ ⟨s.key.toArray⟩ = .ok honest)
    (h : verifySlot hash storageRoot index s = .ok outcome) :
    (match valueAt hash ⟨true, entries⟩ ⟨s.key.toArray⟩ with
      | some bytes => (Codec.decode bytes : Except RlpError U256) = .ok s.value ∧ outcome = .set
      | none => s.value = 0 ∧ outcome = .absent) ∨
      (∃ pair, findProofCollision hash s.proof honest = some pair ∧ IsCollision hash pair) ∨
      ∃ pair, findPathCollision hash ⟨true, entries⟩ = some pair ∧ IsCollision hash pair :=
  verifySlot_sound hroot rfl hhonest (storageEntries_nodup hentries) h

/-! ## Completeness -/

/-- Completeness of the account check: the trie's own proof of the address passes.

It passes when the answer has the fields of the account that the trie holds.

It reports an address without a value as absent, when the fields fit an address with no account.

The keys of the trie must have distinct paths. -/
theorem verifyAccount_getProof {trie : Trie} {stateRoot : Hash32} {p : AccountProof}
    (hroot : root hash trie = .ok stateRoot) (hsecured : trie.secured = true)
    (hhonest : getProof hash trie ⟨p.address.toArray⟩ = .ok p.accountProof)
    (hpaths : (trie.data.map fun entry => keyPath hash trie.secured entry.1).Nodup) :
    match valueAt hash trie ⟨p.address.toArray⟩ with
    | some bytes =>
      decodeAccount bytes = .ok (p.account, p.storageHash) →
        p.verifyAccount hash stateRoot = .ok true
    | none =>
      p.absentFields hash = true → p.verifyAccount hash stateRoot = .ok false := by
  have hverify := verifyProof_getProof hash hroot hhonest hpaths
  rw [hsecured] at hverify
  unfold verifyAccount
  cases hv : valueAt hash trie ⟨p.address.toArray⟩ with
  | none =>
    intro ha
    simp [hverify, hv, ha, Except.mapError, bind, Except.bind, pure, Except.pure]
  | some bytes =>
    intro hd
    simp [hverify, hv, hd, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Completeness of the slot check: the trie's own proof of the slot passes.

It passes when the answer has the word that the trie holds.

It reports a slot without a value as absent, when the answer gives it the word `0`.

The keys of the trie must have distinct paths. -/
theorem verifySlot_getProof {trie : Trie} {storageRoot : Hash32} {index : Nat} {s : StorageProof}
    (hroot : root hash trie = .ok storageRoot) (hsecured : trie.secured = true)
    (hhonest : getProof hash trie ⟨s.key.toArray⟩ = .ok s.proof)
    (hpaths : (trie.data.map fun entry => keyPath hash trie.secured entry.1).Nodup) :
    match valueAt hash trie ⟨s.key.toArray⟩ with
    | some bytes =>
      (Codec.decode bytes : Except RlpError U256) = .ok s.value →
        verifySlot hash storageRoot index s = .ok .set
    | none => s.value = 0 → verifySlot hash storageRoot index s = .ok .absent := by
  have hverify := verifyProof_getProof hash hroot hhonest hpaths
  rw [hsecured] at hverify
  unfold verifySlot
  cases hv : valueAt hash trie ⟨s.key.toArray⟩ with
  | none =>
    intro hz
    simp [hverify, hv, hz, Except.mapError, bind, Except.bind, pure, Except.pure]
  | some bytes =>
    intro hd
    simp [hverify, hv, hd, Except.mapError, bind, Except.bind, pure, Except.pure]

end AccountProof

/-! ## The codes of the errors -/

/-- Two errors with one code come from one constructor. -/
theorem AccountProofError.code_injective (e₁ e₂ : AccountProofError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [AccountProofError.code] at h; exact absurd h (by decide))

/-- An account proof error never has the code of a proof error, so one Python class carries both.
-/
theorem AccountProofError.code_ne_proof (e : AccountProofError) (r : Trie.ProofError) :
    e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [AccountProofError.code, Trie.ProofError.code] <;> decide

/-- An account proof error never has the code of a trie error, so one Python class carries both.
-/
theorem AccountProofError.code_ne_trie (e : AccountProofError) (r : Trie.TrieError) :
    e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [AccountProofError.code, Trie.TrieError.code] <;> decide

/-- An account proof error never has the code of a range error, so one Python class carries both.
-/
theorem AccountProofError.code_ne_range (e : AccountProofError) (r : Trie.RangeError) :
    e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [AccountProofError.code, Trie.RangeError.code] <;> decide

end EthLib.Execution.State

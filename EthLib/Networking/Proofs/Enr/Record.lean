module

public import EthLib.Networking.Enr.Record
public import EthLib.Networking.Proofs.Enr.Base64
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the decoder of node records

The decoder rejects a record over 300 bytes.

The keys of every record it accepts strictly increase, so they are sorted and unique.

Every record it accepts has the key `id`, and it rejects a record without it.

It undoes the encoder on every record that fits, has increasing keys and has the key `id`.

The same holds for the text form.
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Serialization.Rlp

/-! ## Rejections -/

/-- The decoder rejects more than 300 bytes. -/
theorem decode_tooLarge (bytes : ByteArray) (h : MAX_RECORD_SIZE < bytes.size) :
    decode bytes = .error (.tooLarge bytes.size) := by
  simp only [decode, h, ↓reduceIte]
  rfl

/-- Every record that the decoder accepts came from at most 300 bytes. -/
theorem size_le_of_decode {bytes : ByteArray} {r : Enr} (h : decode bytes = .ok r) :
    bytes.size ≤ MAX_RECORD_SIZE := by
  apply Nat.le_of_not_lt
  intro hlt
  rw [decode_tooLarge bytes hlt] at h
  cases h

/-- Keys whose check succeeds strictly increase, each before every later one. -/
theorem pairwise_of_checkKeys :
    (pairs : List (ByteArray × Item)) → checkKeys pairs = .ok () →
      pairs.Pairwise (fun p q => keyLt p.1 q.1)
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | p :: q :: rest, h => by
    unfold checkKeys at h
    split at h
    · rename_i hpq
      have hrest := pairwise_of_checkKeys (q :: rest) h
      refine List.Pairwise.cons ?_ hrest
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hpq
      -- A later key comes after `q`, which comes after `p`.
      · exact List.lt_trans hpq (List.rel_of_pairwise_cons hrest hs)
    · split at h <;> cases h

/-- Strictly increasing keys pass the check. -/
theorem checkKeys_of_pairwise :
    (pairs : List (ByteArray × Item)) → pairs.Pairwise (fun p q => keyLt p.1 q.1) →
      checkKeys pairs = .ok ()
  | [], _ => rfl
  | [_], _ => rfl
  | p :: q :: rest, h => by
    have hpq : keyLt p.1 q.1 := List.rel_of_pairwise_cons h List.mem_cons_self
    unfold checkKeys
    rw [ite_eq_left hpq]
    exact checkKeys_of_pairwise (q :: rest) (List.Pairwise.of_cons h)

/-- A decoded record passed both checks on its pairs: the order of the keys, and the key `id`. -/
theorem checks_of_decode {bytes : ByteArray} {r : Enr} (h : decode bytes = .ok r) :
    checkKeys r.pairs = .ok () ∧ r.pairs.any (·.1 = KEY_ID) = true := by
  unfold decode at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    rename_i pairs _
    split at h
    · cases h
    rename_i hk
    split at h
    · -- The record has the key `id`, and its keys passed the check.
      rename_i hid
      cases h
      exact ⟨by cases hc : checkKeys pairs <;> simp_all, hid⟩
    · cases h
  all_goals cases h

/-- The keys of a decoded record strictly increase: they are sorted, and no key repeats. -/
theorem pairwise_of_decode {bytes : ByteArray} {r : Enr} (h : decode bytes = .ok r) :
    r.pairs.Pairwise (fun p q => keyLt p.1 q.1) :=
  pairwise_of_checkKeys r.pairs (checks_of_decode h).1

/-- A decoded record has the key `id`. -/
theorem has_id_of_decode {bytes : ByteArray} {r : Enr} (h : decode bytes = .ok r) :
    ∃ value, (KEY_ID, value) ∈ r.pairs := by
  obtain ⟨⟨key, value⟩, hmem, hkey⟩ := List.any_eq_true.mp (checks_of_decode h).2
  simp only [decide_eq_true_eq] at hkey
  exact ⟨value, hkey ▸ hmem⟩

/-- No key repeats in a decoded record. -/
theorem keys_nodup_of_decode {bytes : ByteArray} {r : Enr} (h : decode bytes = .ok r) :
    (r.pairs.map (·.1)).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  -- A key never comes before itself.
  refine (pairwise_of_decode h).imp fun {a b} hlt heq => ?_
  rw [heq] at hlt
  exact List.lt_irrefl _ hlt

/-! ## Round trip -/

/-- The pairs read back from their items. -/
theorem readPairs_flatten :
    (pairs : List (ByteArray × Item)) → readPairs (flatten pairs) = .ok pairs
  | [] => rfl
  | (key, value) :: rest => by
    simp only [flatten, readPairs, readPairs_flatten rest, bind, Except.bind, pure, Except.pure]

/-- The pairs have the key `id` exactly when one of their keys is `id`. -/
theorem any_id_iff (pairs : List (ByteArray × Item)) :
    pairs.any (·.1 = KEY_ID) = true ↔ ∃ value, (KEY_ID, value) ∈ pairs := by
  simp only [List.any_eq_true, decide_eq_true_eq, Prod.exists]
  constructor
  · rintro ⟨key, value, hmem, rfl⟩
    exact ⟨value, hmem⟩
  · rintro ⟨value, hmem⟩
    exact ⟨KEY_ID, value, hmem, rfl⟩

/-- On a record that fits and has increasing keys, only the key `id` decides the answer. -/
theorem decode_of_encode (r : Enr) (bytes : ByteArray) (he : r.encode = .ok bytes)
    (hs : bytes.size ≤ MAX_RECORD_SIZE) (hk : r.pairs.Pairwise (fun p q => keyLt p.1 q.1)) :
    decode bytes = if r.pairs.any (·.1 = KEY_ID) then .ok r else .error .missingId := by
  unfold Enr.encode at he
  unfold decode
  simp only [Nat.not_lt.mpr hs, ↓reduceIte, Serialization.Rlp.decode_encode _ _ he,
    Except.mapError, LawfulCodec.ofItem_toItem, readPairs_flatten, checkKeys_of_pairwise _ hk, bind,
    Except.bind, pure, Except.pure]
  split <;> rfl

/-- The decoder undoes the encoder on a record that fits, has increasing keys and has `id`. -/
theorem decode_encode (r : Enr) (bytes : ByteArray) (he : r.encode = .ok bytes)
    (hs : bytes.size ≤ MAX_RECORD_SIZE) (hk : r.pairs.Pairwise (fun p q => keyLt p.1 q.1))
    (hid : ∃ value, (KEY_ID, value) ∈ r.pairs) :
    decode bytes = .ok r := by
  rw [decode_of_encode r bytes he hs hk, ite_eq_left ((any_id_iff r.pairs).mpr hid)]

/-- The decoder rejects a record without the key `id`, even if it fits and its keys increase. -/
theorem decode_missingId (r : Enr) (bytes : ByteArray) (he : r.encode = .ok bytes)
    (hs : bytes.size ≤ MAX_RECORD_SIZE) (hk : r.pairs.Pairwise (fun p q => keyLt p.1 q.1))
    (hid : ∀ value, (KEY_ID, value) ∉ r.pairs) :
    decode bytes = .error .missingId := by
  have hany : r.pairs.any (·.1 = KEY_ID) = false := by
    cases hc : r.pairs.any (·.1 = KEY_ID)
    · rfl
    · obtain ⟨value, hmem⟩ := (any_id_iff r.pairs).mp hc
      exact absurd hmem (hid value)
  rw [decode_of_encode r bytes he hs hk, hany]
  rfl

/-- The text form reads back as the record. -/
theorem fromText_toText (r : Enr) (text : String) (bytes : ByteArray) (he : r.encode = .ok bytes)
    (ht : r.toText = .ok text) (hs : bytes.size ≤ MAX_RECORD_SIZE)
    (hk : r.pairs.Pairwise (fun p q => keyLt p.1 q.1)) (hid : ∃ value, (KEY_ID, value) ∈ r.pairs) :
    fromText text = .ok r := by
  simp only [Enr.toText, he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at ht
  subst ht
  have hdec := Base64.decode_encode bytes
  simp only [Base64.decode, bind, Except.bind, pure, Except.pure] at hdec
  unfold fromText
  simp only [String.toList_append, String.toList_ofList, TEXT_PREFIX, List.cons_append,
    List.nil_append]
  split at hdec
  · cases hdec
  rename_i list hlist
  simp only [Except.ok.injEq] at hdec
  simp only [Base64.encode, String.toList_ofList] at hlist
  simp only [Base64.encode, String.toList_ofList, hlist, Except.mapError, bind, Except.bind,
    hdec, decode_encode r bytes he hs hk hid]

end EthLib.Networking.Enr

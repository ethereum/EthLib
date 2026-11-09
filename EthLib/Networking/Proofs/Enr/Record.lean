module

public import EthLib.Base.Proofs.Base64
public import EthLib.Networking.Enr.Record
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the decoder of node records

The decoder rejects a record over 300 bytes.

The keys of every record it accepts strictly increase, so they are sorted and unique.

Every record it accepts has the key `id`, and it rejects a record without it.

It undoes the encoder on every record that fits, has increasing keys and has the key `id`.

Every record it accepts came from its own encoding, so a record has one accepted encoding.

The same holds for the text form.

Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Base
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

/-! ## Canonical encodings -/

/-- Items that read as pairs are the items of those pairs. -/
theorem flatten_of_readPairs :
    (items : List Item) → {pairs : List (ByteArray × Item)} → readPairs items = .ok pairs →
      flatten pairs = items
  | [], _, h => by
    simp only [readPairs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | .bytes key :: value :: rest, pairs, h => by
    cases hr : readPairs rest with
    | error e => simp [readPairs, hr, bind, Except.bind] at h
    | ok ps =>
      simp only [readPairs, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [flatten, flatten_of_readPairs rest hr]
  | .list _ :: _ :: _, _, h => by
    simp [readPairs, throw, throwThe, MonadExceptOf.throw] at h
  | [_], _, h => by
    simp [readPairs, throw, throwThe, MonadExceptOf.throw] at h

/-- Bytes that decode to a record are the encoding of that record. -/
theorem encode_of_decode {bytes : ByteArray} {r : Enr} (h : decode bytes = .ok r) :
    r.encode = .ok bytes := by
  unfold decode at h
  by_cases hsize : MAX_RECORD_SIZE < bytes.size
  · simp [hsize, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  cases hd : Serialization.Rlp.decode bytes with
  | error e => simp [hsize, hd, Except.mapError, bind, Except.bind] at h
  | ok item =>
    simp only [hsize, hd, ↓reduceIte, Except.mapError, bind, Except.bind] at h
    split at h
    · rename_i signature seqItem rest
      -- Each read succeeded, and each one is inverted by the encoder.
      cases hseq : (Codec.ofItem seqItem : Except RlpError UInt64) with
      | error e => simp [hseq] at h
      | ok seq =>
        cases hp : readPairs rest with
        | error e => simp [hseq, hp] at h
        | ok pairs =>
          cases hc : checkKeys pairs with
          | error e => simp [hseq, hp, hc] at h
          | ok u =>
            by_cases hid : pairs.any (·.1 = KEY_ID) = true
            · simp only [hseq, hp, hc, hid, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
              subst h
              rw [Enr.encode, LawfulCodec.toItem_of_ofItem hseq, flatten_of_readPairs rest hp]
              exact Serialization.Rlp.encode_decode bytes _ hd
            · simp [hseq, hp, hc, hid, throw, throwThe, MonadExceptOf.throw] at h
    all_goals simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Bytes decode to a record exactly when they are its encoding and the record passes the checks.

The checks are the size of at most 300 bytes, keys that strictly increase, and the key `id`. -/
theorem decode_eq_ok_iff (bytes : ByteArray) (r : Enr) :
    decode bytes = .ok r ↔ r.encode = .ok bytes ∧ bytes.size ≤ MAX_RECORD_SIZE ∧
      r.pairs.Pairwise (fun p q => keyLt p.1 q.1) ∧ ∃ value, (KEY_ID, value) ∈ r.pairs :=
  ⟨fun h => ⟨encode_of_decode h, size_le_of_decode h, pairwise_of_decode h, has_id_of_decode h⟩,
    fun ⟨he, hs, hk, hid⟩ => decode_encode r bytes he hs hk hid⟩

/-- A text that reads as a record is the text form of that record. -/
theorem toText_of_fromText {text : String} {r : Enr} (h : fromText text = .ok r) :
    r.toText = .ok text := by
  unfold fromText at h
  split at h
  · rename_i rest htext
    cases hb : Base64.decodeList rest with
    | error e => simp [hb, Except.mapError, bind, Except.bind] at h
    | ok bytes =>
      simp only [hb, Except.mapError, bind, Except.bind] at h
      -- The bytes are the encoding of the record, and the characters are the base64 of the bytes.
      have hl := Base64.encodeList_decodeList rest bytes hb
      simp only [Enr.toText, encode_of_decode h, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq]
      apply String.toList_injective
      simp [Base64.encode, TEXT_PREFIX, hl, htext]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem EnrError.code_injective (e₁ e₂ : EnrError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [EnrError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Enr

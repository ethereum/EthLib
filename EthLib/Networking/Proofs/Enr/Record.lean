module

public import EthLib.Networking.Enr.Record
public import EthLib.Networking.Proofs.Enr.Base64
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the decoder of node records

The decoder rejects a record over 300 bytes.

The keys of every record it accepts strictly increase, so they are sorted and unique.

It undoes the encoder on every record that fits and has increasing keys.

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

/-- The keys of a decoded record strictly increase: they are sorted, and no key repeats. -/
theorem pairwise_of_decode {bytes : ByteArray} {r : Enr} (h : decode bytes = .ok r) :
    r.pairs.Pairwise (fun p q => keyLt p.1 q.1) := by
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
    cases h
    exact pairwise_of_checkKeys pairs (by cases hc : checkKeys pairs <;> simp_all)
  all_goals cases h

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

/-- The decoder undoes the encoder on a record that fits in 300 bytes and has increasing keys. -/
theorem decode_encode (r : Enr) (bytes : ByteArray) (he : r.encode = .ok bytes)
    (hs : bytes.size ≤ MAX_RECORD_SIZE) (hk : r.pairs.Pairwise (fun p q => keyLt p.1 q.1)) :
    decode bytes = .ok r := by
  unfold Enr.encode at he
  unfold decode
  simp only [Nat.not_lt.mpr hs, ↓reduceIte, Serialization.Rlp.decode_encode _ _ he,
    Except.mapError, LawfulCodec.ofItem_toItem, readPairs_flatten, checkKeys_of_pairwise _ hk, bind,
    Except.bind, pure, Except.pure]

/-- The text form reads back as the record. -/
theorem fromText_toText (r : Enr) (text : String) (bytes : ByteArray) (he : r.encode = .ok bytes)
    (ht : r.toText = .ok text) (hs : bytes.size ≤ MAX_RECORD_SIZE)
    (hk : r.pairs.Pairwise (fun p q => keyLt p.1 q.1)) :
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
    hdec, decode_encode r bytes he hs hk]

end EthLib.Networking.Enr

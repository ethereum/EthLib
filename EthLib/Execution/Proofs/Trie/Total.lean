module

public import EthLib.Execution.Proofs.Trie.HexPrefix
public import EthLib.Execution.Proofs.Trie.Root
public import EthLib.Serialization.Proofs.Rlp.Bound

/-!
# Proofs: which maps have a root

A map whose keys and values have fewer than `2^32` bytes has a root exactly when no value is empty.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-- The packed bytes of an even run of nibbles number half of them. -/
private theorem length_packNibbles :
    (x : List Nibble) → (h : x.length % 2 = 0) → (packNibbles x h).length = x.length / 2
  | [], _ => rfl
  | [_], h => by simp at h
  | _ :: _ :: rest, h => by
    simp only [packNibbles, List.length_cons, length_packNibbles rest]
    omega

/-- The hex-prefix encoding of a path has at most one byte more than half the path. -/
private theorem size_nibbleListToCompact (x : List Nibble) (isLeaf : Bool) :
    (nibbleListToCompact x isLeaf).size ≤ x.length / 2 + 1 := by
  unfold nibbleListToCompact
  split
  · simp [ByteArray.size, length_packNibbles]
    omega
  · simp [ByteArray.size, length_packNibbles]
    omega

/-- A node that encodes is held by its parent as an item of at most 33 encoded bytes. -/
private theorem encodeInternalNode_ok (hash : ByteArray → Hash32) (node : Option InternalNode)
    (e : ByteArray) (h : encode (unencoded node) = .ok e) :
    ∃ held, encodeInternalNode hash node = .ok held ∧
      ∃ eh, encode held = .ok eh ∧ eh.size ≤ 33 := by
  rw [encodeInternalNode_eq, h]
  by_cases hs : e.size < 32
  · exact ⟨_, by simp [hs, bind, Except.bind, pure, Except.pure], e, h, by omega⟩
  · have hb : (⟨(hash e).toArray⟩ : ByteArray).size = 32 := by simp [ByteArray.size]
    obtain ⟨eh, heh⟩ := (encode_bytes_succeeds_iff _).2 (by rw [hb]; decide)
    exact ⟨_, by simp [hs, bind, Except.bind, pure, Except.pure], eh, heh,
      by have := (encode_bytes_size_le _ _ heh).2 (by rw [hb]; decide); omega⟩

/-- The value a branch picks from its keys is the start value or the value of one of them. -/
private theorem foldl_value (p : ByteArray → Prop) (level : Nat) :
    (obj : List (List Nibble × ByteArray)) → (start : ByteArray) → p start →
      (∀ entry ∈ obj, p entry.2) →
      p (obj.foldl (fun value entry => if entry.1.length = level then entry.2 else value) start)
  | [], _, hstart, _ => hstart
  | (key, keyValue) :: rest, start, hstart, hobj => by
    refine foldl_value p level rest _ ?_ fun entry he => hobj entry (List.mem_cons_of_mem _ he)
    show p (if key.length = level then keyValue else start)
    split
    · exact hobj _ List.mem_cons_self
    · exact hstart

/-- A map of a function that succeeds on every entry succeeds, with outputs from it. -/
private theorem mapMVector_exists_ok {α β ε : Type} {f : α → Except ε β} (q : β → Prop) :
    (xs : List α) → (∀ x ∈ xs, ∃ y, f x = .ok y ∧ q y) →
      ∃ ys, mapMVector f xs = .ok ys ∧ ∀ y ∈ ys.toList, q y
  | [], _ => ⟨⟨#[], rfl⟩, rfl, by simp⟩
  | x :: rest, h => by
    obtain ⟨y, hy, hq⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys, hqs⟩ :=
      mapMVector_exists_ok q rest fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨⟨⟨y :: ys.toList⟩, by simp⟩,
      by simp only [mapMVector, hy, hys, bind, Except.bind, pure, Except.pure], ?_⟩
    intro z hz
    simp only [Vector.toList_mk, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hq
    · exact hqs z hz

/-- One step on short paths and values gives a node that encodes, if the nested calls do. -/
private theorem patricializeStep_encodes (hash : ByteArray → Hash32)
    (recurse : List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode))
    (hrec : ∀ obj level, (∀ entry ∈ obj, entry.1.length < 2 ^ 33 ∧ entry.2.size < 2 ^ 32) →
      ∃ node, recurse obj level = .ok node ∧ ∃ e, encode (unencoded node) = .ok e)
    (obj : List (List Nibble × ByteArray)) (level : Nat)
    (hobj : ∀ entry ∈ obj, entry.1.length < 2 ^ 33 ∧ entry.2.size < 2 ^ 32) :
    ∃ node, patricializeStep hash recurse obj level = .ok node ∧
      ∃ e, encode (unencoded node) = .ok e := by
  match obj with
  | [] => exact ⟨none, rfl, (encode_bytes_succeeds_iff _).2 (by simp)⟩
  | [(key, value)] =>
    refine ⟨_, patricializeStep_singleton .., ?_⟩
    have hk := hobj _ List.mem_cons_self
    simp only at hk
    have hc := size_nibbleListToCompact (key.drop level) true
    obtain ⟨e, he, -⟩ := encode_list_exists_ok_of_size_le (2 ^ 33)
      [.bytes (nibbleListToCompact (key.drop level) true), .bytes value] (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · simp only [List.length_drop] at hc
          obtain ⟨e, he, hle, -⟩ :=
            encode_bytes_exists_ok (nibbleListToCompact (key.drop level) true) (by omega)
          exact ⟨e, he, by omega⟩
        · obtain ⟨e, he, hle, -⟩ := encode_bytes_exists_ok value (by omega)
          exact ⟨e, he, by omega⟩) (by simp)
    exact ⟨e, he⟩
  | first :: second :: rest =>
    rw [patricializeStep_cons_cons]
    obtain ⟨nodeOf, hnodeOf⟩ :=
      Classical.axiomOfChoice fun lvl => hrec (first :: second :: rest) lvl hobj
    obtain ⟨eOf, heOf⟩ := Classical.axiomOfChoice fun lvl => (hnodeOf lvl).2
    obtain ⟨heldOf, hheldOf⟩ := Classical.axiomOfChoice
      fun lvl => encodeInternalNode_ok hash (nodeOf lvl) (eOf lvl) (heOf lvl)
    obtain ⟨subOf, hsubOf⟩ := Classical.axiomOfChoice
      fun (pr : List Nibble × ByteArray → Bool) =>
        hrec ((first :: second :: rest).filter pr) (level + 1)
          fun entry he => hobj entry (List.mem_filter.1 he).1
    obtain ⟨seOf, hseOf⟩ := Classical.axiomOfChoice fun pr => (hsubOf pr).2
    obtain ⟨subHeldOf, hsubHeldOf⟩ := Classical.axiomOfChoice
      fun pr => encodeInternalNode_ok hash (subOf pr) (seOf pr) (hseOf pr)
    have hnode := fun lvl => (hnodeOf lvl).1
    have hheld := fun lvl => (hheldOf lvl).1
    have hsub := fun pr => (hsubOf pr).1
    have hsubHeld := fun pr => (hsubHeldOf pr).1
    dsimp only
    simp only [hnode, hheld, hsub, hsubHeld, bind, Except.bind, pure, Except.pure]
    split
    · refine ⟨_, rfl, ?_⟩
      generalize List.foldl _ _ _ = k
      have hf := (hobj first List.mem_cons_self).1
      have hc := size_nibbleListToCompact (List.take k (List.drop level first.1)) false
      obtain ⟨eh, heh, hle⟩ := (hheldOf (level + k)).2
      obtain ⟨e, he, -⟩ := encode_list_exists_ok_of_size_le (2 ^ 33)
        [.bytes (nibbleListToCompact (List.take k (List.drop level first.1)) false),
          heldOf (level + k)] (by
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · simp only [List.length_take, List.length_drop] at hc
            obtain ⟨e, he, hle, -⟩ := encode_bytes_exists_ok
              (nibbleListToCompact (List.take k (List.drop level first.1)) false) (by omega)
            exact ⟨e, he, by omega⟩
          · exact ⟨eh, heh, by omega⟩) (by simp)
      exact ⟨e, he⟩
    · obtain ⟨ys, hys, hq⟩ :=
        mapMVector_exists_ok (fun held => ∃ eh, encode held = .ok eh ∧ eh.size ≤ 33)
          (f := fun nibble => Except.ok (subHeldOf fun x => decide (x.fst[level]? = some nibble)))
          (List.finRange 16) (fun nibble _ => ⟨_, rfl, (hsubHeldOf _).2⟩)
      rw [hys]
      refine ⟨_, rfl, ?_⟩
      have hv : (List.foldl (fun value x => if x.fst.length = level then x.snd else value)
          ByteArray.empty (first :: second :: rest)).size < 2 ^ 32 :=
        foldl_value (fun v => v.size < 2 ^ 32) level _ _ (by simp [ByteArray.size])
          fun e he => (hobj e he).2
      generalize List.foldl _ ByteArray.empty _ = value at hv
      refine (encode_list_exists_ok_of_size_le (2 ^ 33) _ ?_ ?_).imp fun e h => h.1
      · intro i hi
        simp only [Vector.toList_cast, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with hi | rfl
        · obtain ⟨eh, heh, hle⟩ := hq i hi
          exact ⟨eh, heh, by omega⟩
        · obtain ⟨e, he, hle, -⟩ := encode_bytes_exists_ok value (by omega)
          exact ⟨e, he, by omega⟩
      · simp

/-- The node composition on short paths and values gives a node that encodes. -/
private theorem patricializeAux_encodes (hash : ByteArray → Hash32) :
    (fuel : Nat) → (obj : List (List Nibble × ByteArray)) → (level : Nat) →
      (∀ entry ∈ obj, entry.1.length < 2 ^ 33 ∧ entry.2.size < 2 ^ 32) →
      ∃ node, patricializeAux hash fuel obj level = .ok node ∧
        ∃ e, encode (unencoded node) = .ok e
  | 0, obj, level, hobj => by
    rw [patricializeAux_zero]
    exact patricializeStep_encodes hash _
      (fun _ _ _ => ⟨none, rfl, (encode_bytes_succeeds_iff _).2 (by simp)⟩) obj level hobj
  | fuel + 1, obj, level, hobj => by
    rw [patricializeAux_add_one]
    exact patricializeStep_encodes hash _ (patricializeAux_encodes hash fuel) obj level hobj

/-- A map of short keys and values has a root exactly when no value is empty.

Each key and each value has fewer than `2^32` bytes, so no node reaches the limit of RLP. -/
theorem root_exists_ok_iff (hash : ByteArray → Hash32) (trie : Trie)
    (small : ∀ entry ∈ trie.data, entry.1.size < 2 ^ 32 ∧ entry.2.size < 2 ^ 32) :
    (∃ digest, root hash trie = .ok digest) ↔ ∀ entry ∈ trie.data, entry.2.size ≠ 0 := by
  constructor
  · rintro ⟨digest, h⟩ entry hmem hzero
    rw [root_emptyValue hash trie ⟨entry, hmem, hzero⟩] at h
    cases h
  · intro hne
    have hobj : ∀ entry ∈ trie.data.map fun (preimage, value) =>
        (keyPath hash trie.secured preimage, value),
        entry.1.length < 2 ^ 33 ∧ entry.2.size < 2 ^ 32 := by
      intro entry hmem
      obtain ⟨⟨k, v⟩, hkv, rfl⟩ := List.mem_map.1 hmem
      obtain ⟨hk, hv⟩ := small _ hkv
      simp only at hk hv
      refine ⟨?_, hv⟩
      show (keyPath hash trie.secured k).length < 2 ^ 33
      rw [keyPath_eq, length_bytesToNibbleList]
      cases trie.secured
      · simp only [Bool.false_eq_true, ↓reduceIte]
        omega
      · simp [ByteArray.size]
    obtain ⟨node, hnode, e, he⟩ := patricializeAux_encodes hash
      (longestPath (trie.data.map fun (preimage, value) =>
        (keyPath hash trie.secured preimage, value)) + 1) _ 0 hobj
    refine ⟨hash e, ?_⟩
    rw [← patricialize_eq] at hnode
    rw [root_eq, prepareData_ok hash trie.secured trie.data hne]
    simp [hnode, he, bind, Except.bind, Except.mapError, pure, Except.pure]

end EthLib.Execution.Trie

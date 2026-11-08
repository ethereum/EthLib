module

public import EthLib.Serialization.Rlp.Decode

/-!
# `Serialization.Proofs.Rlp.Loops`

The encoder and the decoder run their lists in loops that carry what they have built so far.

The theorems below give back the plain recursion on the first item, which the other proofs use.
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

/-- The loop from some encodings is the loop from none, after them. -/
theorem joinEncodingsFrom_eq (items : List Item) (out : ByteArray) :
    joinEncodingsFrom items out = (joinEncodingsFrom items .empty).map (out ++ ·) := by
  induction items generalizing out with
  | nil => simp [joinEncodingsFrom, Except.map]
  | cons item rest ih =>
    simp only [joinEncodingsFrom]
    cases encode item with
    | error e => rfl
    | ok head =>
      show joinEncodingsFrom rest (out ++ head) = (joinEncodingsFrom rest (.empty ++ head)).map _
      rw [ih, ih (.empty ++ head)]
      cases joinEncodingsFrom rest .empty <;>
        simp [Except.map, ByteArray.append_assoc]

/-- The encodings of a list are the loop from none. -/
theorem joinEncodings_eq (items : List Item) :
    joinEncodings items = joinEncodingsFrom items .empty := by
  cases items with
  | nil => rfl
  | cons item rest =>
    simp only [joinEncodings, joinEncodingsFrom]
    cases encode item with
    | error e => rfl
    | ok head =>
      show joinEncodingsFrom rest head = joinEncodingsFrom rest (.empty ++ head)
      rw [ByteArray.empty_append]

/-- The encodings of a list are the encoding of its first item, then those of the rest. -/
theorem joinEncodings_cons (item : Item) (rest : List Item) :
    joinEncodings (item :: rest) = do
      let head ← encode item
      let tail ← joinEncodings rest
      return head ++ tail := by
  simp only [joinEncodings]
  cases encode item with
  | error e => rfl
  | ok head =>
    show joinEncodingsFrom rest head = _
    rw [joinEncodingsFrom_eq, joinEncodings_eq]
    cases joinEncodingsFrom rest .empty <;> rfl

/-- The loop from some items read is the loop from none, after them. -/
theorem decodeItemsFrom_eq (input : ByteArray) (pos stop : Nat) (done : List Item) :
    decodeItemsFrom input pos stop done =
      (decodeItemsFrom input pos stop []).map (done.reverse ++ ·) := by
  rw [decodeItemsFrom, decodeItemsFrom]
  split
  · cases hd : decodeItem input pos stop with
    | error e => rfl
    | ok r =>
      obtain ⟨item, ⟨next, hNext⟩⟩ := r
      show decodeItemsFrom input next stop (item :: done) =
        (decodeItemsFrom input next stop [item]).map _
      rw [decodeItemsFrom_eq input next stop (item :: done),
        decodeItemsFrom_eq input next stop [item]]
      cases decodeItemsFrom input next stop [] <;> simp [Except.map]
  · simp [Except.map]
termination_by stop - pos
decreasing_by all_goals omega

/-- The items from `pos` to `stop`: none if no byte is left, else the first item, then the rest. -/
theorem decodeItems_eq (input : ByteArray) (pos stop : Nat) :
    decodeItems input pos stop =
      (if pos < stop then do
        let (item, ⟨next, _⟩) ← decodeItem input pos stop
        let items ← decodeItems input next stop
        .ok (item :: items)
      else
        .ok []) := by
  rw [decodeItems, decodeItemsFrom]
  split
  · cases decodeItem input pos stop with
    | error e => rfl
    | ok r =>
      obtain ⟨item, ⟨next, _⟩⟩ := r
      show decodeItemsFrom input next stop [item] =
        (do let items ← decodeItems input next stop; Except.ok (item :: items))
      rw [decodeItemsFrom_eq, decodeItems]
      cases decodeItemsFrom input next stop [] <;> rfl
  · rfl

end EthLib.Serialization.Rlp

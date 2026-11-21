module

public import EthLib.Serialization.Rlp.Decode

/-!
# `Serialization.Proofs.Rlp.Loops`

The encoder and the decoder run their lists in loops that carry what they have built so far.

The theorems below give back the plain recursion on the first item, which the other proofs use.

The decoder keeps its open lists on a list of its own, not on the native stack.

So the first theorems give back the recursion of one list inside another.
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

/-- The loop inside an outer list reads the inner list to its end, then goes on in the outer one.

The position must not be past the end of the inner list. -/
theorem decodeItemsLoop_cons (input : ByteArray) (pos : Nat) (current parent : OpenList input.size)
    (rest : List (OpenList input.size)) (inside : pos ≤ current.stop) :
    decodeItemsLoop input pos current (parent :: rest) =
      (decodeItemsLoop input pos current []).bind fun items =>
        decodeItemsLoop input current.stop
          { parent with done := .list items :: parent.done } rest := by
  rw [decodeItemsLoop.eq_def input pos current (parent :: rest),
    decodeItemsLoop.eq_def input pos current []]
  by_cases hPos : pos < current.stop
  · simp only [hPos, dite_true]
    cases hh : readHead input pos current.stop current.bounded with
    | error e => rfl
    | ok head =>
      cases head with
      | bytes value next after within =>
        exact decodeItemsLoop_cons input next _ parent rest within
      | list start next after ordered within =>
        -- The nested list closes first, inside both runs, then the run goes on at its end.
        simp only
        rw [decodeItemsLoop_cons input start _ current (parent :: rest) ordered,
          decodeItemsLoop_cons input start _ current [] ordered]
        cases decodeItemsLoop input start ⟨next, _, []⟩ [] with
        | error e => rfl
        | ok inner => exact decodeItemsLoop_cons input next _ parent rest within
  · -- The list ends here, so both runs give its items to the outer list.
    have hEnd : pos = current.stop := by omega
    simp only [hPos, dite_false, Except.bind]
    rw [hEnd]
termination_by input.size - pos
decreasing_by all_goals have := current.bounded; omega

/-- From `pos` to `stop`: the items so far if no byte is left, else one item, then the rest. -/
theorem decodeItemsFrom_unfold (input : ByteArray) (pos stop : Nat) (done : List Item)
    (bounded : stop ≤ input.size := by omega) :
    decodeItemsFrom input pos stop done =
      if pos < stop then do
        let (item, ⟨next, _⟩) ← decodeItem input pos stop
        decodeItemsFrom input next stop (item :: done)
      else
        .ok done.reverse := by
  unfold decodeItemsFrom
  rw [decodeItemsLoop]
  by_cases hPos : pos < stop
  · simp only [hPos, dite_true, ite_true]
    unfold decodeItem
    rcases readHead input pos stop bounded with e | head
    · rfl
    · cases head with
      | bytes value next after within => rfl
      | list start next after ordered within =>
        simp only
        rw [decodeItemsLoop_cons input start _ _ [] ordered]
        unfold decodeItems decodeItemsFrom
        cases decodeItemsLoop input start ⟨next, _, []⟩ [] <;> rfl
  · simp [hPos]

/-- One item read at `pos`: the decoder, written as one recursion with the items of a list. -/
theorem decodeItem_eq (input : ByteArray) (pos stop : Nat) (bounded : stop ≤ input.size) :
    decodeItem input pos stop =
      if hPos : pos < stop then
        let first := input[pos]'(by omega)
        if first < 0x80 then
          .ok (.bytes ⟨#[first]⟩, ⟨pos + 1, by omega, by omega⟩)
        else do
          let (kind, k, length) ← readPrefix input first (pos + 1) stop
          let start := pos + 1 + k
          if hFit : start + length ≤ stop then
            let next : { next : Nat // pos < next ∧ next ≤ stop } :=
              ⟨start + length, by omega, hFit⟩
            match kind with
            | .bytes =>
              if low : length = 1 ∧ ∃ inside : start < input.size, input[start] < 0x80 then
                .error (.singleByteWithPrefix (input[start]'low.2.1))
              else
                .ok (.bytes (input.extract start (start + length)), next)
            | .list =>
              let items ← decodeItems input start (start + length)
              .ok (.list items, next)
          else
            .error (.inputTooShort length (stop - start))
      else
        .error (.inputTooShort 1 0) := by
  unfold decodeItem readHead
  by_cases hPos : pos < stop
  · simp only [hPos, dite_true]
    by_cases hLow : input[pos] < 0x80
    · simp only [hLow, ite_true]
    · simp only [hLow, ite_false, bind, Except.bind]
      cases readPrefix input input[pos] (pos + 1) stop bounded with
      | error e => rfl
      | ok r =>
        obtain ⟨kind, k, length⟩ := r
        by_cases hFit : pos + 1 + k + length ≤ stop
        · cases kind
          · simp only [hFit, dite_true]
            by_cases low : length = 1 ∧ ∃ inside : pos + 1 + k < input.size,
                input[pos + 1 + k] < 0x80
            · simp only [low, and_self, dite_true]
            · simp only [low, dite_false]
          · simp only [hFit, dite_true]
            cases decodeItems input (pos + 1 + k) (pos + 1 + k + length) <;> rfl
        · simp only [hFit, dite_false]
  · simp only [hPos, dite_false]

/-- The loop from some items read is the loop from none, after them. -/
theorem decodeItemsFrom_eq (input : ByteArray) (pos stop : Nat) (done : List Item)
    (bounded : stop ≤ input.size := by omega) :
    decodeItemsFrom input pos stop done =
      (decodeItemsFrom input pos stop []).map (done.reverse ++ ·) := by
  rw [decodeItemsFrom_unfold input pos stop done bounded,
    decodeItemsFrom_unfold input pos stop [] bounded]
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
theorem decodeItems_eq (input : ByteArray) (pos stop : Nat)
    (bounded : stop ≤ input.size := by omega) :
    decodeItems input pos stop =
      (if pos < stop then do
        let (item, ⟨next, _⟩) ← decodeItem input pos stop
        let items ← decodeItems input next stop
        .ok (item :: items)
      else
        .ok []) := by
  rw [decodeItems, decodeItemsFrom_unfold input pos stop [] bounded]
  split
  · cases decodeItem input pos stop with
    | error e => rfl
    | ok r =>
      obtain ⟨item, ⟨next, _⟩⟩ := r
      show decodeItemsFrom input next stop [item] =
        (do let items ← decodeItems input next stop; Except.ok (item :: items))
      rw [decodeItemsFrom_eq input next stop [item] bounded, decodeItems]
      cases decodeItemsFrom input next stop [] <;> rfl
  · rfl

end EthLib.Serialization.Rlp

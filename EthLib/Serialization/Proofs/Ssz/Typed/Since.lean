module

public import EthLib.Base.Proofs.Fork
public import EthLib.Serialization.Ssz.Typed.Since
public import EthLib.Serialization.Proofs.Ssz.Typed.Container

/-!
# Proofs: fields that a fork adds or removes are lawful

Where it is present, a field converts as any field does, so its laws are those of its type.

Where it is absent, it adds no SSZ field and reads none, and its one value is the one read back.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Base SszType SszFields

/-- A field present when `p` holds, in front of lawful fields, is lawful. -/
theorem lawful_presentFieldsProd (p : Prop) [Decidable p] (α β : Type) [SszType α]
    [LawfulSszType α] [SszFields β] [LawfulSszFields β] :
    @LawfulSszFields ((p → α) × β) (presentFieldsProd p α β) := by
  refine @LawfulSszFields.mk _ (presentFieldsProd p α β) ?allWellFormed ?fits ?ofValues_toValues
    ?toValues_of_ofValues ?roots_eq ?ofValues_ne_error ?encodes_eq ?decodeSlots_check
    ?decodeSlots_read
  case ofValues_ne_error =>
    intro values fault count each
    by_cases present : p
    · match values, count, each with
      | [], count, _ => simp [descs, present] at count
      | value :: rest, count, each =>
        simp only [descs, ite_eq_left present, List.length_cons, List.zip_cons_cons, List.mem_cons,
          forall_eq_or_imp] at count each
        cases head : ofValue (α := α) value with
        | error other => exact absurd head (LawfulSszType.ofValue_ne_error each.1)
        | ok a =>
          cases tail : SszFields.ofValues (β := β) rest with
          | error other => exact absurd tail (LawfulSszFields.ofValues_ne_error (by omega) each.2)
          | ok b => simp [ofValues, present, head, tail, bind, Except.bind, pure, Except.pure]
    · simp only [descs, ite_eq_right present] at count each
      cases tail : SszFields.ofValues (β := β) values with
      | error other => exact absurd tail (LawfulSszFields.ofValues_ne_error count each)
      | ok b => simp [ofValues, present, tail, bind, Except.bind, pure, Except.pure]
  case encodes_eq =>
    intro pair
    by_cases present : p
    · simp only [encodes, descs, toValues, dite_eq_left present, ite_eq_left present,
        LawfulSszType.encode_eq, serializeFields_cons, LawfulSszFields.encodes_eq (β := β)]
      cases Ssz.serialize (desc α) (toValue (pair.1 present)) <;>
        cases serializeFields (descs β) (toValues pair.2) <;> rfl
    · simp only [encodes, descs, toValues, dite_eq_right present, ite_eq_right present,
        LawfulSszFields.encodes_eq (β := β)]
  case decodeSlots_check =>
    intro slots
    by_cases present : p
    · match slots with
      | .inline bytes :: slots =>
        have rest := LawfulSszFields.decodeSlots_check (β := β) slots
        rcases LawfulSszType.decode_cases (α := α) bytes with
          ⟨fault, read, dec⟩ | ⟨value, a, read, -, dec⟩
        · simp [decodeSlots, descs, present, checkInline, ByteSlot.toSlot, read, dec, bind,
            Except.bind, Functor.map, Except.map]
        · simp only [decodeSlots, descs, dite_eq_left present, ite_eq_left present, List.map_cons,
            ByteSlot.toSlot, checkInline, read, dec, bind, Except.bind, ← rest]
          cases SszFields.decodeSlots (β := β) slots <;> rfl
      | .body _ :: slots =>
        simp only [decodeSlots, descs, dite_eq_left present, ite_eq_left present, List.map_cons,
          ByteSlot.toSlot, checkInline, ← LawfulSszFields.decodeSlots_check (β := β) slots, bind,
          Except.bind]
        cases SszFields.decodeSlots (β := β) slots <;> rfl
      | [] => simp [decodeSlots, descs, present, checkInline, Functor.map, Except.map]
    · simp only [decodeSlots, descs, dite_eq_right present, ite_eq_right present,
        ← LawfulSszFields.decodeSlots_check (β := β) slots, bind, Except.bind]
      cases SszFields.decodeSlots (β := β) slots <;> rfl
  case decodeSlots_read =>
    intro slots read bodies made count starts
    by_cases present : p
    · match slots, made, count, starts with
      | .inline bytes :: slots, made, count, starts =>
        rcases LawfulSszType.decode_cases (α := α) bytes with
          ⟨fault, -, dec⟩ | ⟨value, a, read, conv, dec⟩
        · simp [decodeSlots, present, dec, bind, Except.bind] at made
        cases rest : SszFields.decodeSlots (β := β) slots with
        | error fault => simp [decodeSlots, present, dec, rest, bind, Except.bind] at made
        | ok reader =>
          simp only [decodeSlots, dite_eq_left present, dec, rest, bind, Except.bind, pure,
            Except.pure, Except.ok.injEq] at made
          subst made
          have tail := LawfulSszFields.decodeSlots_read bodies rest
            (by simpa [descs, present] using count) (by simpa [byteBodyStarts] using starts)
          simp only [descs, ite_eq_left present, fillSlots, deserializeFields, read, tail, ofValues,
            dite_eq_left present, bind, Except.bind, pure, Except.pure]
          rcases deserializeFields (descs β) (fillSlots slots bodies) with _ | values
          · rfl
          · cases others : SszFields.ofValues (β := β) values <;> simp [others, conv]
      | .body _ :: slots, made, count, starts =>
        cases rest : SszFields.decodeSlots (β := β) slots with
        | error fault => simp [decodeSlots, present, rest, bind, Except.bind] at made
        | ok reader =>
          simp only [decodeSlots, dite_eq_left present, rest, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at made
          subst made
          match bodies, starts with
          | [], starts => simp [byteBodyStarts] at starts
          | bytes :: bodies, starts =>
            have tail := LawfulSszFields.decodeSlots_read bodies rest
              (by simpa [descs, present] using count) (by simpa [byteBodyStarts] using starts)
            rcases LawfulSszType.decode_cases (α := α) bytes with
              ⟨fault, read, dec⟩ | ⟨value, a, read, conv, dec⟩
            · simp [descs, present, fillSlots, deserializeFields, read, dec, bind, Except.bind]
            · simp only [descs, ite_eq_left present, fillSlots, deserializeFields, read, dec, tail,
                ofValues, dite_eq_left present, bind, Except.bind, pure, Except.pure]
              rcases deserializeFields (descs β) (fillSlots slots bodies) with _ | values
              · rfl
              · cases others : SszFields.ofValues (β := β) values <;> simp [others, conv]
      | [], _, count, _ => simp [descs, present] at count
    · cases rest : SszFields.decodeSlots (β := β) slots with
      | error fault => simp [decodeSlots, present, rest, bind, Except.bind] at made
      | ok reader =>
        simp only [decodeSlots, dite_eq_right present, rest, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at made
        subst made
        have tail := LawfulSszFields.decodeSlots_read bodies rest
          (by simpa [descs, present] using count) starts
        simp only [descs, ite_eq_right present, tail, ofValues, dite_eq_right present, bind,
          Except.bind, pure, Except.pure]
        rcases deserializeFields (descs β) (fillSlots slots bodies) with _ | values
        · rfl
        · cases SszFields.ofValues (β := β) values <;> rfl
  case roots_eq =>
    intro pair
    by_cases present : p <;>
      simp [roots, descs, toValues, present, LawfulSszType.root_eq,
        LawfulSszFields.roots_eq (β := β)]
  case allWellFormed =>
    by_cases present : p <;>
      simp [descs, present, Desc.allWellFormed,
        LawfulSszType.wellFormed (α := α), LawfulSszFields.allWellFormed (β := β), bind,
        Except.bind]
  case fits =>
    intro pair
    obtain ⟨count, each⟩ := LawfulSszFields.fits pair.2
    by_cases present : p
    · refine ⟨by simp [descs, toValues, present, count], ?_⟩
      simp only [descs, toValues, present, ite_true, dite_true,
        List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨LawfulSszType.fits (pair.1 present), each⟩
    · simpa [descs, toValues, present] using And.intro count each
  case ofValues_toValues =>
    intro pair
    by_cases present : p
    · simp [toValues, ofValues, present, LawfulSszType.ofValue_toValue,
        LawfulSszFields.ofValues_toValues, bind, Except.bind, pure, Except.pure]
    · simp only [toValues, ofValues, present, dite_false,
        LawfulSszFields.ofValues_toValues, bind, Except.bind, pure, Except.pure]
      exact congrArg Except.ok (Prod.ext (funext fun h => absurd h present) rfl)
  case toValues_of_ofValues =>
    intro values pair read
    by_cases present : p
    · match values, read with
      | [], read => simp [ofValues, present] at read
      | value :: rest, read =>
        simp only [ofValues, present, dite_true, bind, Except.bind] at read
        cases head : ofValue (α := α) value with
        | error fault => simp [head] at read
        | ok field =>
          cases tail : SszFields.ofValues (β := β) rest with
          | error fault => simp [head, tail] at read
          | ok others =>
            simp only [head, tail, pure, Except.pure, Except.ok.injEq] at read
            subst read
            simp [toValues, present, LawfulSszType.toValue_of_ofValue head,
              LawfulSszFields.toValues_of_ofValues tail]
    · simp only [ofValues, present, dite_false, bind, Except.bind] at read
      cases tail : SszFields.ofValues (β := β) values with
      | error fault => simp [tail] at read
      | ok others =>
        simp only [tail, pure, Except.pure, Except.ok.injEq] at read
        subst read
        simp [toValues, present, LawfulSszFields.toValues_of_ofValues tail]

/-- A field present when `p` holds, as the last field of a container, is lawful. -/
theorem lawful_presentFields (p : Prop) [Decidable p] (α : Type) [SszType α]
    [LawfulSszType α] : @LawfulSszFields (p → α) (presentFields p α) := by
  refine @LawfulSszFields.mk _ (presentFields p α) ?allWellFormed ?fits ?ofValues_toValues
    ?toValues_of_ofValues ?roots_eq ?ofValues_ne_error ?encodes_eq ?decodeSlots_check
    ?decodeSlots_read
  case ofValues_ne_error =>
    intro values fault count each
    by_cases present : p
    · match values, count, each with
      | [value], _, each =>
        have fits := each (desc α, value) (by simp [descs, present])
        cases made : ofValue (α := α) value with
        | error other => exact absurd made (LawfulSszType.ofValue_ne_error fits)
        | ok a => simp [ofValues, present, made, Functor.map, Except.map]
      | [], count, _ | _ :: _ :: _, count, _ => simp [descs, present] at count
    · match values, count with
      | [], _ => simp [ofValues, present]
      | _ :: _, count => simp [descs, present] at count
  case encodes_eq =>
    intro field
    by_cases present : p
    · simp only [encodes, descs, toValues, dite_eq_left present, ite_eq_left present,
        LawfulSszType.encode_eq, serializeFields_cons, serializeFields_nil]
      cases Ssz.serialize (desc α) (toValue (field present)) <;> rfl
    · simp [encodes, descs, toValues, present, serializeFields_nil, pure, Except.pure,
        Functor.map, Except.map]
  case decodeSlots_check =>
    intro slots
    by_cases present : p
    · match slots with
      | .inline bytes :: _ =>
        rcases LawfulSszType.decode_cases (α := α) bytes with
          ⟨fault, read, dec⟩ | ⟨value, a, read, -, dec⟩ <;>
        simp [decodeSlots, descs, present, checkInline, ByteSlot.toSlot, read, dec, bind,
          Except.bind, Functor.map, Except.map, pure, Except.pure]
      | .body _ :: _ | [] =>
        simp [decodeSlots, descs, present, checkInline, ByteSlot.toSlot, Functor.map, Except.map]
    · simp [decodeSlots, descs, present, checkInline, Functor.map, Except.map]
  case decodeSlots_read =>
    intro slots read bodies made count starts
    by_cases present : p
    · match slots, made, count, starts with
      | [.inline bytes], made, _, starts =>
        obtain rfl : bodies = [] := List.eq_nil_of_length_eq_zero (by
          simpa [byteBodyStarts] using starts.symm)
        rcases LawfulSszType.decode_cases (α := α) bytes with
          ⟨fault, -, dec⟩ | ⟨value, a, read, conv, dec⟩
        · simp [decodeSlots, present, dec, bind, Except.bind] at made
        · simp only [decodeSlots, dite_eq_left present, dec, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at made
          subst made
          simp [descs, present, fillSlots, deserializeFields, read, ofValues, conv, bind,
            Except.bind, pure, Except.pure, Functor.map, Except.map]
      | [.body _], made, _, starts =>
        match bodies, starts with
        | [bytes], _ =>
          simp only [decodeSlots, dite_eq_left present, Except.ok.injEq] at made
          subst made
          rcases LawfulSszType.decode_cases (α := α) bytes with
            ⟨fault, read, dec⟩ | ⟨value, a, read, conv, dec⟩
          · simp [descs, present, fillSlots, deserializeFields, read, dec, bind, Except.bind,
              Functor.map, Except.map]
          · simp [descs, present, fillSlots, deserializeFields, read, dec, ofValues, conv, bind,
              Except.bind, pure, Except.pure, Functor.map, Except.map]
        | [], starts | _ :: _ :: _, starts => simp [byteBodyStarts] at starts
      | [], _, count, _ | _ :: _ :: _, _, count, _ => simp [descs, present] at count
    · match slots, made, count, starts with
      | [], made, _, starts =>
        obtain rfl : bodies = [] := List.eq_nil_of_length_eq_zero (by
          simpa [byteBodyStarts] using starts.symm)
        simp only [decodeSlots, dite_eq_right present, Except.ok.injEq] at made
        subst made
        simp [descs, present, fillSlots, deserializeFields, ofValues, bind, Except.bind]
      | _ :: _, _, count, _ => simp [descs, present] at count
  case roots_eq =>
    intro field
    by_cases present : p
    · simp only [roots, descs, toValues, present, dite_true, ite_true, LawfulSszType.root_eq,
        List.zip_cons_cons, List.zip_nil_right, List.mapM_cons, List.mapM_nil]
      cases Ssz.hashTreeRoot (desc α) (toValue (field present)) <;> rfl
    · simp [roots, descs, toValues, present, pure, Except.pure]
  case allWellFormed =>
    by_cases present : p <;>
      simp [descs, present, Desc.allWellFormed,
        LawfulSszType.wellFormed (α := α), bind, Except.bind]
  case fits =>
    intro field
    by_cases present : p
    · simpa [descs, toValues, present] using LawfulSszType.fits (field present)
    · simp [descs, toValues, present]
  case ofValues_toValues =>
    intro field
    by_cases present : p
    · simp [toValues, ofValues, present, LawfulSszType.ofValue_toValue,
        Functor.map, Except.map]
    · simp only [toValues, ofValues, present, dite_false]
      exact congrArg Except.ok (funext fun h => absurd h present)
  case toValues_of_ofValues =>
    intro values field read
    by_cases present : p
    · match values, read with
      | [value], read =>
        simp only [ofValues, present, dite_true] at read
        cases head : ofValue (α := α) value with
        | error fault => simp [head, Functor.map, Except.map] at read
        | ok item =>
          simp only [head, Functor.map, Except.map] at read
          obtain rfl := Except.ok.inj read
          simp [toValues, present, LawfulSszType.toValue_of_ofValue head]
      | [], read | _ :: _ :: _, read => simp [ofValues, present] at read
    · match values, read with
      | [], _ => simp [toValues, present]
      | _ :: _, read => simp [ofValues, present] at read

instance {first fork : Fork} {α β : Type} [SszType α] [LawfulSszType α] [SszFields β]
    [LawfulSszFields β] : LawfulSszFields (Since first fork α × β) :=
  lawful_presentFieldsProd (first ≤ fork) α β

instance {first fork : Fork} {α : Type} [SszType α] [LawfulSszType α] :
    LawfulSszFields (Since first fork α) :=
  lawful_presentFields (first ≤ fork) α

instance {last fork : Fork} {α β : Type} [SszType α] [LawfulSszType α] [SszFields β]
    [LawfulSszFields β] : LawfulSszFields (Until last fork α × β) :=
  lawful_presentFieldsProd (fork < last) α β

instance {last fork : Fork} {α : Type} [SszType α] [LawfulSszType α] :
    LawfulSszFields (Until last fork α) :=
  lawful_presentFields (fork < last) α

instance {first last fork : Fork} {α β : Type} [SszType α] [LawfulSszType α] [SszFields β]
    [LawfulSszFields β] : LawfulSszFields (During first last fork α × β) :=
  lawful_presentFieldsProd (first ≤ fork ∧ fork < last) α β

instance {first last fork : Fork} {α : Type} [SszType α] [LawfulSszType α] :
    LawfulSszFields (During first last fork α) :=
  lawful_presentFields (first ≤ fork ∧ fork < last) α

/-- Fields that appear at a fork keep their names distinct, when all their names are distinct. -/
theorem sinceNames_sublist {first fork : Fork} (names : List String) :
    (sinceNames first fork names).Sublist names := by
  unfold sinceNames
  split
  · exact List.Sublist.refl names
  · exact List.nil_sublist names

/-- Fields that a fork removes keep their names distinct, when all their names are distinct. -/
theorem untilNames_sublist {last fork : Fork} (names : List String) :
    (untilNames last fork names).Sublist names := by
  unfold untilNames
  split
  · exact List.Sublist.refl names
  · exact List.nil_sublist names

/-- Fields present between two forks keep their names distinct, when all their names are. -/
theorem duringNames_sublist {first last fork : Fork} (names : List String) :
    (duringNames first last fork names).Sublist names := by
  unfold duringNames
  split
  · exact List.Sublist.refl names
  · exact List.nil_sublist names

/-- From the fork that removes them, fields contribute no SSZ field. -/
theorem descs_until_of_not_lt {last fork : Fork} {α β : Type} [SszType α] [SszFields β]
    (h : ¬fork < last) : descs (Until last fork α × β) = descs β := by
  simp [descs, h]

/-- Before the fork that removes it, a field contributes one SSZ field of its type. -/
theorem descs_until_of_lt {last fork : Fork} {α β : Type} [SszType α] [SszFields β]
    (h : fork < last) : descs (Until last fork α × β) = desc α :: descs β := by
  simp [descs, h]

end EthLib.Serialization.Ssz

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
    ?toValues_of_ofValues
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
    ?toValues_of_ofValues
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

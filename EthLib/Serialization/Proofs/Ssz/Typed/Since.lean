module

public import EthLib.Base.Proofs.Fork
public import EthLib.Serialization.Ssz.Typed.Since
public import EthLib.Serialization.Proofs.Ssz.Typed.Container

/-!
# Proofs: fields that appear at a fork are lawful

From its fork on, a field converts as any field does, so its laws are those of its type.

Before its fork, it adds no SSZ field and reads none, and its one value is the one read back.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Base SszType SszFields

variable {first fork : Fork}

instance {α β : Type} [SszType α] [LawfulSszType α] [SszFields β] [LawfulSszFields β] :
    LawfulSszFields (Since first fork α × β) where
  allWellFormed := by
    by_cases present : first ≤ fork <;>
      simp [descs, present, Desc.allWellFormed, LawfulSszType.wellFormed (α := α),
        LawfulSszFields.allWellFormed (β := β), bind, Except.bind]
  fits pair := by
    obtain ⟨count, each⟩ := LawfulSszFields.fits pair.2
    by_cases present : first ≤ fork
    · refine ⟨by simp [descs, toValues, present, count], ?_⟩
      simp only [descs, toValues, present, ite_true, dite_true, List.zip_cons_cons,
        List.mem_cons, forall_eq_or_imp]
      exact ⟨LawfulSszType.fits (pair.1 present), each⟩
    · simpa [descs, toValues, present] using And.intro count each
  ofValues_toValues pair := by
    by_cases present : first ≤ fork
    · simp [toValues, ofValues, present, LawfulSszType.ofValue_toValue,
        LawfulSszFields.ofValues_toValues, bind, Except.bind, pure, Except.pure]
    · simp only [toValues, ofValues, present, dite_false, LawfulSszFields.ofValues_toValues,
        bind, Except.bind, pure, Except.pure]
      exact congrArg Except.ok (Prod.ext (Since.eq_of_not_le present _ _) rfl)
  toValues_of_ofValues {values pair} read := by
    by_cases present : first ≤ fork
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

instance {α : Type} [SszType α] [LawfulSszType α] : LawfulSszFields (Since first fork α) where
  allWellFormed := by
    by_cases present : first ≤ fork <;>
      simp [descs, present, Desc.allWellFormed, LawfulSszType.wellFormed (α := α), bind,
        Except.bind]
  fits field := by
    by_cases present : first ≤ fork
    · simpa [descs, toValues, present] using LawfulSszType.fits (field present)
    · simp [descs, toValues, present]
  ofValues_toValues field := by
    by_cases present : first ≤ fork
    · simp [toValues, ofValues, present, LawfulSszType.ofValue_toValue, Functor.map,
        Except.map]
    · simp only [toValues, ofValues, present, dite_false]
      exact congrArg Except.ok (Since.eq_of_not_le present _ _)
  toValues_of_ofValues {values field} read := by
    by_cases present : first ≤ fork
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

/-- Fields that appear at a fork keep their names distinct, when all their names are distinct. -/
theorem sinceNames_sublist (names : List String) : (sinceNames first fork names).Sublist names := by
  unfold sinceNames
  split
  · exact List.Sublist.refl names
  · exact List.nil_sublist names

end EthLib.Serialization.Ssz

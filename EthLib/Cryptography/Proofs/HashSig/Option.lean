module

public import EthLib.Cryptography.HashSig

/-!
# Entries of a successful optional collection

The actual in-order collector returns the value computed at every index.

Success supplies those values without a default or a nonempty value type.
-/

public section

namespace EthLib.Cryptography.HashSig

/-- Every entry of a successful collection is the actual result at that index. -/
theorem ofFnInOrder_eq_some_get {α : Type} :
    ∀ (n : Nat) (f : Fin n → Option α) (values : Vector α n),
      HashSig.ofFnInOrder n f = some values → ∀ i : Fin n, f i = some values[i] := by
  intro n
  induction n with
  | zero => intro f values completed i; exact Fin.elim0 i
  | succ n ih =>
    intro f values completed
    rw [HashSig.ofFnInOrder] at completed
    obtain ⟨head, headRun, rest⟩ := Option.bind_eq_some_iff.mp completed
    obtain ⟨tail, tailRun, same⟩ := Option.bind_eq_some_iff.mp rest
    have returned : (#v[head] ++ tail).cast (Nat.add_comm 1 n) = values := Option.some.inj same
    subst values
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using headRun
    · simpa using ih (fun j => f j.succ) tail tailRun j

end EthLib.Cryptography.HashSig

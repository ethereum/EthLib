module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchReserve

/-!
# Physical counts at live and frozen signing keys

Stopping a key's count at its first search is a decision made before any new reply.

A fresh word at a live key adds one trial and tests that same word for validity.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest

open HashSig OracleComp OracleSpec CachedCodeword PostSigning
open scoped Classical

noncomputable def initialCount (keys : Finset Key) (f : Key → Entry → Nat)
    (saved : Snapshots) (s : Entry) : Nat := ∑ k ∈ keys, f k (entry saved k s)

/-- An attempted search preserves the totals, including for keys already booked. -/
theorem initialCount_begin (keys : Finset Key) (f : Key → Entry → Nat) (saved : Snapshots)
    (k : Key) (s : Entry) : initialCount keys f (begin saved k s) s
      = initialCount keys f saved s := by
  simp only [initialCount, entry_begin]

/-- A fresh word adds one physical trial and, when accepted, one valid word at its own live key.

Neither count changes after a key's first attempted search.
-/
theorem initialCount_probe (pp : PublicParam) (keys : Finset Key) (saved : Snapshots) (s : Entry)
    (a : HashInput) (k : Key) (atKey : messageKey pp a = some k) (cold : s.1 a = none)
    (fresh : a ∉ s.2) (w : HashOutput) :
    let after : Entry := (s.1.cacheQuery a w, insert a s.2)
    let active := k ∈ keys ∧ saved k = none
    initialCount keys (inputCount pp) saved after = initialCount keys (inputCount pp) saved s +
      (if active then 1 else 0) ∧
    initialCount keys (validCount pp) saved after = initialCount keys (validCount pp) saved s +
      (if active ∧ w ∈ accepted then 1 else 0) := by
  classical
  intro after active
  let n := inputCount pp
  let v := validCount pp
  have own : n k after = n k s + 1 := by
    have shape : inputsAtKey pp k.1 k.2 after.2 = insert a (inputsAtKey pp k.1 k.2 s.2) := by
      ext b
      by_cases e : b = a <;> simp_all [after, inputsAtKey]
    have new : a ∉ inputsAtKey pp k.1 k.2 s.2 := by simp [inputsAtKey, fresh]
    exact (congrArg Finset.card shape).trans (Finset.card_insert_of_notMem new)
  have ok : v k after = v k s + (if w ∈ accepted then 1 else 0) := by
    change (validInputs pp k.1 k.2 _ _).card = _
    rw [validInputs_after pp k.1 k.2 s.1 s.2 a atKey cold w]
    by_cases good : w ∈ accepted <;> simp [good, v, validCount]
  have other (j : Key) (ne : j ≠ k) : n j after = n j s ∧ v j after = v j s := by
    have foreign : messageKey pp a ≠ some j := by simpa [atKey] using Ne.symm ne
    constructor
    · apply congrArg Finset.card
      ext b
      by_cases eq : b = a <;> simp_all [n, inputCount, inputsAtKey, after]
    · have eq := foreign_probe pp j.1 j.2 0 0 (by decide) s.1 s.2 a foreign cold w
      exact congrArg Finset.card eq.1
  have sum (f : Key → Entry → Nat) (inc : Nat) (self : f k after = f k s + inc)
      (away : ∀ j, j ≠ k → f j after = f j s) :
      initialCount keys f saved after
        = initialCount keys f saved s + (if active then inc else 0) := by
    have row (j : Key) :
        f j (entry saved j after) = f j (entry saved j s) +
          (if j = k ∧ saved k = none then inc else 0) := by
      by_cases same : j = k
      · subst j
        cases held : saved k <;> simp [entry, held, self]
      · cases held : saved j <;> simp [entry, held, same, away j same]
    simp only [initialCount, row, Finset.sum_add_distrib]
    by_cases held : saved k = none <;> simp [active, held, Finset.sum_ite_eq']
  refine ⟨sum n 1 own (fun j hj => (other j hj).1), ?_⟩
  rw [sum v _ ok (fun j hj => (other j hj).2)]
  by_cases live : active <;> simp [live, v]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest

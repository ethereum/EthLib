module

public import EthLib.Cryptography.Proofs.Wots

/-!
# Proofs: a chain walked to an honest value binds its start

A walk up a hash chain that ends at an honest chain value started at the honest value.

Otherwise some step maps a value that is not honest to the next honest value.

When the honest values form a chain, that step is a second preimage under the step at its position.

The binding itself holds for any honest values, chain or not.

A real step compresses, so second preimages exist.

So the theorem names a search that returns one, and does not just assert one exists.

- The search walks the chain from its start, one position at a time.
- It returns the first position where a value that is not honest steps to the next honest value.
- The honest walk runs into no such position.

In WOTS+C, a signature reveals chain `i` at its digit `x_i`, and hides every value below.

A forgery whose digit is lower walks up from that lower position.

If it reaches the honest end, it starts at a hidden value, or it hits a second preimage.

The statements hold for every step function, run in the identity monad.

leanXMSS and leanSPHINCS both walk their chains with it.
-/

@[expose] public section

namespace EthLib.Cryptography.Wots

variable {α : Type} {n : Nat} (step : Fin n → α → Id α)

/-! ## The honest chain -/

/-- The honest value at position `k` of the chain that starts at `c` at position 0.

Above the last position, the value stays at the end. -/
def honestValue (c : α) : Nat → α
  | 0 => c
  | k + 1 => if hk : k < n then (step ⟨k, hk⟩ (honestValue c k)).run else honestValue c k

/-- The honest value one position up is the step of the honest value. -/
theorem honestValue_succ (c : α) {k : Nat} (hk : k < n) :
    honestValue step c (k + 1) = (step ⟨k, hk⟩ (honestValue step c k)).run := by
  simp only [honestValue, hk, ↓reduceDIte]

/-- A walk of `s + 1` steps is one step, then a walk of `s` steps from the next position. -/
theorem chain_succ_run (start : Nat) :
    ∀ (s : Nat) (h : start + (s + 1) ≤ n) (b : α), (chain step start (s + 1) h b).run
      = (chain step (start + 1) s (by omega) (step ⟨start, by omega⟩ b).run).run
  | 0, _, _ => rfl
  | s + 1, h, b => by
    rw [chain_succ, Id.run_bind, chain_succ_run start s (by omega) b, chain_succ, Id.run_bind]
    -- The last step leaves `start + (s + 1)`, the same as `start + 1 + s`.
    have hpos : (⟨start + (s + 1), by omega⟩ : Fin n) = ⟨start + 1 + s, by omega⟩ :=
      Fin.ext (show start + (s + 1) = start + 1 + s by omega)
    rw [hpos]

/-- A walk from the honest value at `start` reaches the honest value `steps` positions up. -/
theorem chain_honestValue (c : α) :
    ∀ (steps start : Nat) (h : start + steps ≤ n),
      (chain step start steps h (honestValue step c start)).run
        = honestValue step c (start + steps)
  | 0, _, _ => rfl
  | s + 1, start, h => by
    rw [chain_succ_run, ← honestValue_succ step c (by omega), chain_honestValue c s (start + 1),
      show start + 1 + s = start + (s + 1) by omega]

/-! ## The search -/

/-- A value offered at position `pos` in place of the honest one. -/
structure ChainPreimage (α : Type) where
  /-- The position of the value on the chain. -/
  pos : Nat
  /-- The value offered there. -/
  value : α

/-- The value is not honest, and the step at its position maps it to the next honest value.

`honest` gives the honest value at each position. -/
def ChainPreimage.Valid (honest : Nat → α) (w : ChainPreimage α) : Prop :=
  ∃ h : w.pos < n, w.value ≠ honest w.pos ∧ (step ⟨w.pos, h⟩ w.value).run = honest (w.pos + 1)

/-- The second preimage a walk from position `start` runs into, at the lowest position.

At each position, the walk applies the step to its value.

A position whose value is not honest, but whose next value is, is a second preimage. -/
def findChainPreimage [DecidableEq α] (honest : Nat → α) :
    (start steps : Nat) → start + steps ≤ n → α → Option (ChainPreimage α)
  | _, 0, _, _ => none
  | start, s + 1, h, b =>
    let next := (step ⟨start, by omega⟩ b).run
    if b ≠ honest start ∧ next = honest (start + 1) then some ⟨start, b⟩
    else findChainPreimage honest (start + 1) s (by omega) next

/-- Every second preimage the search returns is valid, `k` positions above the start.

Its value is the one the walk holds there, after `k` steps, so the walk hashes it. -/
theorem findChainPreimage_valid [DecidableEq α] (honest : Nat → α) :
    ∀ (steps start : Nat) (h : start + steps ≤ n) (b : α) (w : ChainPreimage α),
      findChainPreimage step honest start steps h b = some w →
      w.Valid step honest ∧ ∃ k, ∃ hk : k < steps, w.pos = start + k ∧
        w.value = (chain step start k (by omega) b).run := by
  intro steps
  induction steps with
  | zero => intro start h b w hw; simp [findChainPreimage] at hw
  | succ s ih =>
    intro start h b w hw
    simp only [findChainPreimage] at hw
    split at hw
    · -- This position is the second preimage.
      rename_i hfound
      cases hw
      exact ⟨⟨show start < n by omega, hfound⟩, 0, Nat.succ_pos _, rfl, rfl⟩
    · -- The second preimage is further up: one step later in the count.
      obtain ⟨hvalid, k, hk, hpos, hvalue⟩ := ih (start + 1) (by omega) _ w hw
      refine ⟨hvalid, k + 1, by omega, by omega, ?_⟩
      rw [hvalue, chain_succ_run]

/-- The honest walk runs into no second preimage. -/
theorem findChainPreimage_honest [DecidableEq α] (c : α) :
    ∀ (steps start : Nat) (h : start + steps ≤ n),
      findChainPreimage step (honestValue step c) start steps h (honestValue step c start)
        = none := by
  intro steps
  induction steps with
  | zero => intro start h; rfl
  | succ s ih =>
    intro start h
    simp only [findChainPreimage, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    rw [← honestValue_succ step c (by omega)]
    exact ih (start + 1) (by omega)

/-! ## Binding -/

/-- Binding: a walk that reaches the honest value `steps` positions up started at the honest value.

Otherwise the search finds a second preimage, valid by `findChainPreimage_valid`. -/
theorem chain_binding [DecidableEq α] (honest : Nat → α) :
    ∀ (steps start : Nat) (h : start + steps ≤ n) (b : α),
      (chain step start steps h b).run = honest (start + steps) →
      b = honest start ∨ (findChainPreimage step honest start steps h b).isSome := by
  intro steps
  induction steps with
  | zero => intro start h b hb; exact .inl hb
  | succ s ih =>
    intro start h b hb
    rw [chain_succ_run, show start + (s + 1) = start + 1 + s by omega] at hb
    simp only [findChainPreimage]
    -- When this position is a second preimage, the search stops here.
    by_cases hfound : b ≠ honest start ∧ (step ⟨start, by omega⟩ b).run = honest (start + 1)
    · exact .inr (by simp [hfound])
    simp only [hfound, ↓reduceIte]
    rcases ih (start + 1) (by omega) _ hb with hnext | hsome
    · -- The next value is honest and no second preimage is here: this value is honest.
      exact .inl (Classical.byContradiction fun hne => hfound ⟨hne, hnext⟩)
    · exact .inr hsome

end EthLib.Cryptography.Wots

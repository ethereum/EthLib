module

/-!
# Hash chains and the codeword search of WOTS+C

leanXMSS and leanSPHINCS both sign with WOTS+C, and they share its two loops.

A chain applies a step function once per position, from a start position upward.

The search tries trials one by one and keeps the first that gives a codeword.

Each scheme supplies its own step, trials and test.

Source: [ePrint 2022/778](https://eprint.iacr.org/2022/778) for WOTS+C.

The chain is Construction 2 of [ePrint 2025/055][hbms], §4.2.

The search is step 3 of the signing of Construction 3 in the same paper.

[hbms]: https://eprint.iacr.org/2025/055
-/

@[expose] public section

namespace EthLib.Cryptography.Wots

variable {m : Type → Type} [Monad m]

/-- Walk a chain for `steps` steps, from position `start`, with `step` at each position.

The step from position `k` gets `k`, so a scheme can put it in the hash address.

A chain of `n + 1` positions has `n` steps, and the bound keeps the walk on the chain. -/
def chain {α : Type} {n : Nat} (step : Fin n → α → m α) (start : Nat) :
    (steps : Nat) → start + steps ≤ n → α → m α
  -- Construction 2, steps 1 and 2: `y := x`, and `y` is the result when `s = 0`.
  | 0, _, value => pure value
  -- Step 3: for each `j ∈ [s]`, `y := Th(P, tweak(ep, i, k + j), y)`, with `k` the start.
  --
  -- The step that reaches position `k + j` gets index `k + j - 1`.
  --
  -- The last step leaves position `start + s`, having walked `s` before it.
  | s + 1, h, value => do
    let previous ← chain step start s (by omega) value
    step ⟨start + s, by omega⟩ previous

/-- Try the trials from `c` onward, at most `fuel` of them.

Returns the first trial whose test gives a codeword, with the codeword. -/
@[specialize] def findFirst {κ β : Type} (trial : Nat → κ) (test : κ → m (Option β)) (c : Nat) :
    (fuel : Nat) → m (Option (κ × β))
  -- Construction 3, signing step 3: while `ctr < K` and `x = ⊥`, with `fuel` trials left.
  | 0 => pure none
  | fuel + 1 => do
    -- Step 3a: the next trial, derived from a counter rather than sampled at random.
    let k := trial c
    match ← test k with
    -- The least admissible trial wins.
    | some x => pure (some (k, x))
    -- Otherwise move on to the next trial.
    | none => findFirst trial test (c + 1) fuel

end EthLib.Cryptography.Wots

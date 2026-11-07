module

public import EthLib.Execution.Proofs.Evm.Logic.Triple

/-!
# Proofs: loops

A loop runs its body until a condition fails.

A proof of a loop gives an invariant for each value of a measure, a natural number.

Each run of the body goes from the invariant at `k + 1` to the invariant at `k`.

The exit goes from the invariant at `0` to the postcondition.

So the loop reaches the postcondition from the invariant at any `n`, by induction on `n`.

This is total correctness: the measure, not the gas, bounds the number of runs of the body.

A loop whose body pays a price per run can carry the gas in its invariant.

Its gas is then the sum of the prices of the runs and the price of the exit.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type}

namespace Triple

variable {S : Evm fork Meter → Evm fork Meter → Prop}

/-- A loop whose body may lower the measure by more than one. -/
theorem loop_lt {I : Nat → Evm fork Meter → Prop} {Q : Evm fork Meter → Prop}
    (body : ∀ k, Triple S (I (k + 1)) fun evm => ∃ j < k + 1, I j evm)
    (exit : Triple S (I 0) Q) (n : Nat) : Triple S (I n) Q := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => exact exit
    | succ k =>
      intro evm hp
      obtain ⟨mid, hreach, j, hj, hi⟩ := body k evm hp
      obtain ⟨after, hreach', hq⟩ := ih j hj mid hi
      exact ⟨after, hreach.trans hreach', hq⟩

/-- A loop: each run of the body lowers the measure by one, and the exit ends it at 0. -/
theorem loop {I : Nat → Evm fork Meter → Prop} {Q : Evm fork Meter → Prop}
    (body : ∀ k, Triple S (I (k + 1)) (I k)) (exit : Triple S (I 0) Q) (n : Nat) :
    Triple S (I n) Q :=
  loop_lt (fun k => (body k).consequence (fun _ h => h) fun _ h => ⟨k, Nat.lt_succ_self k, h⟩)
    exit n

/-- The gas that `n` runs of a body take.

The run that starts with `k + 1` runs left costs `cost k`. -/
def loopCost (cost : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => cost k + loopCost cost k

/-- A loop whose body pays a price that depends on the runs left, with the gas in the invariant.

The invariant `I k g` holds at the head of the loop with `k` runs left and `g` gas.

A run of the body with `k + 1` runs left pays `cost k`, and the exit pays `exitCost`.

From the head with `n` runs left and enough gas, the loop reaches the postcondition.

The postcondition gets the gas left after every run and the exit. -/
theorem loop_gas {I : Nat → Nat → Evm fork Meter → Prop} {Q : Nat → Evm fork Meter → Prop}
    {cost : Nat → Nat} {exitCost : Nat}
    (body : ∀ k g, cost k ≤ g → Triple S (I (k + 1) g) (I k (g - cost k)))
    (exit : ∀ g, exitCost ≤ g → Triple S (I 0 g) (Q (g - exitCost))) (n : Nat) (g : Nat)
    (hgas : loopCost cost n + exitCost ≤ g) :
    Triple S (I n g) (Q (g - (loopCost cost n + exitCost))) := by
  induction n generalizing g with
  | zero =>
    simp only [loopCost, Nat.zero_add] at hgas ⊢
    exact exit g hgas
  | succ k ih =>
    simp only [loopCost] at hgas ⊢
    have h := ih (g - cost k) (by omega)
    rw [show g - cost k - (loopCost cost k + exitCost) =
      g - (cost k + loopCost cost k + exitCost) by omega] at h
    exact (body k g (by omega)).seq h

end Triple

end EthLib.Execution.Evm.Logic

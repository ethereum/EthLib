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

end Triple

end EthLib.Execution.Evm.Logic

module

public import EthLib.Execution.Proofs.Evm.Logic.Known

/-!
# Proofs: a contract that writes two words in reverse order and returns both

This example proves code that writes the higher word of memory first, with frames that know ranges.

The bytecode `0x6002602052600160005260406000f3` returns the words 1 and 2, in that order.

- At 0, `60 02 60 20 52` writes the word 2 at offset 32.
- At 5, `60 01 60 00 52` writes the word 1 at offset 0.
- At 10, `60 40 60 00 f3` returns the 64 bytes from offset 0.

The second write keeps the fact of the first, since their ranges are apart.

The two facts then join into the fact of the 64 bytes.

The code costs 30 gas.

Six pushes and two stores cost 3 each, and the growth of memory to two words costs 6.

It halts normally, returns the two words, and keeps its state and substate.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.Pair

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- The bytecode: write 2 at offset 32, then 1 at offset 0, then return the 64 bytes. -/
def CODE : ByteArray := ⟨#[0x60, 0x02, 0x60, 0x20, 0x52, 0x60, 0x01, 0x60, 0x00, 0x52, 0x60,
  0x40, 0x60, 0x00, 0xf3]⟩

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- Memory grows from nothing to two words for the write at offset 32, for 6 gas. -/
theorem extendMemory_high : extendMemory 0 [((32 : U256), (32 : U256))] = ⟨6, 64⟩ := by
  decide

/-- The write at offset 0 falls within the two words, so memory does not grow. -/
theorem extendMemory_low : extendMemory 64 [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
  decide

/-- The specification: with at least 30 gas, the code returns the words 1 and 2, in that order. -/
theorem spec {gas : Nat} (hgas : 30 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 1 ++ wordBytes 2) (gas - 30) state substate) := by
  have h1 := Known.of_at (size := 0) (facts := []) fun memory =>
    push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 0) (stack := []) (memory := memory) (gas := gas)
      (byte := 0x02) (by decide) rfl rfl (by omega) (by decide)
  have h2 := Known.of_at (size := 0) (facts := []) fun memory =>
    push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 2) (stack := [2]) (memory := memory) (gas := gas - 3)
      (byte := 0x20) (by decide) rfl rfl (by omega) (by decide)
  have h3 := mstore_known (fork := fork) (code := CODE) (message := message) (pc := 4)
    (size := 0) (facts := []) (gas := gas - 3 - 3) (state := state) (substate := substate)
    (start := 32) (value := 2) (rest := []) (by decide) rfl
    (by rw [extendMemory_high]; dsimp only; omega)
  rw [extendMemory_high] at h3
  dsimp only at h3
  rw [List.filter_nil] at h3
  have h4 := Known.of_at (size := 0 + 64) (facts := [((32 : U256).toNat, wordBytes 2)])
    fun memory =>
    push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 5) (stack := []) (memory := memory)
      (gas := gas - 3 - 3 - (3 + 6))
      (byte := 0x01) (by decide) rfl rfl (by omega) (by decide)
  have h5 := Known.of_at (size := 0 + 64) (facts := [((32 : U256).toNat, wordBytes 2)])
    fun memory =>
    push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 7) (stack := [1]) (memory := memory)
      (gas := gas - 3 - 3 - (3 + 6) - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h6 := mstore_known (fork := fork) (code := CODE) (message := message) (pc := 9)
    (size := 0 + 64) (facts := [((32 : U256).toNat, wordBytes 2)])
    (gas := gas - 3 - 3 - (3 + 6) - 3 - 3) (state := state) (substate := substate)
    (start := 0) (value := 1) (rest := []) (by decide) rfl
    (by rw [Nat.zero_add, extendMemory_low]; dsimp only; omega)
  rw [Nat.zero_add, extendMemory_low] at h6
  dsimp only at h6
  -- The fact of the word 2 is apart from the range of the second write, so it stays.
  have hkeep : [((32 : U256).toNat, wordBytes 2)].filter (Apart (0 : U256).toNat 32) =
      [((32 : U256).toNat, wordBytes 2)] := by
    simp [Apart, size_wordBytes]
  rw [hkeep] at h6
  have h7 := Known.of_at (size := 64 + 0)
    (facts := [((0 : U256).toNat, wordBytes 1), ((32 : U256).toNat, wordBytes 2)]) fun memory =>
    push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 10) (stack := []) (memory := memory)
      (gas := gas - 3 - 3 - (3 + 6) - 3 - 3 - (3 + 0)) (byte := 0x40) (by decide) rfl rfl
      (by omega) (by decide)
  have h8 := Known.of_at (size := 64 + 0)
    (facts := [((0 : U256).toNat, wordBytes 1), ((32 : U256).toNat, wordBytes 2)]) fun memory =>
    push1 (code := CODE) (fork := fork) (message := message) (state := state)
      (substate := substate) (pc := 12) (stack := [64]) (memory := memory)
      (gas := gas - 3 - 3 - (3 + 6) - 3 - 3 - (3 + 0) - 3) (byte := 0x00) (by decide) rfl rfl
      (by omega) (by decide)
  have h9 := return_known (fork := fork) (code := CODE) (message := message) (pc := 14)
    (size := 64 + 0)
    (facts := ((0 : U256).toNat, wordBytes 1 ++ wordBytes 2) ::
      [((0 : U256).toNat, wordBytes 1), ((32 : U256).toNat, wordBytes 2)])
    (gas := gas - 3 - 3 - (3 + 6) - 3 - 3 - (3 + 0) - 3 - 3) (state := state)
    (substate := substate) (start := 0) (length := 64) (out := wordBytes 1 ++ wordBytes 2)
    (rest := []) (by decide) rfl (List.mem_cons_self ..)
    (by rw [ByteArray.size_append, size_wordBytes, size_wordBytes]; rfl)
  have hg : gas - 3 - 3 - (3 + 6) - 3 - 3 - (3 + 0) - 3 - 3 = gas - 30 := by omega
  rw [hg] at h9
  refine Spec.seq (P := At CODE message 0 [] .empty gas state substate) ?_ h9
  intro evm hat
  obtain ⟨mid, hreach, hmid⟩ :=
    (((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8) evm (known_of_at_empty hat)
  exact ⟨mid, hreach, hmid.join (List.mem_cons_self ..)
    (by rw [size_wordBytes]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

/-- The loop of the interpreter runs the code to its specification.

It holds for every bound on the gas of messages and every runner of messages.

The code sends no message. -/
theorem runFrame_spec {gas : Nat} (hgas : 30 ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted false (wordBytes 1 ++ wordBytes 2) (gas - 30) state substate stopped :=
  (spec hgas).runFrame start within

end EthLib.Execution.Evm.Logic.Pair

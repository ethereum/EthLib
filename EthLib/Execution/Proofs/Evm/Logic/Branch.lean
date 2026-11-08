module

public import EthLib.Execution.Proofs.Evm.Logic.Rules

/-!
# Proofs: a rule for a table of keys that branches on the top word of the stack

A table of entries in a code compares the top word of the stack with a key in each entry.

Each entry is DUP1, a push of its key, EQ, a push of its destination, and JUMPI.

The key takes `n` bytes and the destination `m` bytes, from 1 to 32 each, in every entry.

An entry then takes `n + m + 5` bytes of code.

The run jumps to the destination of the first entry whose key is the word.

When no key is the word, the run goes on past the table.

Each entry that the run tests costs 22 gas, at every fork with the one-counter meter.

The stack keeps the word, and memory, the state and the substate stay as they are.

Each destination must be a valid destination of a jump, and the stack must have room for two words.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- The code holds the byte `b` at the index `i`. -/
def ByteAt (code : ByteArray) (i : Nat) (b : UInt8) : Prop := ∃ h : i < code.size, code[i] = b

/-- The size of an entry: DUP1, the push of its key, EQ, the push of its destination, JUMPI. -/
abbrev entrySize (n m : Fin 33) : Nat := 1 + (1 + n) + 1 + (1 + m) + 1

/-- A table of entries in the code from `pc`, each with a key of `n` bytes and a destination of `m`.

Each destination is a valid destination of a jump. -/
def Table (code : ByteArray) (n m : Fin 33) : Nat → List (U256 × U256) → Prop
  | _, [] => True
  | pc, (key, dest) :: entries =>
    ByteAt code pc 0x80 ∧ ByteAt code (pc + 1) (0x5f + UInt8.ofNat n.val) ∧
      pushData code (pc + 1) n = key ∧ ByteAt code (pc + 1 + (1 + n)) 0x14 ∧
      ByteAt code (pc + 1 + (1 + n) + 1) (0x5f + UInt8.ofNat m.val) ∧
      pushData code (pc + 1 + (1 + n) + 1) m = dest ∧
      ByteAt code (pc + 1 + (1 + n) + 1 + (1 + m)) 0x57 ∧
      isValidJumpDest (validJumpDestinations code) dest.toNat = true ∧
      Table code n m (pc + entrySize n m) entries

/-- The number of entries that the run tests for the word `x`: up to the first with key `x`. -/
def tested (x : U256) : List (U256 × U256) → Nat
  | [] => 0
  | (key, _) :: entries => if key = x then 1 else tested x entries + 1

/-- Where the run goes for the word `x`, from a table at `pc` with entries of `size` bytes.

That is the destination of the first entry with key `x`, or the end of the table. -/
def branch (x : U256) (pc size : Nat) : List (U256 × U256) → Nat
  | [] => pc
  | (key, dest) :: entries => if key = x then dest.toNat else branch x (pc + size) size entries

variable {code : ByteArray} {message : Message fork} {memory : ByteArray}
  {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- A table of keys sends the word `x` to the destination of the first entry with key `x`.

When no key is `x`, the run goes on past the table.

It pays 22 gas for each entry it tests, and keeps the word on the stack. -/
theorem branchTable {n m : Fin 33} (hn : n.val ≠ 0) (hm : m.val ≠ 0) {x : U256}
    {rest : List U256} (hstack : rest.length + 2 < STACK_LIMIT) :
    ∀ {pc gas : Nat} {entries : List (U256 × U256)}, Table code n m pc entries →
      22 * tested x entries ≤ gas →
      Hoare fork (At code message pc (x :: rest) memory gas state substate returnData)
        (At code message (branch x pc (entrySize n m) entries) (x :: rest) memory
          (gas - 22 * tested x entries) state substate returnData)
  | pc, gas, [], _, _ => Triple.of_imp fun _ h => h
  | pc, gas, (key, dest) :: entries, ⟨⟨l0, b0⟩, ⟨l1, b1⟩, hkey, ⟨l2, b2⟩, ⟨l3, b3⟩, hdest,
      ⟨l4, b4⟩, valid, table⟩, hgas => by
    have h22 : 22 ≤ gas := by
      simp only [tested] at hgas
      split at hgas <;> omega
    have h1 := dup1 (fork := fork) (code := code) (message := message) (memory := memory)
      (state := state) (substate := substate) (returnData := returnData)
      (pc := pc) (x := x) (rest := rest) (gas := gas)
      l0 b0 (by omega) (by simp only [List.length_cons]; omega)
    have h2 := push (fork := fork) (code := code) (message := message) (memory := memory)
      (state := state) (substate := substate) (returnData := returnData)
      (pc := pc + 1) (stack := x :: x :: rest)
      (gas := gas - 3) (n := n) (word := key) hn l1 b1 (decode_push n hn) hkey (by omega)
      (by simp only [List.length_cons]; omega)
    have h3 := binary (fork := fork) (code := code) (message := message) (memory := memory)
      (state := state) (substate := substate) (returnData := returnData)
      (pc := pc + 1 + (1 + n)) (x := key) (y := x)
      (rest := x :: rest) (gas := gas - 3 - 3) l2 b2
      (ofByte_of_decode (op := .eq) rfl (Fork.frontier_le _)) instruction_eq
      (by simp only [OPCODE_EQ, VERY_LOW]; omega)
    have h4 := push (fork := fork) (code := code) (message := message) (memory := memory)
      (state := state) (substate := substate) (returnData := returnData)
      (pc := pc + 1 + (1 + n) + 1)
      (stack := equal key x :: x :: rest) (gas := gas - 3 - 3 - OPCODE_EQ) (n := m) (word := dest)
      hm l3 b3 (decode_push m hm) hdest (by simp only [OPCODE_EQ, VERY_LOW]; omega)
      (by simp only [List.length_cons]; omega)
    have h14 := ((h1.seq h2).seq h3).seq h4
    by_cases hk : key = x
    · have h5 := jumpi_taken (fork := fork) (code := code) (message := message) (memory := memory)
        (state := state) (substate := substate) (returnData := returnData)
        (pc := pc + 1 + (1 + n) + 1 + (1 + m))
        (destination := dest) (condition := equal key x) (rest := x :: rest)
        (gas := gas - 3 - 3 - OPCODE_EQ - 3) l4 b4 (by simp only [OPCODE_EQ, VERY_LOW]; omega)
        (by simp [equal, hk]) valid
      have h := h14.seq h5
      simp only [branch, tested, hk, ite_true]
      exact Hoare.gas_eq h (by simp only [OPCODE_EQ, VERY_LOW]; omega)
    · have heq : equal key x = 0 := by simp [equal, hk]
      rw [heq] at h14
      have h5 := jumpi_zero (fork := fork) (code := code) (message := message) (memory := memory)
        (state := state) (substate := substate) (returnData := returnData)
        (pc := pc + 1 + (1 + n) + 1 + (1 + m))
        (destination := dest) (rest := x :: rest) (gas := gas - 3 - 3 - OPCODE_EQ - 3) l4 b4
        (by simp only [OPCODE_EQ, VERY_LOW]; omega)
      have hpc : pc + 1 + (1 + n) + 1 + (1 + m) + 1 = pc + entrySize n m := by
        simp only [entrySize]
        omega
      rw [hpc] at h5
      simp only [tested, hk, ite_false] at hgas
      have h15 := Hoare.gas_eq (h14.seq h5) (gas' := gas - 22)
        (by simp only [OPCODE_EQ, VERY_LOW]; omega)
      have ih := branchTable (x := x) (pc := pc + entrySize n m) (gas := gas - 22) hn hm hstack
        table (by omega)
      simp only [branch, tested, hk, ite_false]
      exact Hoare.gas_eq (h15.seq ih) (by omega)

/-- When no key of the table is `x`, the run goes past all its entries. -/
theorem branch_of_forall_ne {x : U256} {size : Nat} :
    ∀ {pc : Nat} {entries : List (U256 × U256)}, (∀ e ∈ entries, e.1 ≠ x) →
      branch x pc size entries = pc + entries.length * size
  | pc, [], _ => by simp [branch]
  | pc, (key, dest) :: entries, h => by
    have hk : key ≠ x := h (key, dest) (by simp)
    simp only [branch, hk, ite_false, List.length_cons]
    rw [branch_of_forall_ne fun e he => h e (by simp [he])]
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- When no key of the table is `x`, the run tests every entry. -/
theorem tested_of_forall_ne {x : U256} :
    ∀ {entries : List (U256 × U256)}, (∀ e ∈ entries, e.1 ≠ x) →
      tested x entries = entries.length
  | [], _ => rfl
  | (key, dest) :: entries, h => by
    have hk : key ≠ x := h (key, dest) (by simp)
    simp only [tested, hk, ite_false, List.length_cons]
    rw [tested_of_forall_ne fun e he => h e (by simp [he])]

end EthLib.Execution.Evm.Logic

module

public import EthLib.Execution.Proofs.Evm.OpTables.Parts
public import EthLib.Execution.Proofs.Evm.Machine.Frame

/-!
# Proofs: the instructions that read and write only the stack follow the tables

Each one takes and leaves the words of its tables, and pays its constant price.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-- An exchange keeps the height of the stack, and both depths are on it. -/
theorem exchangeItems_eq_some {stack after : Stack} {i j : Nat}
    (h : exchangeItems stack i j = some after) :
    after.val.length = stack.val.length ∧ i < stack.val.length ∧ j < stack.val.length := by
  unfold exchangeItems at h
  split at h
  · rename_i a b ha hb
    cases h
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hb
    exact ⟨by simp, hi, hj⟩
  · cases h

/-- POP takes a word and pays at least its price. -/
theorem popStep_moves {evm after : Evm fork Meter} (h : popStep evm = .ok after) :
    Moves 1 0 OPCODE_POP evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((popWord_moves h1).trans (chargeGas_moves h2)).trans (advance_moves _ _)).weaken

/-- PUSHn leaves a word and pays at least its price. -/
theorem pushN_moves {n : Fin 33} {evm after : Evm fork Meter} (h : pushN n evm = .ok after) :
    Moves 0 1 (if n.val = 0 then OPCODE_PUSH0 else OPCODE_PUSH) evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((chargeGas_moves h1).trans (pushWord_moves h2)).trans (advance_moves _ _)).weaken

/-- DUPn copies the word at its depth and pays at least its price. -/
theorem dupN_moves {n : Fin 16} {evm after : Evm fork Meter} (h : dupN n evm = .ok after) :
    Moves (n.val + 1) (n.val + 2) OPCODE_DUP evm after := by
  obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · cases h
  · rename_i x hx
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have m1 := chargeGas_moves h1
    obtain ⟨hn, -⟩ := List.getElem?_eq_some_iff.mp hx
    have := m1.stack
    exact ((((m1.trans (pushWord_moves h2)).trans (advance_moves _ _)).weaken (t' := 0)
      (l' := 1) (p' := OPCODE_DUP)).deepen (n.val + 1) (by omega)).weaken

/-- SWAPn exchanges the top word with the word at its depth and pays at least its price. -/
theorem swapN_moves {n : Fin 16} {evm after : Evm fork Meter} (h : swapN n evm = .ok after) :
    Moves (n.val + 2) (n.val + 2) OPCODE_SWAP evm after := by
  obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
  have m1 := chargeGas_moves h1
  split at h
  · rename_i top rest hs hstack
    split at h
    · cases h
    · rename_i x hx
      cases h
      obtain ⟨hn, -⟩ := List.getElem?_eq_some_iff.mp hx
      have hlen : e1.stack.val.length = rest.length + 1 := by rw [hstack]; rfl
      have m2 : Moves 0 0 0 e1 (advance { e1 with stack := ⟨x :: rest.set n.val top, by
          simpa using hs⟩ }) :=
        .of_length (by simp [advance, hlen]) rfl rfl rfl
      have := m1.stack
      exact ((m1.trans m2).weaken (t' := 0) (l' := 0) (p' := OPCODE_SWAP)).deepen (n.val + 2)
        (by omega) |>.weaken
  · cases h

/-- DUPN copies the word at the depth of its immediate byte and pays at least its price. -/
theorem dupnStep_moves {evm after : Evm fork Meter} {n : Nat}
    (hn : decodeSingle (immediateByte evm.code evm.pc) = some n) (h : dupnStep evm = .ok after) :
    Moves n (n + 1) OPCODE_DUPN evm after := by
  obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
  have m1 := chargeGas_moves h1
  rw [m1.code, pc_chargeGas h1, hn] at h
  dsimp only at h
  split at h
  · cases h
  · rename_i x hx
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hx
    have := m1.stack
    exact ((((m1.trans (pushWord_moves h2)).trans (advance_moves _ _)).weaken (t' := 0)
      (l' := 1) (p' := OPCODE_DUPN)).deepen n (by omega)).weaken

/-- SWAPN exchanges the top word with the word at the depth of its immediate byte. -/
theorem swapnStep_moves {evm after : Evm fork Meter} {n : Nat}
    (hn : decodeSingle (immediateByte evm.code evm.pc) = some n) (h : swapnStep evm = .ok after) :
    Moves (n + 1) (n + 1) OPCODE_SWAPN evm after := by
  obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
  have m1 := chargeGas_moves h1
  have hn' : decodeSingle (immediateByte e1.code e1.pc) = some n := by
    rw [m1.code, pc_chargeGas h1]
    exact hn
  rw [hn'] at h
  dsimp only at h
  split at h
  · rename_i stack hs
    cases h
    obtain ⟨hlen, -, hj⟩ := exchangeItems_eq_some hs
    have m2 : Moves 0 0 0 e1 (advance { e1 with stack } 2) := .of_length hlen rfl rfl rfl
    have := m1.stack
    have m3 := ((m1.trans m2).weaken (t' := 0) (l' := 0) (p' := OPCODE_SWAPN)).deepen (n + 1)
      (by omega)
    exact m3.weaken
  · cases h

/-- EXCHANGE exchanges the two words at the depths of its immediate byte. -/
theorem exchangeStep_moves {evm after : Evm fork Meter} {n m : Nat}
    (hn : decodePair (immediateByte evm.code evm.pc) = some (n, m))
    (h : exchangeStep evm = .ok after) : Moves (m + 1) (m + 1) OPCODE_EXCHANGE evm after := by
  obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
  have m1 := chargeGas_moves h1
  have hn' : decodePair (immediateByte e1.code e1.pc) = some (n, m) := by
    rw [m1.code, pc_chargeGas h1]
    exact hn
  rw [hn'] at h
  dsimp only at h
  split at h
  · rename_i stack hs
    cases h
    obtain ⟨hlen, -, hj⟩ := exchangeItems_eq_some hs
    have m2 : Moves 0 0 0 e1 (advance { e1 with stack } 2) := .of_length hlen rfl rfl rfl
    have := m1.stack
    have m3 := ((m1.trans m2).weaken (t' := 0) (l' := 0) (p' := OPCODE_EXCHANGE)).deepen (m + 1)
      (by omega)
    exact m3.weaken
  · cases h

/-- EXP takes two words, leaves one and pays at least its price. -/
theorem expStep_moves {evm after : Evm fork Meter} (h : expStep fork evm = .ok after) :
    Moves 2 1 OPCODE_EXP_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((((popWord_moves h1).trans (popWord_moves h2)).trans (chargeGas_moves h3)).trans
    (pushWord_moves h4)).trans (advance_moves _ _)).weaken

/-- KECCAK256 takes two words, leaves one and pays at least its price. -/
theorem keccak256Step_moves {evm after : Evm fork Meter} (h : keccak256Step evm = .ok after) :
    Moves 2 1 OPCODE_KECCAK256_BASE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((((popWord_moves h1).trans (popWord_moves h2)).trans
    (chargeGasAndMemory_moves h3)).trans (pushWord_moves h4)).trans (advance_moves _ _)).weaken
    (hp := by simp only [keccak256Cost]; omega)

/-- The price of PUSHn in the tables is the price that it charges. -/
theorem constantGas_push (n : Fin 33) :
    Op.constantGas fork (.push n) = if n.val = 0 then OPCODE_PUSH0 else OPCODE_PUSH := by
  simp only [Op.constantGas, Fin.ext_iff, Fin.val_zero]

/-- Each instruction that reads and writes only the stack follows the tables. -/
theorem stackOnlyStep_moves {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} {takes leaves : Nat} (hf : stackOnlyStep fork op = some f)
    (hw : op.stackWords (immediateByte evm.code evm.pc) = some (takes, leaves))
    (h : f evm = .ok after) : Moves takes leaves (op.constantGas fork) evm after := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hf
  case dupn =>
    split at hf
    · cases hf
      obtain ⟨n, hn, he⟩ := Option.map_eq_some_iff.mp hw
      cases he
      exact dupnStep_moves hn h
    · cases hf
  case swapn =>
    split at hf
    · cases hf
      obtain ⟨n, hn, he⟩ := Option.map_eq_some_iff.mp hw
      cases he
      exact swapnStep_moves hn h
    · cases hf
  case exchange =>
    split at hf
    · cases hf
      obtain ⟨⟨n, m⟩, hn, he⟩ := Option.map_eq_some_iff.mp hw
      cases he
      exact exchangeStep_moves hn h
    · cases hf
  all_goals subst hf
  all_goals simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw
  all_goals obtain ⟨rfl, rfl⟩ := hw
  case push n => exact constantGas_push n ▸ pushN_moves h
  all_goals first
    | exact binaryOp_moves h
    | exact unaryOp_moves h
    | exact ternaryOp_moves h
    | exact expStep_moves h
    | exact keccak256Step_moves h
    | exact popStep_moves h
    | exact dupN_moves h
    | exact swapN_moves h

/-! ## An immediate byte that encodes no depth -/

/-- DUPN fails with an error that aborts nothing when its immediate byte encodes no depth. -/
theorem dupnStep_eq_error {evm : Evm fork Meter}
    (hn : decodeSingle (immediateByte evm.code evm.pc) = none) :
    ∃ e, e.aborts = false ∧ dupnStep evm = .error e := by
  unfold dupnStep
  cases hc : chargeGas evm OPCODE_DUPN with
  | error e => exact ⟨e, by rw [chargeGas_eq_error hc]; rfl, rfl⟩
  | ok e1 =>
    have hn' : decodeSingle (immediateByte e1.code e1.pc) = none := by
      rw [(chargeGas_moves hc).code, pc_chargeGas hc]
      exact hn
    exact ⟨.invalidParameter (immediateByte e1.code e1.pc), rfl, by
      simp only [bind, Except.bind, hn']⟩

/-- SWAPN fails with an error that aborts nothing when its immediate byte encodes no depth. -/
theorem swapnStep_eq_error {evm : Evm fork Meter}
    (hn : decodeSingle (immediateByte evm.code evm.pc) = none) :
    ∃ e, e.aborts = false ∧ swapnStep evm = .error e := by
  unfold swapnStep
  cases hc : chargeGas evm OPCODE_SWAPN with
  | error e => exact ⟨e, by rw [chargeGas_eq_error hc]; rfl, rfl⟩
  | ok e1 =>
    have hn' : decodeSingle (immediateByte e1.code e1.pc) = none := by
      rw [(chargeGas_moves hc).code, pc_chargeGas hc]
      exact hn
    exact ⟨.invalidParameter (immediateByte e1.code e1.pc), rfl, by
      simp only [bind, Except.bind, hn']⟩

/-- EXCHANGE fails with an error that aborts nothing when its immediate byte encodes no pair. -/
theorem exchangeStep_eq_error {evm : Evm fork Meter}
    (hn : decodePair (immediateByte evm.code evm.pc) = none) :
    ∃ e, e.aborts = false ∧ exchangeStep evm = .error e := by
  unfold exchangeStep
  cases hc : chargeGas evm OPCODE_EXCHANGE with
  | error e => exact ⟨e, by rw [chargeGas_eq_error hc]; rfl, rfl⟩
  | ok e1 =>
    have hn' : decodePair (immediateByte e1.code e1.pc) = none := by
      rw [(chargeGas_moves hc).code, pc_chargeGas hc]
      exact hn
    exact ⟨.invalidParameter (immediateByte e1.code e1.pc), rfl, by
      simp only [bind, Except.bind, hn']⟩

end EthLib.Execution.Evm

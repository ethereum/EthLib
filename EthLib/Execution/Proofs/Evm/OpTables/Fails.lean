module

public import EthLib.Execution.Proofs.Evm.OpTables.Parts
public import EthLib.Execution.Proofs.Evm.Step
public import EthLib.Base.Proofs.Except

/-!
# Proofs: the errors of the parts of an instruction follow the tables

A pop fails only on the empty stack, and a push only on a full stack.

So a stack error of an instruction comes only from the words of its tables.

An error that aborts the run comes only once the instruction has taken its words.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)

variable {fork : Fork} {Meter : Type}

namespace FailsByTables

variable {a b : Evm fork Meter} {e : EvmError} {t l : Nat}

/-- An error that halts the frame and is no stack error follows any tables. -/
theorem of_halts (hu : e ≠ .stackUnderflow) (ho : e ≠ .stackOverflow) (ha : e.aborts = false) :
    FailsByTables t l a e :=
  ⟨fun h => absurd h hu, fun h => absurd h ho, fun _ => ha⟩

/-- Out of gas follows any tables. -/
theorem outOfGas : FailsByTables t l a .outOfGas :=
  of_halts nofun nofun rfl

/-- A write in a static frame follows any tables. -/
theorem writeInStaticContext : FailsByTables t l a .writeInStaticContext :=
  of_halts nofun nofun rfl

/-- An underflow follows the tables of a step that takes more words than the stack holds. -/
theorem of_underflow (h : a.stack.val.length < t) : FailsByTables t l a .stackUnderflow :=
  ⟨fun _ => h, nofun, fun _ => rfl⟩

/-- An overflow follows the tables of a step whose words would overflow the stack. -/
theorem of_overflow (h : STACK_LIMIT + t < a.stack.val.length + l) :
    FailsByTables t l a .stackOverflow :=
  ⟨nofun, fun _ => h, fun _ => rfl⟩

/-- An error follows the tables of a frame when it follows them from a frame of the same stack. -/
theorem of_stack (hs : b.stack = a.stack) (h : FailsByTables t l b e) : FailsByTables t l a e := by
  have hu := h.underflow
  have ho := h.overflow
  have hh := h.short
  rw [hs] at hu ho hh
  exact ⟨hu, ho, hh⟩

variable [GasMeter Meter]

/-- An error that aborts the run follows the tables once the stack holds the words taken. -/
theorem of_aborts {p t' l' : Nat} (m : Moves t' l' p a b) (ht : t ≤ t') (ha : e.aborts = true) :
    FailsByTables t l a e := by
  have := m.enough
  refine ⟨fun h => ?_, fun h => ?_, fun h => absurd h (by omega)⟩ <;> subst h <;> cases ha

/-- A pop that fails after a change follows the tables of a step that takes one more word. -/
theorem pop {p t' l' : Nat} (m : Moves t' l' p a b) (h : popWord b = .error e)
    (ht : t' < t + l' := by omega) : FailsByTables t l a e := by
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · obtain ⟨hs, rfl⟩ := Stack.pop_eq_error_iff.mp h
    have := m.stack
    rw [hs, List.length_nil] at this
    exact of_underflow (by omega)
  · cases h

omit [GasMeter Meter] in
/-- A push that fails on a stack of the height given leaves one word too many. -/
theorem push_of_length {t' l' : Nat} {x : U256}
    (hs : b.stack.val.length + t' = a.stack.val.length + l') (h : pushWord b x = .error e)
    (hl : t + l' < t' + l := by omega) : FailsByTables t l a e := by
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · obtain ⟨hb, rfl⟩ := Stack.push_eq_error_iff.mp h
    exact of_overflow (by omega)
  · cases h

/-- A push that fails after a change follows the tables of a step that leaves one more word. -/
theorem push {p t' l' : Nat} {x : U256} (m : Moves t' l' p a b) (h : pushWord b x = .error e)
    (hl : t + l' < t' + l := by omega) : FailsByTables t l a e :=
  push_of_length m.stack h hl

end FailsByTables

/-! ## The parts -/

variable [GasMeter Meter]

/-- A gas check fails only out of gas. -/
theorem checkGas_error {evm : Evm fork Meter} {amount : Nat} {e : EvmError}
    (h : checkGas evm amount = .error e) : e = .outOfGas := by
  unfold checkGas at h
  split at h
  · cases h
    rfl
  · cases h

variable [LawfulGasMeter Meter]

/-- A charge of a price and of the growth of memory fails only out of gas. -/
theorem chargeGasAndMemory_error {evm : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} {e : EvmError}
    (h : chargeGasAndMemory evm cost ranges = .error e) : e = .outOfGas := by
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact chargeGas_eq_error h
  · cases h

/-- A charge of state gas fails only out of gas. -/
theorem chargeStateGas_error {evm : Evm fork Meter} {amount : Nat} {e : EvmError}
    (h : chargeStateGas evm amount = .error e) : e = .outOfGas := by
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact LawfulGasMeter.chargeState_error h
  · cases h

/-! ## The shapes of the simple instructions -/

/-- An instruction that reads the frame fails by its tables. -/
theorem readFrame_fails {cost : Nat} {value : Evm fork Meter → U256} {evm : Evm fork Meter}
    {e : EvmError} (h : readFrame cost value evm = .error e) : FailsByTables 0 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨e1, h1, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push (chargeGas_moves h1) h
  · cases h

/-- An instruction that reads a number fails by its tables. -/
theorem readNumber_fails {cost : Nat} {value : Evm fork Meter → Nat} {evm : Evm fork Meter}
    {e : EvmError} (h : readNumber cost value evm = .error e) : FailsByTables 0 1 evm e := by
  unfold readNumber at h
  split at h
  · exact readFrame_fails h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  · cases h
    exact .of_aborts (.refl evm) (Nat.le_refl _) rfl

/-- An instruction with one operand fails by its tables. -/
theorem unaryOp_fails {cost : Nat} {f : U256 → U256} {evm : Evm fork Meter} {e : EvmError}
    (h : unaryOp cost f evm = .error e) : FailsByTables 1 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨e2, h2, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push (m1.trans (chargeGas_moves h2)) h
  · cases h

/-- An instruction with two operands fails by its tables. -/
theorem binaryOp_fails {cost : Nat} {f : U256 → U256 → U256} {evm : Evm fork Meter}
    {e : EvmError} (h : binaryOp cost f evm = .error e) : FailsByTables 2 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, h2, h⟩
  · exact .pop m1 h
  have m2 := m1.trans (popWord_moves h2)
  rcases Base.bind_eq_error h with h | ⟨e3, h3, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push (m2.trans (chargeGas_moves h3)) h
  · cases h

/-- An instruction with three operands fails by its tables. -/
theorem ternaryOp_fails {cost : Nat} {f : U256 → U256 → U256 → U256} {evm : Evm fork Meter}
    {e : EvmError} (h : ternaryOp cost f evm = .error e) : FailsByTables 3 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, h2, h⟩
  · exact .pop m1 h
  have m2 := m1.trans (popWord_moves h2)
  rcases Base.bind_eq_error h with h | ⟨⟨_, e3⟩, h3, h⟩
  · exact .pop m2 h
  have m3 := m2.trans (popWord_moves h3)
  rcases Base.bind_eq_error h with h | ⟨e4, h4, h⟩
  · rw [chargeGas_eq_error h]
    exact .outOfGas
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push (m3.trans (chargeGas_moves h4)) h
  · cases h

end EthLib.Execution.Evm

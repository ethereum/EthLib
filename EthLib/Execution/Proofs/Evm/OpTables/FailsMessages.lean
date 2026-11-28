module

public import EthLib.Execution.Proofs.Evm.OpTables.Fails
public import EthLib.Execution.Proofs.Evm.OpTables.Messages

/-!
# Proofs: the errors of the calls and the creations follow the tables

A call or a creation fails on a stack error only when the stack is too short or would grow too high.

Each error that aborts the run comes once it has taken its words.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The calls -/

/-- The pops of the operands of a call fail by the tables of the call. -/
theorem popCallOperands_fails {kind : CallKind} {evm : Evm fork Meter} {l : Nat} {e : EvmError}
    (h : popCallOperands kind evm = .error e) :
    FailsByTables (if kind.sendsValue then 7 else 6) l evm e := by
  have hv : (if kind.sendsValue then 7 else 6) = 6 + (if kind.sendsValue then 1 else 0) := by
    split <;> rfl
  rw [hv]
  rcases Base.bind_eq_error h with h | ⟨⟨_, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨_, e2⟩, h2, h⟩
  · exact .pop m1 h
  have m2 := m1.trans (popWord_moves h2)
  rcases Base.bind_eq_error h with h | ⟨⟨_, e3⟩, h3, h⟩
  · unfold popCallValue at h
    split at h
    · rename_i hs
      simp only [hs, ↓reduceIte]
      exact .pop m2 h
    · cases h
  have p3 : Moves (if kind.sendsValue then 1 else 0) 0 0 e2 e3 := by
    unfold popCallValue at h3
    split at h3
    · rename_i hs
      simpa [hs] using popWord_moves h3
    · rename_i hs
      cases h3
      simpa [hs] using Moves.refl e2
  have m3 := m2.trans p3
  rcases Base.bind_eq_error h with h | ⟨⟨_, e4⟩, h4, h⟩
  · exact .pop m3 h
  have m4 := m3.trans (popWord_moves h4)
  rcases Base.bind_eq_error h with h | ⟨⟨_, e5⟩, h5, h⟩
  · exact .pop m4 h
  have m5 := m4.trans (popWord_moves h5)
  rcases Base.bind_eq_error h with h | ⟨⟨_, e6⟩, h6, h⟩
  · exact .pop m5 h
  have m6 := m5.trans (popWord_moves h6)
  rcases Base.bind_eq_error h with h | ⟨⟨_, e7⟩, -, h⟩
  · exact .pop m6 h
  · cases h

/-- A call fails by its tables. -/
theorem callStep_fails {kind : CallKind} {evm : Evm fork Meter} {e : EvmError}
    (h : callStep kind evm = .error e) :
    FailsByTables (if kind.sendsValue then 7 else 6) 1 evm e := by
  rcases Base.bind_eq_error h with h | ⟨⟨call, e1⟩, h1, h⟩
  · exact popCallOperands_fails h
  have m1 := popCallOperands_moves h1
  dsimp only at h
  split at h
  · cases h
    exact .writeInStaticContext
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  have m2 : Moves 0 0 0 e1 e2 := by
    have := accessAddress_moves e1 call.address
    rwa [hacc] at this
  rw [hacc] at h
  dsimp only at h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · rw [checkGas_error h]
    exact .outOfGas
  exact .of_aborts ((m1.trans m2).trans (recordAccountRead_moves e2 call.address)) (by omega)
    (keepReads_eq_error.mp h).2

/-! ## The creations -/

/-- A call or a creation that sends no message fails by its tables, only on a full stack. -/
theorem skipCall_fails {before evm : Evm fork Meter} {t gas reservoir : Nat} {e : EvmError}
    (hs : evm.stack.val.length + t = before.stack.val.length)
    (h : skipCall evm gas reservoir = .error e) : FailsByTables t 1 before e := by
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact .push_of_length (t' := t) (l' := 0) (by exact hs) h
  · cases h

/-- The address of a creation fails only with an error that aborts the run. -/
theorem creationAddress_error {sender : Address} {nonce : Nat} {salt : Option U256}
    {initCode : ByteArray} {e : EvmError}
    (h : creationAddress sender nonce salt initCode = .error e) : e.aborts = true := by
  unfold creationAddress at h
  split at h
  · cases h
  · cases hc : createAddress sender nonce with
    | error e' =>
      rw [hc] at h
      cases h
      rfl
    | ok a =>
      rw [hc] at h
      cases h

/-- The launch of a creation that has taken its words fails by the tables of the creation. -/
theorem launchCreate_fails {before evm : Evm fork Meter} {value : U256} {initCode : ByteArray}
    {salt : Option U256} {takes price : Nat} {e : EvmError}
    (paid : Moves takes 0 price before evm)
    (h : launchCreate evm value initCode salt = .error e) : FailsByTables takes 1 before e := by
  unfold launchCreate at h
  dsimp only at h
  have pre : Moves takes 0 price before
      (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) :=
    paid.keep rfl rfl rfl rfl
  split at h
  · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact skipCall_fails pre.stack h
    · cases h
  rcases Base.bind_eq_error h with h | ⟨address, -, h⟩
  · exact .of_aborts pre (by omega) (creationAddress_error h)
  have c0 := (pre.trans (accessAddress_moves _ address)).trans
    (recordAccountRead_moves _ address)
  exact .of_aborts c0 (by omega) (keepReads_eq_error.mp h).2

variable [LawfulGasMeter Meter]

/-- A creation fails by its tables. -/
theorem createStep_fails {create2 : Bool} {evm : Evm fork Meter} {e : EvmError}
    (h : createStep create2 evm = .error e) :
    FailsByTables (if create2 then 4 else 3) 1 evm e := by
  unfold createStep at h
  dsimp only at h
  split at h
  · rcases Base.bind_eq_error h with h | ⟨_, h, -⟩
    · cases h
      exact .writeInStaticContext
    · cases h
  have hv : (if create2 then 4 else 3) = 3 + (if create2 then 1 else 0) := by
    split <;> rfl
  rw [hv]
  rcases Base.bind_eq_error h with h | ⟨⟨value, e1⟩, h1, h⟩
  · exact .pop (.refl _) h
  have m1 := popWord_moves h1
  rcases Base.bind_eq_error h with h | ⟨⟨start, e2⟩, h2, h⟩
  · exact .pop m1 h
  have m2 := m1.trans (popWord_moves h2)
  rcases Base.bind_eq_error h with h | ⟨⟨size, e3⟩, h3, h⟩
  · exact .pop m2 h
  have m3 := m2.trans (popWord_moves h3)
  rcases Base.bind_eq_error h with h | ⟨⟨salt, e4⟩, h4, h⟩
  · unfold popSalt at h
    cases create2
    · cases h
    · show FailsByTables (3 + 1) 1 evm e
      rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact .pop m3 h
      · cases h
  have m4 := m3.trans (popSalt_moves h4)
  rcases Base.bind_eq_error h with h | ⟨e5, h5, h⟩
  · rw [chargeGasAndMemory_error h]
    exact .outOfGas
  have m := (m4.trans (chargeGasAndMemory_moves h5)).weaken
    (t' := 3 + if create2 then 1 else 0) (l' := 0) (p' := 0) (ht := by split <;> omega)
  unfold genericCreate at h
  split at h
  · cases h
    exact .outOfGas
  split at h
  · cases h
    exact .writeInStaticContext
  exact launchCreate_fails m h

/-- Each instruction that may send a message fails by its tables. -/
theorem messageInstruction_fails {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {takes leaves : Nat} {immediate : UInt8} {e : EvmError}
    (hrun : messageInstruction fork op = some run)
    (hw : op.stackWords immediate = some (takes, leaves)) (h : run evm = .error e) :
    FailsByTables takes leaves evm e := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc <;>
      simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;>
      obtain ⟨rfl, rfl⟩ := hw
    all_goals first
      | (subst hc; exact callStep_fails h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact callStep_fails h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun <;>
      simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;>
      obtain ⟨rfl, rfl⟩ := hw
    all_goals first
      | (subst hrun; exact createStep_fails h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact createStep_fails h
         · cases hrun)

end EthLib.Execution.Evm

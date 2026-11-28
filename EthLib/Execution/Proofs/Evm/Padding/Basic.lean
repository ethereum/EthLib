module

public import EthLib.Execution.Evm.Interpreter
public import EthLib.Execution.Proofs.Evm.Machine.Memory
public import EthLib.Base.Proofs.Except

/-!
# Proofs: steps that run the same on other code with the same bytes

Two codes agree when they hold the same bytes, read as zeros past their ends.

Their flags agree when they mark the same jump destinations.

A step that reads the code only through such bytes and flags runs the same on either.

The tactics here unfold a step and match its two runs part by part.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork byteAtOrZero)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A result of a step, with the code and the jump destinations of each frame replaced. -/
def StepResult.withCode (code : ByteArray) (jumps : Array Bool) :
    StepResult fork Meter → StepResult fork Meter
  | .next after => .next { after with code, validJumpDestinations := jumps }
  | .child caller message resume =>
    .child { caller with code, validJumpDestinations := jumps } message fun child =>
      (fun after => { after with code, validJumpDestinations := jumps }) <$> resume child

/-- Other code with the same bytes and destinations gives the same frame or error, with that code.

The bytes are read as zeros past the end of each code. -/
def SwapsCode (run : Evm fork Meter → Except EvmError (Evm fork Meter)) : Prop :=
  ∀ evm code jumps, (∀ i, byteAtOrZero code i = byteAtOrZero evm.code i) →
    (∀ i, isValidJumpDest jumps i = isValidJumpDest evm.validJumpDestinations i) →
      run { evm with code, validJumpDestinations := jumps } =
        (fun after => { after with code, validJumpDestinations := jumps }) <$> run evm

/-- Other code with the same bytes and destinations gives the same result, with that code. -/
def SwapsCodeChild (run : Evm fork Meter → Except EvmError (StepResult fork Meter)) : Prop :=
  ∀ evm code jumps, (∀ i, byteAtOrZero code i = byteAtOrZero evm.code i) →
    (∀ i, isValidJumpDest jumps i = isValidJumpDest evm.validJumpDestinations i) →
      run { evm with code, validJumpDestinations := jumps } =
        StepResult.withCode code jumps <$> run evm

/-! ## Sequences in the monad of errors -/

namespace Padding

/-- A success in the monad of errors is its pure value. -/
theorem pure_eq_ok {ε α : Type} (a : α) : (pure a : Except ε α) = Except.ok a := rfl

/-- An error stops a sequence of steps. -/
theorem error_bind_eq {ε α β : Type} (e : ε) (k : α → Except ε β) :
    (Except.error e >>= k) = Except.error e := rfl

/-- A map keeps an error. -/
theorem map_error_eq {ε α β : Type} (e : ε) (f : α → β) :
    f <$> (Except.error e : Except ε α) = Except.error e := rfl

end Padding

omit [GasMeter Meter] in
/-- Two results that send a message agree when their parts agree. -/
theorem ok_child_eq {c₁ c₂ : Evm fork Meter} {m₁ m₂ : Message fork}
    {r₁ r₂ : Evm fork Meter → Except EvmError (Evm fork Meter)} (hc : c₁ = c₂) (hm : m₁ = m₂)
    (hr : ∀ child, r₁ child = r₂ child) :
    (Except.ok (.child c₁ m₁ r₁) : Except EvmError (StepResult fork Meter)) =
      Except.ok (.child c₂ m₂ r₂) := by
  subst hc hm
  rw [funext hr]

/-- A check that keeps its reads maps through, when the halted frames of both sides map. -/
theorem keepReads_map {α β : Type} {e₁ e₂ : Evm fork Meter} {h₁ : Evm fork Meter → β}
    {h₂ : Evm fork Meter → α} {f : α → β} {x₁ : Except EvmError β} {x₂ : Except EvmError α}
    (hx : x₁ = f <$> x₂)
    (hh : ∀ err, h₁ (exceptionalHalt e₁ err) = f (h₂ (exceptionalHalt e₂ err))) :
    keepReads e₁ h₁ x₁ = f <$> keepReads e₂ h₂ x₂ := by
  subst hx
  cases x₂ with
  | error err =>
    simp only [keepReads, EthLib.Execution.Evm.Padding.map_error_eq]
    split <;> simp [hh, Functor.map, Except.map]
  | ok a => rfl

/-! ## Accesses, with the frame as a record -/

omit [GasMeter Meter] in
/-- An access to an address changes only the accessed addresses, from Berlin. -/
theorem accessAddress_eq (evm : Evm fork Meter) (address : Address) :
    accessAddress evm address =
      (decide (fork ≥ .berlin) && decide (address ∉ evm.substate.accessedAddresses),
        { evm with
          substate := if fork ≥ .berlin then
            { evm.substate with
              accessedAddresses := evm.substate.accessedAddresses.insert address }
          else evm.substate }) := by
  unfold accessAddress
  split <;> simp_all

omit [GasMeter Meter] in
/-- An access to a storage key changes only the accessed storage keys, from Berlin. -/
theorem accessStorageKey_eq (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    accessStorageKey evm address key =
      (decide (fork ≥ .berlin) &&
          decide (key ∉ evm.substate.accessedStorageKeys.getD address ∅),
        { evm with
          substate := if fork ≥ .berlin then
            { evm.substate with
              accessedStorageKeys := evm.substate.accessedStorageKeys.insert address
                ((evm.substate.accessedStorageKeys.getD address ∅).insert key) }
          else evm.substate }) := by
  unfold accessStorageKey
  split <;> simp_all

/-! ## Reads of the code by its bytes -/

/-- Two codes with the same bytes give the same pushed word. -/
theorem pushData_congr {code other : ByteArray}
    (h : ∀ i, byteAtOrZero code i = byteAtOrZero other i) (pc n : Nat) :
    pushData code pc n = pushData other pc n := by
  simp only [pushData, bufferRead_eq, h]

/-- Two codes with the same bytes give the same immediate byte. -/
theorem immediateByte_congr {code other : ByteArray}
    (h : ∀ i, byteAtOrZero code i = byteAtOrZero other i) (pc : Nat) :
    immediateByte code pc = immediateByte other pc :=
  h (pc + 1)

/-- Two codes with the same bytes give the same bytes from any start. -/
theorem bufferBytes_congr {code other : ByteArray}
    (h : ∀ i, byteAtOrZero code i = byteAtOrZero other i) (start size : Nat) :
    bufferBytes code start size = bufferBytes other start size := by
  simp only [bufferBytes_eq, bufferRead_eq, h]

/-! ## Tactics -/

/-- Unfold the parts of a step, and push maps through its sequences. -/
scoped syntax "swap_code_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| swap_code_simp) => `(tactic| swap_code_simp [])
  | `(tactic| swap_code_simp [$ids,*]) =>
    `(tactic| simp only [popWord, pushWord, chargeGas, chargeStateGas, refillStateGas,
               chargeGasAndMemory, advance, exceptionalHalt, recordAccountRead,
               recordStorageRead, accessAddress_eq, accessStorageKey_eq, checkGas, readFrame,
               readNumber, unaryOp, binaryOp, ternaryOp, haltWithOutput, resumeCreate,
               resumeCall, incorporateChild, touchedOnSuccess, touchedOnError,
               StepResult.withCode, throw, throwThe, MonadExceptOf.throw, bind_assoc,
               EthLib.Execution.Evm.Padding.pure_eq_ok, EthLib.Base.ok_bind,
               EthLib.Execution.Evm.Padding.error_bind_eq, EthLib.Base.map_ok,
               EthLib.Execution.Evm.Padding.map_error_eq, map_bind, Functor.map_map,
               Function.comp_def, id_eq, $ids,*])

/-- Unfold a step, then match its parts on both sides, with the code replaced on the left.

The extra lemmas rewrite the reads of the code. -/
scoped syntax "swap_code" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| swap_code) => `(tactic| swap_code [])
  | `(tactic| swap_code [$ids,*]) =>
    `(tactic| (swap_code_simp [$ids,*]
               repeat' (first
                 -- Two frames that differ only in the code that the map puts back.
                 | with_reducible rfl
                 | swap_code_simp [$ids,*]
                 -- A halt that keeps the reads, then the rest of the instruction.
                 | refine keepReads_map ?_ fun _ => ?_
                 -- The same first part on both sides, then the rest.
                 | refine bind_congr fun _ => ?_
                 -- A message to run, then the frame that resumes.
                 | refine ok_child_eq rfl rfl fun _ => ?_
                 -- A branch, on a condition that reads no code.
                 | (split <;> try simp only [*, bind_assoc,
                     EthLib.Execution.Evm.Padding.pure_eq_ok, EthLib.Base.ok_bind,
                     EthLib.Execution.Evm.Padding.error_bind_eq, EthLib.Base.map_ok,
                     EthLib.Execution.Evm.Padding.map_error_eq, map_bind,
                     Functor.map_map, ite_true, ite_false, true_and, and_true,
                     not_false_eq_true]))))

end EthLib.Execution.Evm

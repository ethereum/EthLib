module

public import EthLib.Execution.Proofs.Evm.Call.StepRules
public import EthLib.Execution.Proofs.Evm.Call.Observe

/-!
# Proofs: no step reads the logs that a simulation reports

A frame keeps two lists of logs: its own, and those that a simulation reports.

Each write of the second list appends to it, and no step reads it.

So logs put in front of the second list at the start of a message stay in front at its end.

Everything else that the message computes is the same, and so is any error that aborts it.

Two messages that start with different second lists then differ only in their second lists.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The frame with `logs` in front of the logs that a simulation reports. -/
def Evm.prependSimulatedLogs (logs : Array Blocks.Log) (evm : Evm fork Meter) : Evm fork Meter :=
  { evm with
    substate := { evm.substate with simulatedLogs := logs ++ evm.substate.simulatedLogs } }

/-- The frame with no log that a simulation reports. -/
def Evm.eraseSimulatedLogs (evm : Evm fork Meter) : Evm fork Meter :=
  { evm with substate := { evm.substate with simulatedLogs := #[] } }

/-! ## The parts of a step keep the logs in front -/

section Parts

variable (logs : Array Blocks.Log)

omit [GasMeter Meter] in
/-- A pop keeps the logs in front. -/
private theorem popWord_prepend (evm : Evm fork Meter) :
    popWord (evm.prependSimulatedLogs logs) =
      (fun p => (p.1, p.2.prependSimulatedLogs logs)) <$> popWord evm := by
  simp only [popWord, Evm.prependSimulatedLogs]
  cases evm.stack.pop <;> rfl

omit [GasMeter Meter] in
/-- A push keeps the logs in front. -/
private theorem pushWord_prepend (evm : Evm fork Meter) (x : U256) :
    pushWord (evm.prependSimulatedLogs logs) x =
      (·.prependSimulatedLogs logs) <$> pushWord evm x := by
  simp only [pushWord, Evm.prependSimulatedLogs]
  cases evm.stack.push x <;> rfl

/-- A charge keeps the logs in front. -/
private theorem chargeGas_prepend (evm : Evm fork Meter) (amount : Nat) :
    chargeGas (evm.prependSimulatedLogs logs) amount =
      (·.prependSimulatedLogs logs) <$> chargeGas evm amount := by
  simp only [chargeGas, Evm.prependSimulatedLogs]
  cases GasMeter.charge evm.gas amount <;> rfl

/-- A charge of state gas keeps the logs in front. -/
private theorem chargeStateGas_prepend (evm : Evm fork Meter) (amount : Nat) :
    chargeStateGas (evm.prependSimulatedLogs logs) amount =
      (·.prependSimulatedLogs logs) <$> chargeStateGas evm amount := by
  simp only [chargeStateGas, Evm.prependSimulatedLogs]
  cases GasMeter.chargeState evm.gas amount <;> rfl

/-- A charge with memory keeps the logs in front. -/
private theorem chargeGasAndMemory_prepend (evm : Evm fork Meter) (cost : Nat)
    (ranges : List (U256 × U256)) :
    chargeGasAndMemory (evm.prependSimulatedLogs logs) cost ranges =
      (·.prependSimulatedLogs logs) <$> chargeGasAndMemory evm cost ranges := by
  simp only [chargeGasAndMemory, chargeGas_prepend, bind_map_left, map_bind, map_pure]
  rfl

omit [GasMeter Meter] in
/-- The pops of the topics keep the logs in front. -/
private theorem popTopics_prepend (evm : Evm fork Meter) (n : Nat) :
    popTopics (evm.prependSimulatedLogs logs) n =
      (fun p => (p.1, p.2.prependSimulatedLogs logs)) <$> popTopics evm n := by
  induction n generalizing evm with
  | zero => rfl
  | succ k ih =>
    simp only [popTopics, popWord_prepend, bind_map_left, map_bind, map_pure, ih]

omit [GasMeter Meter] in
/-- An access to an address keeps the logs in front. -/
private theorem accessAddress_prepend (evm : Evm fork Meter) (address : Address) :
    accessAddress (evm.prependSimulatedLogs logs) address =
      ((accessAddress evm address).1, (accessAddress evm address).2.prependSimulatedLogs logs) := by
  unfold accessAddress
  split <;> rfl

omit [GasMeter Meter] in
/-- An access to a slot keeps the logs in front. -/
private theorem accessStorageKey_prepend (evm : Evm fork Meter) (address : Address)
    (key : Bytes32) :
    accessStorageKey (evm.prependSimulatedLogs logs) address key =
      ((accessStorageKey evm address key).1,
        (accessStorageKey evm address key).2.prependSimulatedLogs logs) := by
  unfold accessStorageKey
  split <;> rfl

omit [GasMeter Meter] in
/-- The record of a read of an account keeps the logs in front. -/
private theorem recordAccountRead_prepend (evm : Evm fork Meter) (address : Address) :
    recordAccountRead (evm.prependSimulatedLogs logs) address =
      (recordAccountRead evm address).prependSimulatedLogs logs := rfl

omit [GasMeter Meter] in
/-- The record of a read of a slot keeps the logs in front. -/
private theorem recordStorageRead_prepend (evm : Evm fork Meter) (address : Address)
    (key : Bytes32) :
    recordStorageRead (evm.prependSimulatedLogs logs) address key =
      (recordStorageRead evm address key).prependSimulatedLogs logs := rfl

/-- A refill of state gas keeps the logs in front. -/
private theorem refillStateGas_prepend (evm : Evm fork Meter) (amount : Nat) :
    refillStateGas (evm.prependSimulatedLogs logs) amount =
      (refillStateGas evm amount).prependSimulatedLogs logs := rfl

omit [GasMeter Meter] in
/-- A move of the program counter keeps the logs in front. -/
private theorem advance_prepend (evm : Evm fork Meter) (n : Nat) :
    advance (evm.prependSimulatedLogs logs) n = (advance evm n).prependSimulatedLogs logs := rfl

/-- An exceptional halt keeps the logs in front. -/
private theorem exceptionalHalt_prepend (evm : Evm fork Meter) (e : EvmError) :
    exceptionalHalt (evm.prependSimulatedLogs logs) e =
      (exceptionalHalt evm e).prependSimulatedLogs logs := rfl

omit [GasMeter Meter] in
/-- Each part of the frame but its simulated logs stays as it was. -/
private theorem prepend_proj (evm : Evm fork Meter) :
    (evm.prependSimulatedLogs logs).pc = evm.pc ∧
    (evm.prependSimulatedLogs logs).stack = evm.stack ∧
    (evm.prependSimulatedLogs logs).memory = evm.memory ∧
    (evm.prependSimulatedLogs logs).code = evm.code ∧
    (evm.prependSimulatedLogs logs).validJumpDestinations = evm.validJumpDestinations ∧
    (evm.prependSimulatedLogs logs).gas = evm.gas ∧
    (evm.prependSimulatedLogs logs).running = evm.running ∧
    (evm.prependSimulatedLogs logs).message = evm.message ∧
    (evm.prependSimulatedLogs logs).output = evm.output ∧
    (evm.prependSimulatedLogs logs).returnData = evm.returnData ∧
    (evm.prependSimulatedLogs logs).state = evm.state ∧
    (evm.prependSimulatedLogs logs).error = evm.error ∧
    (evm.prependSimulatedLogs logs).substate.accountsToDelete = evm.substate.accountsToDelete ∧
    (evm.prependSimulatedLogs logs).substate.logs = evm.substate.logs ∧
    (evm.prependSimulatedLogs logs).substate.touchedAccounts = evm.substate.touchedAccounts ∧
    (evm.prependSimulatedLogs logs).substate.refundCounter = evm.substate.refundCounter ∧
    (evm.prependSimulatedLogs logs).substate.accessedAddresses = evm.substate.accessedAddresses ∧
    (evm.prependSimulatedLogs logs).substate.accessedStorageKeys =
      evm.substate.accessedStorageKeys :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- The simulated logs start with the logs put in front. -/
private theorem prepend_simulatedLogs (evm : Evm fork Meter) :
    (evm.prependSimulatedLogs logs).substate.simulatedLogs =
      logs ++ evm.substate.simulatedLogs := rfl

omit [GasMeter Meter] in
/-- The code of an account reads the same. -/
private theorem accountCode_prepend (evm : Evm fork Meter) (address : Address) :
    accountCode (evm.prependSimulatedLogs logs) address = accountCode evm address := rfl

/-- The check of the gas left reads the same. -/
private theorem checkGas_prepend (evm : Evm fork Meter) (amount : Nat) :
    checkGas (evm.prependSimulatedLogs logs) amount = checkGas evm amount := rfl

/-- A transfer log that a simulation reports goes after the logs in front. -/
private theorem pushSimulatedTransferLog_append (fork : Fork) (rest : Array Blocks.Log)
    (sender recipient : Address) (amount : U256) :
    pushSimulatedTransferLog fork (logs ++ rest) sender recipient amount =
      logs ++ pushSimulatedTransferLog fork rest sender recipient amount := by
  unfold pushSimulatedTransferLog pushTransferLog
  split <;> (split <;> simp only [Array.append_push])

/-- The rest of an instruction that keeps its reads keeps the logs in front when the rest does.

The result of a halt must carry the logs in front through the map. -/
private theorem keepReads_prepend {α : Type} (g : α → α) (halted halted' : Evm fork Meter → α)
    (hh : ∀ e, halted' (e.prependSimulatedLogs logs) = g (halted e)) (evm : Evm fork Meter)
    (rest rest' : Except EvmError α) (h : rest' = g <$> rest) :
    keepReads (evm.prependSimulatedLogs logs) halted' rest' = g <$> keepReads evm halted rest := by
  subst h
  cases rest with
  | error e =>
    simp only [keepReads, Functor.map, Except.map]
    split
    · rfl
    · rw [exceptionalHalt_prepend, hh]
  | ok a => rfl

omit [GasMeter Meter] in
/-- A frame built with the substate of a frame with logs in front has those logs in front. -/
private theorem prepend_mk (evm : Evm fork Meter) (pc : Nat) (stack : Stack)
    (memory code : ByteArray) (valid : Array Bool) (gas : Meter) (running : Bool)
    (message : Message fork) (output returnData : ByteArray) (state : TransactionState)
    (error : Option EvmError) :
    (Evm.mk pc stack memory code valid gas running message output returnData state
        (evm.prependSimulatedLogs logs).substate error) =
      (Evm.mk pc stack memory code valid gas running message output returnData state
        evm.substate error).prependSimulatedLogs logs := rfl

/-- The caller after its callee keeps the logs in front of its own. -/
private theorem incorporateChild_prepend (caller child : Evm fork Meter) :
    incorporateChild fork (caller.prependSimulatedLogs logs) child =
      (incorporateChild fork caller child).prependSimulatedLogs logs := by
  unfold incorporateChild
  split
  · simp only [Evm.prependSimulatedLogs, Array.append_assoc]
    rfl
  · rfl

end Parts

/-- Unfold a step and move the logs in front through each of its parts.

The optional lemmas move them through further parts. -/
local syntax "prepend_free" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| prepend_free $[[$extra?,*]]?) => do
    let extra : Lean.Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
      match extra? with
      | some xs => xs
      | none => {}
    `(tactic| (simp only [popWord_prepend, pushWord_prepend, chargeGas_prepend,
                 chargeStateGas_prepend, chargeGasAndMemory_prepend, popTopics_prepend,
                 accessAddress_prepend, accessStorageKey_prepend, recordAccountRead_prepend,
                 recordStorageRead_prepend, refillStateGas_prepend, advance_prepend,
                 exceptionalHalt_prepend, accountCode_prepend, checkGas_prepend, prepend_proj,
                 prepend_simulatedLogs, prepend_mk, incorporateChild_prepend,
                 pushSimulatedTransferLog_append, bind_map_left, map_bind, map_pure, bind_assoc,
                 pure_bind, Functor.map_map, $extra,*]
               repeat' (first
                 | rfl
                 | refine congrArg (fun k => _ >>= k) (funext fun _ => ?_)
                 | refine keepReads_prepend _ _ _ _ (by intro _; rfl) _ _ _ ?_
                 | simp only [popWord_prepend, pushWord_prepend, chargeGas_prepend,
                   chargeStateGas_prepend, chargeGasAndMemory_prepend, popTopics_prepend,
                   accessAddress_prepend, accessStorageKey_prepend, recordAccountRead_prepend,
                   recordStorageRead_prepend, refillStateGas_prepend, advance_prepend,
                   exceptionalHalt_prepend, accountCode_prepend, checkGas_prepend, prepend_proj,
                   prepend_simulatedLogs, prepend_mk, incorporateChild_prepend,
                   pushSimulatedTransferLog_append, bind_map_left, map_bind, map_pure, bind_assoc,
                   pure_bind, Functor.map_map, $extra,*]
                 | (split <;> (try simp_all [map_pure, throw, throwThe, MonadExceptOf.throw])))))

/-- An instruction that keeps the logs in front of the simulated logs. -/
private def Keeps (run : Evm fork Meter → Except EvmError (Evm fork Meter)) : Prop :=
  ∀ logs evm, run (evm.prependSimulatedLogs logs) = (·.prependSimulatedLogs logs) <$> run evm

private theorem unaryOp_keeps (cost : Nat) (f : U256 → U256) :
    Keeps (unaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro logs evm
  simp only [unaryOp]
  prepend_free

private theorem binaryOp_keeps (cost : Nat) (f : U256 → U256 → U256) :
    Keeps (binaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro logs evm
  simp only [binaryOp]
  prepend_free

private theorem ternaryOp_keeps (cost : Nat) (f : U256 → U256 → U256 → U256) :
    Keeps (ternaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro logs evm
  simp only [ternaryOp]
  prepend_free

private theorem readFrame_keeps (cost : Nat) (value : Evm fork Meter → U256)
    (hvalue : ∀ logs evm, value (evm.prependSimulatedLogs logs) = value evm) :
    Keeps (readFrame cost value) := by
  intro logs evm
  simp only [readFrame]
  prepend_free
  simp only [hvalue]

private theorem readNumber_keeps (cost : Nat) (value : Evm fork Meter → Nat)
    (hvalue : ∀ logs evm, value (evm.prependSimulatedLogs logs) = value evm) :
    Keeps (readNumber cost value) := by
  intro logs evm
  simp only [readNumber, hvalue]
  split
  · exact readFrame_keeps cost _ (fun _ _ => rfl) logs evm
  · prepend_free

private theorem expStep_keeps : Keeps (expStep (Meter := Meter) fork) := by
  intro logs evm
  simp only [expStep]
  prepend_free

private theorem keccak256Step_keeps :
    Keeps (keccak256Step (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [keccak256Step]
  prepend_free

private theorem popStep_keeps : Keeps (popStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [popStep]
  prepend_free

private theorem pushN_keeps (n : Fin 33) :
    Keeps (pushN (fork := fork) (Meter := Meter) n) := by
  intro logs evm
  simp only [pushN]
  prepend_free

private theorem dupN_keeps (n : Fin 16) :
    Keeps (dupN (fork := fork) (Meter := Meter) n) := by
  intro logs evm
  simp only [dupN]
  prepend_free

private theorem swapN_keeps (n : Fin 16) :
    Keeps (swapN (fork := fork) (Meter := Meter) n) := by
  intro logs evm
  simp only [swapN]
  prepend_free

private theorem dupnStep_keeps : Keeps (dupnStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [dupnStep]
  prepend_free

private theorem swapnStep_keeps : Keeps (swapnStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [swapnStep]
  prepend_free

private theorem exchangeStep_keeps :
    Keeps (exchangeStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [exchangeStep]
  prepend_free

omit [GasMeter Meter] in
private theorem stopStep_keeps : Keeps (stopStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [stopStep]
  prepend_free

private theorem jumpStep_keeps : Keeps (jumpStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [jumpStep]
  prepend_free

private theorem jumpiStep_keeps : Keeps (jumpiStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [jumpiStep]
  prepend_free

private theorem jumpdestStep_keeps :
    Keeps (jumpdestStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [jumpdestStep]
  prepend_free

private theorem mloadStep_keeps : Keeps (mloadStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [mloadStep]
  prepend_free

private theorem mstoreStep_keeps : Keeps (mstoreStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [mstoreStep]
  prepend_free

private theorem mstore8Step_keeps :
    Keeps (mstore8Step (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [mstore8Step]
  prepend_free

private theorem mcopyStep_keeps : Keeps (mcopyStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [mcopyStep]
  prepend_free

private theorem calldataloadStep_keeps :
    Keeps (calldataloadStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [calldataloadStep]
  prepend_free

private theorem copyToMemory_keeps (base : Nat) (source : Evm fork Meter → ByteArray)
    (hsource : ∀ logs evm, source (evm.prependSimulatedLogs logs) = source evm) :
    Keeps (fun evm => copyToMemory base (source evm) evm) := by
  intro logs evm
  simp only [copyToMemory, hsource]
  prepend_free

private theorem returndatacopyStep_keeps :
    Keeps (returndatacopyStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [returndatacopyStep]
  prepend_free

private theorem returnStep_keeps : Keeps (returnStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [returnStep, haltWithOutput]
  prepend_free

private theorem revertStep_keeps : Keeps (revertStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [revertStep, haltWithOutput]
  prepend_free

private theorem blockhashStep_keeps :
    Keeps (blockhashStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [blockhashStep]
  prepend_free

private theorem blobhashStep_keeps (h : .dencun ≤ fork) :
    Keeps (blobhashStep (Meter := Meter) h) := by
  intro logs evm
  simp only [blobhashStep]
  prepend_free

private theorem logStep_keeps (n : Nat) :
    Keeps (logStep (fork := fork) (Meter := Meter) n) := by
  intro logs evm
  simp only [logStep]
  prepend_free

private theorem stackOnlyStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : stackOnlyStep fork op = some run) : Keeps run := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | with_reducible exact unaryOp_keeps _ _
    | with_reducible exact binaryOp_keeps _ _
    | with_reducible exact ternaryOp_keeps _ _
    | with_reducible exact expStep_keeps
    | with_reducible exact keccak256Step_keeps
    | with_reducible exact popStep_keeps
    | with_reducible exact pushN_keeps _
    | with_reducible exact dupN_keeps _
    | with_reducible exact swapN_keeps _
    | with_reducible exact dupnStep_keeps
    | with_reducible exact swapnStep_keeps
    | with_reducible exact exchangeStep_keeps

private theorem controlFlowStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : controlFlowStep op = some run) : Keeps run := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  · exact stopStep_keeps
  · exact jumpStep_keeps
  · exact jumpiStep_keeps
  · exact readFrame_keeps _ _ fun _ _ => rfl
  · exact readFrame_keeps _ _ fun _ _ => rfl
  · exact jumpdestStep_keeps

private theorem memoryDataStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : memoryDataStep op = some run) : Keeps run := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  all_goals first
    | with_reducible exact mloadStep_keeps
    | with_reducible exact mstoreStep_keeps
    | with_reducible exact mstore8Step_keeps
    | with_reducible exact mcopyStep_keeps
    | with_reducible exact calldataloadStep_keeps
    | with_reducible exact returndatacopyStep_keeps
    | with_reducible exact readFrame_keeps _ _ fun _ _ => rfl
    | with_reducible exact copyToMemory_keeps _ (fun evm => evm.message.data) fun _ _ => rfl
    | with_reducible exact copyToMemory_keeps _ (fun evm => evm.code) fun _ _ => rfl

private theorem returnOpStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some run) : Keeps run := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  · subst hstep
    exact returnStep_keeps
  · split at hstep
    · cases hstep
      exact revertStep_keeps
    · cases hstep

private theorem environmentStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : environmentStep fork op = some run) : Keeps run := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | with_reducible exact blockhashStep_keeps
    | with_reducible exact blobhashStep_keeps _
    | with_reducible exact readFrame_keeps _ _ fun _ _ => rfl
    | with_reducible exact readNumber_keeps _ _ fun _ _ => rfl

private theorem logOpStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : logOpStep op = some run) : Keeps run := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact logStep_keeps _


/-- BALANCE keeps the logs in front. -/
private theorem balanceStep_keeps : Keeps (balanceStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [balanceStep]
  prepend_free

/-- EXTCODESIZE keeps the logs in front. -/
private theorem extcodesizeStep_keeps :
    Keeps (extcodesizeStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [extcodesizeStep]
  prepend_free

/-- EXTCODECOPY keeps the logs in front. -/
private theorem extcodecopyStep_keeps :
    Keeps (extcodecopyStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [extcodecopyStep]
  prepend_free

/-- EXTCODEHASH keeps the logs in front. -/
private theorem extcodehashStep_keeps :
    Keeps (extcodehashStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [extcodehashStep]
  prepend_free

/-- Each instruction that reads another account keeps the logs in front. -/
private theorem accountStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some run) : Keeps run := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | exact balanceStep_keeps
    | exact extcodesizeStep_keeps
    | exact extcodecopyStep_keeps
    | exact extcodehashStep_keeps
    | (intro logs evm
       simp only [prepend_proj, recordAccountRead_prepend]
       exact readFrame_keeps _ _ (fun _ _ => rfl) _ _)

/-- SLOAD keeps the logs in front. -/
private theorem sloadStep_keeps : Keeps (sloadStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [sloadStep]
  prepend_free

/-- SSTORE keeps the logs in front. -/
private theorem sstoreStep_keeps : Keeps (sstoreStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [sstoreStep]
  prepend_free

/-- Each instruction of storage keeps the logs in front. -/
private theorem storageStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some run) : Keeps run := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep
  · exact sloadStep_keeps
  · exact sstoreStep_keeps

/-- TLOAD keeps the logs in front. -/
private theorem tloadStep_keeps : Keeps (tloadStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [tloadStep]
  prepend_free

/-- TSTORE keeps the logs in front. -/
private theorem tstoreStep_keeps : Keeps (tstoreStep (fork := fork) (Meter := Meter)) := by
  intro logs evm
  simp only [tstoreStep]
  prepend_free

/-- Each instruction of transient storage keeps the logs in front. -/
private theorem transientStorageStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some run) : Keeps run := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep
  all_goals split at hstep <;> simp only [Option.some.injEq, reduceCtorEq] at hstep
  · subst hstep
    exact tloadStep_keeps
  · subst hstep
    exact tstoreStep_keeps

omit [GasMeter Meter] in
/-- The end of SELFDESTRUCT puts its transfer log after the logs in front. -/
private theorem finishSelfdestruct_prepend (logs : Array Blocks.Log) (beneficiary : Address)
    (refund : Nat) (evm : Evm fork Meter) :
    finishSelfdestruct fork beneficiary refund (evm.prependSimulatedLogs logs) =
      (·.prependSimulatedLogs logs) <$> finishSelfdestruct fork beneficiary refund evm := by
  simp only [finishSelfdestruct]
  prepend_free

/-- SELFDESTRUCT keeps the logs in front. -/
private theorem selfdestructStep_keeps : Keeps (selfdestructStep (Meter := Meter) fork) := by
  intro logs evm
  simp only [selfdestructStep]
  prepend_free
  all_goals simp only [finishSelfdestruct_prepend]

/-- The instruction of SELFDESTRUCT keeps the logs in front. -/
private theorem selfdestructOpStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some run) : Keeps run := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact selfdestructStep_keeps

/-- Each instruction keeps the logs in front. -/
private theorem instruction_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : instruction fork op = some run) : Keeps run := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact stackOnlyStep_keeps hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact controlFlowStep_keeps hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact memoryDataStep_keeps hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact returnOpStep_keeps hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact environmentStep_keeps hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact accountStep_keeps hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact storageStep_keeps hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact transientStorageStep_keeps hf
  rcases orElse_eq_some hrun with hf | hf
  · exact logOpStep_keeps hf
  · exact selfdestructOpStep_keeps hf

/-! ## Calls and creations keep the logs in front -/

/-- The result of a step with the logs in front of each frame it gives.

A caller resumes into a frame with the logs in front too. -/
def StepResult.prependSimulatedLogs (logs : Array Blocks.Log) :
    StepResult fork Meter → StepResult fork Meter
  | .next after => .next (after.prependSimulatedLogs logs)
  | .child caller message resume =>
    .child (caller.prependSimulatedLogs logs) message
      (fun child => (·.prependSimulatedLogs logs) <$> resume child)

/-- A step that keeps the logs in front of the frames it gives. -/
private def StepKeeps (run : Evm fork Meter → Except EvmError (StepResult fork Meter)) : Prop :=
  ∀ logs evm, run (evm.prependSimulatedLogs logs) =
    StepResult.prependSimulatedLogs logs <$> run evm

/-- A call that runs no message keeps the logs in front. -/
private theorem skipCall_prepend (logs : Array Blocks.Log) (evm : Evm fork Meter)
    (gas reservoir : Nat) :
    skipCall (evm.prependSimulatedLogs logs) gas reservoir =
      (·.prependSimulatedLogs logs) <$> skipCall evm gas reservoir := by
  simp only [skipCall]
  prepend_free

/-- The caller of a call resumes with the logs in front. -/
private theorem resumeCall_prepend (logs : Array Blocks.Log) (caller : Evm fork Meter)
    (newAccount : Nat) (outputStart outputSize : U256) (child : Evm fork Meter) :
    resumeCall fork (caller.prependSimulatedLogs logs) newAccount outputStart outputSize child =
      (·.prependSimulatedLogs logs) <$>
        resumeCall fork caller newAccount outputStart outputSize child := by
  simp only [resumeCall]
  prepend_free

/-- The caller of a creation resumes with the logs in front. -/
private theorem resumeCreate_prepend (logs : Array Blocks.Log) (caller : Evm fork Meter)
    (newAccount : Nat) (address : Address) (child : Evm fork Meter) :
    resumeCreate fork (caller.prependSimulatedLogs logs) newAccount address child =
      (·.prependSimulatedLogs logs) <$> resumeCreate fork caller newAccount address child := by
  simp only [resumeCreate]
  prepend_free

/-- The caller of a call resumes with the logs in front, as a function of its callee. -/
private theorem resumeCall_prepend' (logs : Array Blocks.Log) (caller : Evm fork Meter)
    (newAccount : Nat) (outputStart outputSize : U256) :
    resumeCall fork (caller.prependSimulatedLogs logs) newAccount outputStart outputSize =
      fun child => (·.prependSimulatedLogs logs) <$>
        resumeCall fork caller newAccount outputStart outputSize child :=
  funext (resumeCall_prepend logs caller newAccount outputStart outputSize)

/-- The caller of a creation resumes with the logs in front, as a function of its child. -/
private theorem resumeCreate_prepend' (logs : Array Blocks.Log) (caller : Evm fork Meter)
    (newAccount : Nat) (address : Address) :
    resumeCreate fork (caller.prependSimulatedLogs logs) newAccount address =
      fun child => (·.prependSimulatedLogs logs) <$>
        resumeCreate fork caller newAccount address child :=
  funext (resumeCreate_prepend logs caller newAccount address)

omit [GasMeter Meter] in
/-- A successful step with the logs in front gives its result with the logs in front. -/
private theorem map_ok_prepend (logs : Array Blocks.Log) (result : StepResult fork Meter) :
    StepResult.prependSimulatedLogs logs <$> (Except.ok result : Except EvmError _) =
      .ok (result.prependSimulatedLogs logs) := rfl

/-- A successful value binds as itself. -/
private theorem ok_bind {α β ε : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

omit [GasMeter Meter] in
/-- The pops of the operands of a call keep the logs in front. -/
private theorem popCallOperands_prepend (logs : Array Blocks.Log) (kind : CallKind)
    (evm : Evm fork Meter) :
    popCallOperands kind (evm.prependSimulatedLogs logs) =
      (fun p => (p.1, p.2.prependSimulatedLogs logs)) <$> popCallOperands kind evm := by
  simp only [popCallOperands, popCallValue]
  prepend_free [ok_bind]

/-- The access to a delegate keeps the logs in front. -/
private theorem accessDelegation_prepend (logs : Array Blocks.Log) (evm : Evm fork Meter)
    (address : Address) (known : Nat) :
    accessDelegation (evm.prependSimulatedLogs logs) address known =
      (fun p => (p.1, p.2.prependSimulatedLogs logs)) <$> accessDelegation evm address known := by
  simp only [accessDelegation]
  prepend_free

/-- The payment of a call keeps the logs in front. -/
private theorem payCall_prepend (logs : Array Blocks.Log) (kind : CallKind) (call : CallOperands)
    (memoryCost extraGas newAccount : Nat) (evm : Evm fork Meter) :
    payCall kind call memoryCost extraGas newAccount (evm.prependSimulatedLogs logs) =
      (fun p => (p.1, p.2.prependSimulatedLogs logs)) <$>
        payCall kind call memoryCost extraGas newAccount evm := by
  simp only [payCall]
  prepend_free

/-- The end of a call keeps the logs in front. -/
private theorem finishCall_prepend (logs : Array Blocks.Log) (kind : CallKind)
    (call : CallOperands) (callee : Callee) (subCall newAccount expandBy : Nat)
    (evm : Evm fork Meter) :
    finishCall kind call callee subCall newAccount expandBy (evm.prependSimulatedLogs logs) =
      StepResult.prependSimulatedLogs logs <$>
        finishCall kind call callee subCall newAccount expandBy evm := by
  simp only [finishCall, genericCall, callerFrame, callMessage]
  prepend_free [skipCall_prepend, resumeCall_prepend', map_ok_prepend,
    StepResult.prependSimulatedLogs]

/-- Each call keeps the logs in front. -/
private theorem callStep_keeps (kind : CallKind) :
    StepKeeps (callStep (fork := fork) (Meter := Meter) kind) := by
  intro logs evm
  simp only [callStep]
  prepend_free [popCallOperands_prepend, accessDelegation_prepend, payCall_prepend,
    finishCall_prepend]

omit [GasMeter Meter] in
/-- The pop of the salt keeps the logs in front. -/
private theorem popSalt_prepend (logs : Array Blocks.Log) (create2 : Bool)
    (evm : Evm fork Meter) :
    popSalt create2 (evm.prependSimulatedLogs logs) =
      (fun p => (p.1, p.2.prependSimulatedLogs logs)) <$> popSalt create2 evm := by
  simp only [popSalt]
  prepend_free

/-- A creation once it has paid keeps the logs in front. -/
private theorem launchCreate_prepend (logs : Array Blocks.Log) (evm : Evm fork Meter)
    (value : U256) (initCode : ByteArray) (salt : Option U256) :
    launchCreate (evm.prependSimulatedLogs logs) value initCode salt =
      StepResult.prependSimulatedLogs logs <$> launchCreate evm value initCode salt := by
  simp only [launchCreate]
  prepend_free [skipCall_prepend, resumeCreate_prepend', map_ok_prepend,
    StepResult.prependSimulatedLogs]

/-- Each creation keeps the logs in front. -/
private theorem createStep_keeps (create2 : Bool) :
    StepKeeps (createStep (fork := fork) (Meter := Meter) create2) := by
  intro logs evm
  simp only [createStep, genericCreate]
  prepend_free [popSalt_prepend, launchCreate_prepend]

/-- Each instruction that may send a message keeps the logs in front. -/
private theorem messageInstruction_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    (hrun : messageInstruction fork op = some run) : StepKeeps run := by
  unfold messageInstruction at hrun
  rcases orElse_eq_some hrun with hrun | hrun
  · cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals (try split at hrun) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hrun)
    all_goals first
      | exact callStep_keeps _
      | (subst hrun; exact callStep_keeps _)
      | cases hrun
  · cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals (try split at hrun) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hrun)
    all_goals first
      | exact createStep_keeps _
      | (subst hrun; exact createStep_keeps _)
      | cases hrun

/-- A step from a frame with `logs` in front of its simulated logs gives the same result.

Each frame it gives has `logs` in front, and so does each frame a caller resumes into.

It holds of every frame, so no step reads the simulated logs. -/
theorem step_prependSimulatedLogs (logs : Array Blocks.Log) (evm : Evm fork Meter) :
    step fork (evm.prependSimulatedLogs logs) =
      StepResult.prependSimulatedLogs logs <$> step fork evm := by
  unfold step
  by_cases h : evm.pc < evm.code.size
  · simp only [prepend_proj, h, dite_true]
    rcases Op.ofByte fork evm.code[evm.pc] with _ | op
    · rfl
    · dsimp only
      rcases hi : instruction fork op with _ | run
      · dsimp only
        rcases hm : messageInstruction fork op with _ | run
        · rfl
        · exact messageInstruction_keeps hm logs evm
      · simp only [instruction_keeps hi logs evm, Functor.map_map]
        rfl
  · simp only [prepend_proj, h, dite_false, stopStep_keeps logs evm, Functor.map_map]
    rfl

/-! ## Runs keep the logs in front -/

/-- A frame that ends a run, with the logs in front, and the same bound on its gas. -/
private def prependEnded (logs : Array Blocks.Log) {bound : Nat}
    (after : { after : Evm fork Meter // GasMeter.gasHeld after.gas ≤ bound }) :
    { after : Evm fork Meter // GasMeter.gasHeld after.gas ≤ bound } :=
  ⟨after.val.prependSimulatedLogs logs, after.property⟩

/-- A run of a frame with the logs in front ends with them in front.

Each message that a step sends must run alike from callers that differ only in those logs. -/
private theorem runFrameWith_prepend [LawfulGasMeter Meter] (logs : Array Blocks.Log)
    {bound : Nat} (runChild : MessageRunner fork Meter bound)
    (children : ∀ caller message lt,
      runChild (caller.prependSimulatedLogs logs) message lt = runChild caller message lt)
    (evm : Evm fork Meter) (within : GasMeter.gasHeld evm.gas ≤ bound)
    (within' : GasMeter.gasHeld (evm.prependSimulatedLogs logs).gas ≤ bound) :
    runFrameWith (fun _ _ => pure ()) (step fork) (step_decreases fork) bound runChild
        (evm.prependSimulatedLogs logs) within' =
      prependEnded logs <$>
        runFrameWith (fun _ _ => pure ()) (step fork) (step_decreases fork) bound runChild evm
          within := by
  induction h : measure evm using Nat.strongRecOn generalizing evm with
  | _ n ih =>
  subst h
  generalize hl : runFrameWith (fun _ _ => pure ()) (step fork) (step_decreases fork) bound
    runChild (evm.prependSimulatedLogs logs) within' = l
  generalize hr : runFrameWith (fun _ _ => pure ()) (step fork) (step_decreases fork) bound
    runChild evm within = r
  rw [runFrameWith] at hl hr
  by_cases running : evm.running
  · have running' : (evm.prependSimulatedLogs logs).running = true := running
    simp only [running, running', dite_true] at hl hr
    have hstep := step_prependSimulatedLogs logs evm
    split at hl <;> rename_i hs <;> subst hl <;> split at hr <;> rename_i hs' <;>
      rw [hs, hs'] at hstep <;>
      simp only [Functor.map, Except.map, StepResult.prependSimulatedLogs, Except.error.injEq,
        Except.ok.injEq, reduceCtorEq, StepResult.next.injEq, StepResult.child.injEq] at hstep
    · subst hstep hr
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
      split <;> rfl
    · subst hstep hr
      simp only [bind, Except.bind, pure, Except.pure]
      exact ih _ (step_decreases fork running hs') _ _ _ rfl
    · obtain ⟨rfl, rfl, rfl⟩ := hstep
      subst hr
      rename_i message caller resume
      rw [children]
      simp only [bind, Except.bind, pure, Except.pure]
      rcases hc : runChild caller message
        (Nat.lt_of_lt_of_le (step_decreases fork running hs').1 within) with e | ⟨child, used⟩
      · rfl
      · dsimp only
        obtain ⟨e, hres⟩ | ⟨after, hres⟩ :
            (∃ e, resume child = .error e) ∨ ∃ after, resume child = .ok after := by
          cases resume child <;> simp
        · rw [runFrameWith_match_error hres]
          split <;> rename_i heq <;> rw [hres] at heq <;> cases heq
          by_cases ha : e.aborts = true <;>
            simp [ha, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map, prependEnded]
          rfl
        · rw [runFrameWith_match_ok hres]
          split <;> rename_i heq <;> rw [hres] at heq <;> cases heq
          exact ih _ ((step_decreases fork running hs').2 child _ used hres) _ _ _ rfl
  · have running' : (evm.prependSimulatedLogs logs).running = false :=
      Bool.eq_false_iff.mpr running
    simp only [running, running'] at hl hr
    subst hl hr
    rfl

omit [GasMeter Meter] in
/-- The frame of a message starts with the logs in front when its substate does. -/
private theorem startFrame_mk (logs : Array Blocks.Log) (message : Message fork)
    (state : TransactionState) (accountsToDelete : Std.ExtTreeSet Address)
    (logs' rest : Array Blocks.Log) (touched : Std.ExtTreeSet Address) (refund : Int)
    (addresses : Std.ExtTreeSet Address)
    (keys : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)) (meter : Meter) :
    startFrame message state
        (Substate.mk accountsToDelete logs' (logs ++ rest) touched refund addresses keys) meter =
      (startFrame message state
        (Substate.mk accountsToDelete logs' rest touched refund addresses keys)
        meter).prependSimulatedLogs logs := rfl

/-- A map of ended frames commutes with putting the logs in front when each frame does. -/
private theorem map_prependEnded (logs : Array Blocks.Log) {bound bound' : Nat}
    (r : { after : Evm fork Meter // GasMeter.gasHeld after.gas ≤ bound } →
      { after : Evm fork Meter // GasMeter.gasHeld after.gas ≤ bound' })
    (hr : ∀ x, r (prependEnded logs x) = prependEnded logs (r x))
    (x : Except EvmError { after : Evm fork Meter // GasMeter.gasHeld after.gas ≤ bound }) :
    r <$> (prependEnded logs <$> x) = prependEnded logs <$> (r <$> x) := by
  cases x <;> simp [Functor.map, Except.map, hr]

/-- The rollback of a failed frame keeps the logs in front. -/
private theorem rollbackOnError_prepend (logs : Array Blocks.Log) (snapshot : TransactionState)
    (evm : Evm fork Meter) :
    rollbackOnError snapshot (evm.prependSimulatedLogs logs) =
      (rollbackOnError snapshot evm).prependSimulatedLogs logs := by
  unfold rollbackOnError
  by_cases h : evm.error.isSome = true <;>
    simp only [prepend_proj, h, ite_true, ite_false, Bool.false_eq_true] <;> rfl

/-- A precompile keeps the logs in front. -/
private theorem runPrecompile_prepend (logs : Array Blocks.Log) (address : Nat)
    (evm : Evm fork Meter) :
    runPrecompile fork address (evm.prependSimulatedLogs logs) =
      (·.prependSimulatedLogs logs) <$> runPrecompile fork address evm := by
  unfold runPrecompile
  simp only [prepend_proj]
  split
  · rfl
  · rfl
  · split <;> rfl

/-- The deposit of the code keeps the logs in front. -/
private theorem depositCode_prepend (logs : Array Blocks.Log) (snapshot : TransactionState)
    (evm : Evm fork Meter) :
    depositCode fork snapshot (evm.prependSimulatedLogs logs) =
      (·.prependSimulatedLogs logs) <$> depositCode fork snapshot evm := by
  simp only [depositCode]
  prepend_free [ok_bind]

/-- A call that starts with `logs` in front of its simulated logs ends with them in front.

Its frame is otherwise the same, and so is an error that aborts it. -/
theorem processMessage_prependSimulatedLogs [LawfulGasMeter Meter] (logs : Array Blocks.Log)
    (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
    (held : GasMeter.gasHeld meter ≤ message.gas) :
    processMessage fork message state
        { substate with simulatedLogs := logs ++ substate.simulatedLogs } meter held =
      (fun ended => ⟨ended.val.prependSimulatedLogs logs, ended.property⟩) <$>
        processMessage fork message state substate meter held := by
  show _ = prependEnded logs <$> _
  rw [processMessage, processMessage, processMessageWith, processMessageWith]
  by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
  · obtain ⟨hs, hv⟩ := ht
    simp only [hs, hv, ne_eq, not_false_eq_true, and_self, ite_true,
      pushSimulatedTransferLog_append, liftExcept, bind, Except.bind, Except.mapError]
    rcases (startState fork message state).moveEther fork message.caller message.currentTarget
      message.value with err | moved
    · rfl
    · simp only [startFrame_mk, pure, Except.pure]
      refine Eq.trans ?_ (map_prependEnded logs _ (fun x => Subtype.ext ?_) _)
      · refine congrArg (_ <$> ·) ?_
        rcases hp : precompileAddress fork message with _ | address
        · exact runFrameWith_prepend logs _ (fun _ _ _ => rfl) _ _ _
        · dsimp only
          by_cases hd : message.disablePrecompiles = true
          · simp only [hd, ite_true]
            rfl
          · simp only [hd, Bool.false_eq_true, ite_false]
            split <;> rename_i h1 <;> split <;> rename_i h2 <;>
              simp only [hs, hv, not_false_eq_true, and_self, ite_true] at h2 <;>
              simp only [hs, hv, not_false_eq_true, and_self, ite_true,
                pushSimulatedTransferLog_append, startFrame_mk, runPrecompile_prepend, h2] at h1 <;>
              cases h1 <;> rfl
      · exact rollbackOnError_prepend logs state x.val
  · simp only [ht, ite_false, pure, bind, Except.bind, Except.pure, startFrame_mk]
    refine Eq.trans ?_ (map_prependEnded logs _ (fun x => Subtype.ext ?_) _)
    · refine congrArg (_ <$> ·) ?_
      rcases hp : precompileAddress fork message with _ | address
      · exact runFrameWith_prepend logs _ (fun _ _ _ => rfl) _ _ _
      · dsimp only
        by_cases hd : message.disablePrecompiles = true
        · simp only [hd, ite_true]
          rfl
        · simp only [hd, Bool.false_eq_true, ite_false]
          split <;> rename_i h1 <;> split <;> rename_i h2 <;>
            simp only [ht, ite_false, startFrame_mk, runPrecompile_prepend] at h1 h2 <;>
            change (·.prependSimulatedLogs logs) <$> runPrecompile fork address
              (startFrame message (startState fork message state) substate meter) = _ at h1 <;>
            rw [h2] at h1 <;> cases h1 <;> rfl
    · exact rollbackOnError_prepend logs state x.val

/-- A creation that starts with `logs` in front of its simulated logs ends with them in front.

Its frame is otherwise the same, and so is an error that aborts it. -/
theorem processCreateMessage_prependSimulatedLogs [LawfulGasMeter Meter]
    (logs : Array Blocks.Log) (message : Message fork) (state : TransactionState)
    (substate : Substate) (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas) :
    processCreateMessage fork message state
        { substate with simulatedLogs := logs ++ substate.simulatedLogs } meter held =
      (fun ended => ⟨ended.val.prependSimulatedLogs logs, ended.property⟩) <$>
        processCreateMessage fork message state substate meter held := by
  have call := processMessage_prependSimulatedLogs (Meter := Meter) logs message
  unfold processMessage at call
  show _ = prependEnded logs <$> _
  rw [processCreateMessage, processCreateMessage, processCreateMessageWith,
    processCreateMessageWith]
  rcases prepareCreation fork state message.currentTarget with err | prepared
  · rfl
  simp only [pure, Except.pure] at call
  simp only [liftExcept, bind, Except.bind, pure, Except.pure]
  rw [call]
  rcases processMessageWith fork (fun _ _ => (Except.ok () : Except EvmError Unit)) message
    prepared substate meter held with err | ⟨evm, used⟩
  · rfl
  dsimp only [Functor.map, Except.map]
  obtain ⟨e, hd⟩ | ⟨after, hd⟩ : (∃ e, depositCode fork state evm = .error e) ∨
      ∃ after, depositCode fork state evm = .ok after := by
    cases depositCode fork state evm <;> simp
  · have hd' : depositCode fork state (evm.prependSimulatedLogs logs) = .error e := by
      rw [depositCode_prepend, hd]
      rfl
    rw [processCreateMessageWith_match_error hd', processCreateMessageWith_match_error hd]
    rfl
  · have hd' : depositCode fork state (evm.prependSimulatedLogs logs) =
        .ok (after.prependSimulatedLogs logs) := by
      rw [depositCode_prepend, hd]
      rfl
    rw [processCreateMessageWith_match_ok hd', processCreateMessageWith_match_ok hd]
    rfl

/-- A call that starts with some simulated logs ends as the call that starts with none.

The frames are equal once their simulated logs are erased. -/
private theorem processMessage_erase_empty [LawfulGasMeter Meter] (logs : Array Blocks.Log)
    (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
    (held : GasMeter.gasHeld meter ≤ message.gas) :
    (fun ended => ended.val.eraseSimulatedLogs) <$>
        processMessage fork message state { substate with simulatedLogs := logs } meter held =
      (fun ended => ended.val.eraseSimulatedLogs) <$>
        processMessage fork message state { substate with simulatedLogs := #[] } meter held := by
  have h := processMessage_prependSimulatedLogs logs message state
    { substate with simulatedLogs := #[] } meter held
  simp only [Array.append_empty] at h
  rw [h, Functor.map_map]
  rfl

/-- A creation that starts with some simulated logs ends as the creation that starts with none.

The frames are equal once their simulated logs are erased. -/
private theorem processCreateMessage_erase_empty [LawfulGasMeter Meter]
    (logs : Array Blocks.Log) (message : Message fork) (state : TransactionState)
    (substate : Substate) (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas) :
    (fun ended => ended.val.eraseSimulatedLogs) <$>
        processCreateMessage fork message state { substate with simulatedLogs := logs } meter
          held =
      (fun ended => ended.val.eraseSimulatedLogs) <$>
        processCreateMessage fork message state { substate with simulatedLogs := #[] } meter
          held := by
  have h := processCreateMessage_prependSimulatedLogs logs message state
    { substate with simulatedLogs := #[] } meter held
  simp only [Array.append_empty] at h
  rw [h, Functor.map_map]
  rfl

/-- Two calls that differ only in their simulated logs at the start differ only in them at the end.

Both fail with the same error, or both end with frames equal but for their simulated logs. -/
theorem processMessage_eraseSimulatedLogs [LawfulGasMeter Meter] (logs : Array Blocks.Log)
    (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
    (held : GasMeter.gasHeld meter ≤ message.gas) :
    (fun ended => ended.val.eraseSimulatedLogs) <$>
        processMessage fork message state { substate with simulatedLogs := logs } meter held =
      (fun ended => ended.val.eraseSimulatedLogs) <$>
        processMessage fork message state substate meter held := by
  rw [processMessage_erase_empty]
  exact (processMessage_erase_empty substate.simulatedLogs message state substate meter held).symm

/-- Two creations that differ only in their simulated logs at the start differ only in them.

Both fail with the same error, or both end with frames equal but for their simulated logs. -/
theorem processCreateMessage_eraseSimulatedLogs [LawfulGasMeter Meter]
    (logs : Array Blocks.Log) (message : Message fork) (state : TransactionState)
    (substate : Substate) (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas) :
    (fun ended => ended.val.eraseSimulatedLogs) <$>
        processCreateMessage fork message state { substate with simulatedLogs := logs } meter
          held =
      (fun ended => ended.val.eraseSimulatedLogs) <$>
        processCreateMessage fork message state substate meter held := by
  rw [processCreateMessage_erase_empty]
  exact (processCreateMessage_erase_empty substate.simulatedLogs message state substate meter
    held).symm

end EthLib.Execution.Evm

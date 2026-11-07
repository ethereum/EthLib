module

public import EthLib.Execution.Proofs.Evm.Logic.Log
public import EthLib.Execution.Proofs.Evm.Logic.Examples.CallFlag

/-!
# Proofs: a contract that appends one log with a word of its call data

This example proves a contract that appends a log.

- At 0, `60 00 35 60 00 52` writes the word `w` of call data at offset 0 at offset 0 of memory.
- At 6, `60 2a 60 20 60 00` pushes the topic 42 and the range of 32 bytes at 0.
- At 12, `a1` is LOG1.
- At 13, `60 00 60 00 f3` returns no bytes.

The contract appends one log of the current address, with the topic 42 and the 32 bytes of `w`.

It changes nothing else, and costs 1036 gas.

The frame must be one that may change the state, since LOG1 fails in a static frame.

The rules are those of one counter of gas, at every fork.

The example says nothing of a log that a later revert of a caller drops.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.Emit

open EthLib.Base (Fork U256)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- The bytecode of the contract. -/
def CODE : ByteArray := ⟨#[0x60, 0x00, 0x35, 0x60, 0x00, 0x52, 0x60, 0x2a, 0x60, 0x20, 0x60, 0x00,
  0xa1, 0x60, 0x00, 0x60, 0x00, 0xf3]⟩

/-- The first word of a call data. -/
def word (data : ByteArray) : U256 := loadWord data 0 32

variable {message : Message fork} {state : TransactionState} {substate : Substate}

/-- The log that the contract appends: the current address, the topic 42, and the word. -/
def LOG (message : Message fork) : Blocks.Log :=
  { address := message.currentTarget
    topics := [U256.toBeBytes 42]
    data := wordBytes (word message.data) }

/-- The specification of the contract: it appends its log, returns no bytes, and pays 1036 gas.

The frame may change the state. -/
theorem spec (hstatic : message.isStatic = false) {gas : Nat} (hgas : 1036 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - 1036) state
        { substate with logs := substate.logs.push (LOG message) }) := by
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas) (byte := 0x00)
    (by decide) rfl rfl (by omega) (by decide)
  have h2 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 2) (start := 0) (rest := [])
    (gas := gas - 3) (by decide) rfl (by omega)
  have h3 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 3) (stack := [word message.data]) (memory := .empty)
    (gas := gas - 3 - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have hext : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have h4 := Logic.mstore (fork := fork) (code := CODE) (message := message) (pc := 5)
    (start := 0) (value := word message.data) (rest := []) (memory := .empty)
    (gas := gas - 3 - 3 - 3) (state := state) (substate := substate) (by decide) rfl
    (by simp only [hext]; omega)
  have h0 : (0 : U256).toNat = 0 := rfl
  rw [hext, h0, CallFlag.memoryWrite_word] at h4
  have h5 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 6) (stack := []) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3)) (byte := 0x2a) (by decide) rfl rfl (by omega) (by decide)
  have h6 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 8) (stack := [42]) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3) (byte := 0x20) (by decide) rfl rfl (by omega)
    (by decide)
  have h7 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 10) (stack := [32, 42]) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3) (byte := 0x00) (by decide) rfl rfl (by omega)
    (by decide)
  have hgrow : extendMemory (wordBytes (word message.data)).size [((0 : U256), (32 : U256))] =
      ⟨0, 0⟩ := by
    rw [size_wordBytes]
    decide
  have hcost : logCost (1 : Fin 5).val (32 : U256) = 1006 := by
    unfold logCost
    rw [show (32 : U256).toNat = 32 from rfl]
    rfl
  have h8 := log (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := wordBytes (word message.data)) (pc := 12) (n := 1)
    (byte := 0xa1) (start := 0) (size := 32) (words := [42]) (rest := [])
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3) rfl (by decide) rfl rfl hstatic
    (by rw [hgrow, hcost]; show 1006 + 0 ≤ _; omega)
  rw [hgrow, memoryExtend_zero] at h8
  have hdata : memoryReadBytes (wordBytes (word message.data)) (0 : U256).toNat (32 : U256).toNat =
      wordBytes (word message.data) := by
    have h := memoryReadBytes_whole (memory := wordBytes (word message.data))
    rwa [size_wordBytes] at h
  rw [hdata, hcost] at h8
  change Hoare fork _ (At CODE message (12 + 1) [] (wordBytes (word message.data))
    (gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3 - 1006) state
    { substate with logs := substate.logs.push (LOG message) }) at h8
  have h9 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := { substate with logs := substate.logs.push (LOG message) }) (pc := 13)
    (stack := []) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3 - 1006) (byte := 0x00) (by decide) rfl rfl
    (by omega) (by decide)
  have h10 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := { substate with logs := substate.logs.push (LOG message) }) (pc := 15)
    (stack := [0]) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3 - 1006 - 3) (byte := 0x00) (by decide) rfl rfl
    (by omega) (by decide)
  have hnone : extendMemory (wordBytes (word message.data)).size [((0 : U256), (0 : U256))] =
      ⟨0, 0⟩ := by
    simp [extendMemory]
  have h11 := Logic.«return» (fork := fork) (code := CODE) (message := message) (pc := 17)
    (start := 0) (size := 0) (rest := []) (memory := wordBytes (word message.data))
    (gas := gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3 - 1006 - 3 - 3) (state := state)
    (substate := { substate with logs := substate.logs.push (LOG message) }) (by decide) rfl
    (by rw [hnone]; exact Nat.zero_le _)
  rw [hnone] at h11
  have hread : memoryReadBytes (memoryExtend (wordBytes (word message.data)) 0) (0 : U256).toNat
      (0 : U256).toNat = .empty := rfl
  have hg : gas - 3 - 3 - 3 - (3 + 3) - 3 - 3 - 3 - 1006 - 3 - 3 - 0 = gas - 1036 := by omega
  have hc := h1.seq h2 |>.seq h3 |>.seq h4 |>.seq h5 |>.seq h6 |>.seq h7 |>.seq h8 |>.seq h9
    |>.seq h10
  exact Spec.seq hc (h11.consequence (fun _ hp => hp) fun _ hq => by rw [hread, hg] at hq; exact hq)

/-- The loop of the interpreter runs the code to its specification.

It holds for every bound on the gas of messages and every runner of messages.

The code sends no message. -/
theorem runFrame_spec (hstatic : message.isStatic = false) {gas : Nat} (hgas : 1036 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted false .empty (gas - 1036) state
        { substate with logs := substate.logs.push (LOG message) } stopped :=
  (spec hstatic hgas).runFrame start within

end EthLib.Execution.Evm.Logic.Emit

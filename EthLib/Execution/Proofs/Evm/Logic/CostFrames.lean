module

public import EthLib.Execution.Proofs.Evm.Logic.Cost
public import EthLib.Execution.Proofs.Evm.Logic.Subroutine
public import EthLib.Execution.Proofs.Evm.Logic.LessGas

/-!
# Proofs: upper bounds on gas over the frames of a code

These rules bound the gas of a run between frames of a code, with the meter of one counter.

They cover a triple that names the gas at both ends, and the call of a subroutine.

They also cover a specification that holds from every gas above a threshold.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- A running frame of a code that names every field of the frame except its gas. -/
def AtAny (code : ByteArray) (message : Message fork) (pc : Nat) (stack : List U256)
    (memory : ByteArray) (state : State.TransactionState) (substate : Substate)
    (returnData : ByteArray) (evm : Evm fork Nat) : Prop :=
  ∃ gas, At code message pc stack memory gas state substate returnData evm

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory memory' : ByteArray} {gas : Nat} {state state' : State.TransactionState}
  {substate substate' : Substate} {returnData returnData' : ByteArray}

namespace Costs

variable {S : Evm fork Nat → Evm fork Nat → Prop} {P Q : Evm fork Nat → Prop}

/-- A triple from each gas `g` from `need` on, to frames that hold at least `g - cost` gas.

It bounds the cost by `cost` from every frame that holds at least `need` gas. -/
theorem of_gas {need cost : Nat} {F : Nat → Evm fork Nat → Prop}
    -- The predicate `F g` names the gas `g` of a frame.
    (hF : ∀ g evm, F g evm → evm.gas = g)
    (h : ∀ g, need ≤ g → Triple S (F g) fun evm => g - cost ≤ evm.gas ∧ Q evm) :
    Costs S (fun evm => (∃ g, F g evm) ∧ need ≤ evm.gas) Q cost := by
  rintro evm ⟨⟨g, hg⟩, hn⟩
  have he := hF g evm hg
  obtain ⟨after, hr, hle, hq⟩ := h g (by omega) evm hg
  exact ⟨after, hr, hq, by omega⟩

end Costs

/-! ## Subroutines -/

/-- A subroutine of `code` at `entry` that needs `need` gas and spends at most `cost`.

From the block, with `args` on top of the return address, the frame reaches the return address.

The frame goes from `memory`, `state` and `substate` to `memory'`, `state'` and `substate'`.

Its return data goes from `returnData` to `returnData'`. -/
def CostSubroutine (code : ByteArray) (message : Message fork) (entry : Nat)
    (args results : List U256) (room need cost : Nat) (memory memory' : ByteArray)
    (state state' : State.TransactionState) (substate substate' : Substate)
    (returnData returnData' : ByteArray) : Prop :=
  -- It holds for every return address and every stack under the arguments.
  ∀ (ret : U256) (rest : List U256),
    -- The return address must be a JUMPDEST of the code, since the block jumps back to it.
    isValidJumpDest (validJumpDestinations code) ret.toNat = true →
    -- The stack under the return address must leave room for the `room` words the block pushes.
    args.length + 1 + rest.length + room ≤ STACK_LIMIT →
    Costs (Step fork)
      (fun evm => AtAny code message entry (args ++ ret :: rest) memory state substate returnData
        evm ∧ need ≤ evm.gas)
      -- The block jumps back to the return address with `results` on top of the same stack.
      (AtAny code message ret.toNat (results ++ rest) memory' state' substate' returnData') cost

/-- A subroutine that pays exactly `cost` needs `cost` gas and spends at most `cost`. -/
theorem Subroutine.toCost {entry : Nat} {args results : List U256} {room cost : Nat}
    (h : Subroutine code message entry args results room cost memory memory' state state' substate
      substate' returnData returnData') :
    CostSubroutine code message entry args results room cost cost memory memory' state state'
      substate substate' returnData returnData' := fun ret rest vret hroom =>
  Costs.of_gas (F := fun g => At code message entry (args ++ ret :: rest) memory g state substate
      returnData) (fun _ _ h => h.2.2.2.2.2.2.1) fun g hg =>
    (h ret rest g vret hroom hg).consequence (fun _ h => h) fun _ h =>
      ⟨Nat.le_of_eq h.2.2.2.2.2.2.1.symm, _, h⟩

/-- A call of a subroutine that spends at most `cost`: PUSHn of the address of its block, then JUMP.

The call needs 11 more gas than the block, and spends at most 11 more. -/
theorem callCostSubroutine {n : Fin 33} {entry ret : U256} {args results rest : List U256}
    {room need cost : Nat}
    (h : CostSubroutine code message entry.toNat args results room need cost memory memory' state
      state' substate substate' returnData returnData')
    (hn : n.val ≠ 0) (hlt : pc < code.size) (hbyte : code[pc] = 0x5f + UInt8.ofNat n.val)
    (decoded : Op.decode (0x5f + UInt8.ofNat n.val) = some (.push n))
    (hword : pushData code pc n = entry) (hjlt : pc + (1 + n) < code.size)
    (hjump : code[pc + (1 + n)] = 0x56)
    -- The address of the block is a JUMPDEST of the code, and so is the return address.
    (ventry : isValidJumpDest (validJumpDestinations code) entry.toNat = true)
    (vret : isValidJumpDest (validJumpDestinations code) ret.toNat = true)
    -- The stack under the return address leaves room for the words that the block pushes.
    (hroom : args.length + 1 + rest.length + room ≤ STACK_LIMIT)
    -- The stack also has room for the address of the block, below the limit of 1024 words.
    (hpush : args.length + 1 + rest.length < STACK_LIMIT) :
    Costs (Step fork)
      (fun evm => AtAny code message pc (args ++ ret :: rest) memory state substate returnData
        evm ∧ 11 + need ≤ evm.gas)
      (AtAny code message ret.toNat (results ++ rest) memory' state' substate' returnData')
      (11 + cost) := by
  -- The push and the jump spend 11 and keep the stack, then the block runs.
  have jumped : Costs (Step fork)
      (fun evm => AtAny code message pc (args ++ ret :: rest) memory state substate returnData
        evm ∧ 11 ≤ evm.gas)
      (AtAny code message entry.toNat (args ++ ret :: rest) memory state substate returnData)
      11 :=
    Costs.of_gas (F := fun g => At code message pc (args ++ ret :: rest) memory g state substate
        returnData) (fun _ _ h => h.2.2.2.2.2.2.1) fun g hg =>
      (pushJump hn hlt hbyte decoded hword hjlt hjump ventry
        (by simp only [List.length_append, List.length_cons]; omega) hg).consequence
        (fun _ h => h) fun _ h => ⟨Nat.le_of_eq h.2.2.2.2.2.2.1.symm, _, h⟩
  exact (Costs.seq_need jumped (h ret rest vret hroom)).consequence
    (fun evm ⟨hat, hn⟩ => ⟨hat, Nat.max_le.mpr ⟨by omega, hn⟩⟩) fun _ h => h

/-! ## Specifications from every gas above a threshold -/

/-- A specification to a normal halt from every gas from `B` on, over steps monotone in gas.

From a frame with at least `B` gas, the run spends at most `B`. -/
theorem Costs.of_specG {B : Nat} {Q : Evm fork Nat → Prop}
    (h : ∀ g, B ≤ g →
      SpecG fork (At code message pc stack memory g state substate returnData) Q)
    -- The postcondition is a normal halt, with no error.
    (hok : ∀ evm, Q evm → evm.error = none) :
    Costs (StepG fork)
      (fun evm => AtAny code message pc stack memory state substate returnData evm ∧
        B ≤ evm.gas)
      (fun evm => evm.running = false ∧ Q evm) B := by
  rintro evm ⟨⟨g, hat⟩, hB⟩
  rw [hat.2.2.2.2.2.2.1] at hB ⊢
  -- The frame is the frame `low` with `B` gas, with `g - B` more.
  let low : Evm fork Nat := { evm with gas := B }
  have hlow : At code message pc stack memory B state substate returnData low := by
    obtain ⟨h1, h2, h3, h4, h5, h6, -, h8, h9, h10, h11, h12, h13⟩ := hat
    exact ⟨h1, h2, h3, h4, h5, h6, rfl, h8, h9, h10, h11, h12, h13⟩
  have heq : evm = addGas (g - B) low := by
    have hg : evm.gas = g := hat.2.2.2.2.2.2.1
    show evm = { evm with gas := B + (g - B) }
    rw [Nat.add_sub_cancel' hB, ← hg]
  -- The loop runs `low` to a halt `s` with no error, for any runner of messages.
  obtain ⟨s, hs, hq⟩ := SpecG.runFrame (h B (Nat.le_refl B)) hlow
    (runChild := fun _ _ _ => .error .outOfGas) (bound := B) (Nat.le_refl B)
  -- The run from the frame halts at `s` with `g - B` more gas.
  obtain ⟨z, hr, hzrun, hqz⟩ := h g hB evm hat
  have hzs := low_of_reaches hr hzrun (g - B) low heq (Nat.le_refl B) hs (hok s hq)
  refine ⟨z, hr, ⟨hzrun, hqz⟩, ?_⟩
  rw [hzs, gas_addGas]
  omega

end EthLib.Execution.Evm.Logic

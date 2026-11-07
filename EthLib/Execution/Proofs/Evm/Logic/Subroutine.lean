module

public import EthLib.Execution.Proofs.Evm.Logic.Known

/-!
# Proofs: subroutines inside a code

Bytecode often reuses a block of its own code, as a subroutine, with JUMP.

The caller pushes an address to come back to, then the arguments, then the address of the block.

It jumps there, and the block jumps back to the return address once it has its results.

The EVM has no instruction for this: the convention lives only in the code.

A specification of such a block holds for every return address and every stack under the arguments.

- The return address must be a JUMPDEST of the code, since the block jumps back to it.
- The stack must leave room for the words that the block pushes, up to the limit of 1024 words.
- The frame must hold at least the gas of the block, and the block keeps the rest.

The block then reaches the return address, with its results in place of its arguments.

So one proof of the block serves at every place in the code that calls it.

The rule for a call composes the push of the address of the block and the JUMP with that proof.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- A specification of the block of `code` at `entry`, a subroutine.

It holds for every return address that is a JUMPDEST of the code.

It holds for every stack under the return address that leaves room for `room` more words.

It holds for every gas of at least `cost`.

From the block, with `args` on top of the return address, the frame reaches the return address.

There its stack holds `results` on top of the same stack, and it has paid `cost`.

The frame goes from `memory`, `state` and `substate` to `memory'`, `state'` and `substate'`. -/
def Subroutine (code : ByteArray) (message : Message fork) (entry : Nat)
    (args results : List U256) (room cost : Nat) (memory memory' : ByteArray)
    (state state' : State.TransactionState) (substate substate' : Substate) : Prop :=
  ∀ (ret : U256) (rest : List U256) (gas : Nat),
    isValidJumpDest (validJumpDestinations code) ret.toNat = true →
    args.length + 1 + rest.length + room ≤ STACK_LIMIT → cost ≤ gas →
    Hoare fork (At code message entry (args ++ ret :: rest) memory gas state substate)
      (At code message ret.toNat (results ++ rest) memory' (gas - cost) state' substate')

variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory memory' : ByteArray}
  {gas : Nat} {state state' : State.TransactionState} {substate substate' : Substate}

/-- A call of a subroutine: PUSHn of the address of its block, then JUMP to it.

The address of the block is a JUMPDEST of the code, and so is the return address.

The stack under the return address leaves room for the words that the block pushes.

The stack also has room for the address of the block, below the limit of 1024 words.

The call pays 3 for the push and 8 for the jump, then the gas of the block.

The frame reaches the return address with the results of the block on its stack. -/
theorem callSubroutine {n : Fin 33} {entry ret : U256} {args results rest : List U256}
    {room cost : Nat}
    (h : Subroutine code message entry.toNat args results room cost memory memory' state state'
      substate substate')
    (hn : n.val ≠ 0) (hlt : pc < code.size) (hbyte : code[pc] = 0x5f + UInt8.ofNat n.val)
    (decoded : Op.decode (0x5f + UInt8.ofNat n.val) = some (.push n))
    (hword : pushData code pc n = entry) (hjlt : pc + (1 + n) < code.size)
    (hjump : code[pc + (1 + n)] = 0x56)
    (ventry : isValidJumpDest (validJumpDestinations code) entry.toNat = true)
    (vret : isValidJumpDest (validJumpDestinations code) ret.toNat = true)
    (hroom : args.length + 1 + rest.length + room ≤ STACK_LIMIT)
    (hpush : args.length + 1 + rest.length < STACK_LIMIT) (hgas : 11 + cost ≤ gas) :
    Hoare fork (At code message pc (args ++ ret :: rest) memory gas state substate)
      (At code message ret.toNat (results ++ rest) memory' (gas - (11 + cost)) state'
        substate') := by
  have h1 := push (fork := fork) (code := code) (message := message) (pc := pc)
    (stack := args ++ ret :: rest) (memory := memory) (gas := gas) (state := state)
    (substate := substate) hn hlt hbyte decoded hword (by omega)
    (by simp only [List.length_append, List.length_cons]; omega)
  have h2 := jump (fork := fork) (code := code) (message := message) (pc := pc + (1 + n))
    (memory := memory) (gas := gas - 3) (state := state) (substate := substate)
    (destination := entry) (rest := args ++ ret :: rest) hjlt hjump (by omega) ventry
  have h3 := h ret rest (gas - 3 - 8) vret hroom (by omega)
  have hg : gas - 3 - 8 - cost = gas - (11 + cost) := by omega
  rw [hg] at h3
  exact (h1.seq h2).seq h3

/-! ## Subroutines over frames that know ranges of memory -/

/-- A specification of a subroutine over frames that know only the size of memory and some facts.

It holds for the same return addresses, stacks and gas as a subroutine over exact memory.

The frame goes from memory of size `size` that holds `facts` to size `size'` that holds `facts'`. -/
def KnownSubroutine (code : ByteArray) (message : Message fork) (entry : Nat)
    (args results : List U256) (room cost size size' : Nat) (facts facts' : List (Nat × ByteArray))
    (state state' : State.TransactionState) (substate substate' : Substate) : Prop :=
  ∀ (ret : U256) (rest : List U256) (gas : Nat),
    isValidJumpDest (validJumpDestinations code) ret.toNat = true →
    args.length + 1 + rest.length + room ≤ STACK_LIMIT → cost ≤ gas →
    Hoare fork (Known code message entry (args ++ ret :: rest) size facts gas state substate)
      (Known code message ret.toNat (results ++ rest) size' facts' (gas - cost) state' substate')

/-- A call of a subroutine over frames that know ranges of memory: PUSHn of its address, then JUMP.

It has the hypotheses of a call of a subroutine over exact memory.

The push and the jump keep the size of memory and every fact. -/
theorem callKnownSubroutine {n : Fin 33} {entry ret : U256} {args results rest : List U256}
    {room cost size size' : Nat} {facts facts' : List (Nat × ByteArray)}
    (h : KnownSubroutine code message entry.toNat args results room cost size size' facts facts'
      state state' substate substate')
    (hn : n.val ≠ 0) (hlt : pc < code.size) (hbyte : code[pc] = 0x5f + UInt8.ofNat n.val)
    (decoded : Op.decode (0x5f + UInt8.ofNat n.val) = some (.push n))
    (hword : pushData code pc n = entry) (hjlt : pc + (1 + n) < code.size)
    (hjump : code[pc + (1 + n)] = 0x56)
    (ventry : isValidJumpDest (validJumpDestinations code) entry.toNat = true)
    (vret : isValidJumpDest (validJumpDestinations code) ret.toNat = true)
    (hroom : args.length + 1 + rest.length + room ≤ STACK_LIMIT)
    (hpush : args.length + 1 + rest.length < STACK_LIMIT) (hgas : 11 + cost ≤ gas) :
    Hoare fork (Known code message pc (args ++ ret :: rest) size facts gas state substate)
      (Known code message ret.toNat (results ++ rest) size' facts' (gas - (11 + cost)) state'
        substate') := by
  have h1 := Known.of_at (size := size) (facts := facts) fun memory =>
    push (fork := fork) (code := code) (message := message) (pc := pc)
      (stack := args ++ ret :: rest) (memory := memory) (gas := gas) (state := state)
      (substate := substate) hn hlt hbyte decoded hword (by omega)
      (by simp only [List.length_append, List.length_cons]; omega)
  have h2 := Known.of_at (size := size) (facts := facts) fun memory =>
    jump (fork := fork) (code := code) (message := message) (pc := pc + (1 + n))
      (memory := memory) (gas := gas - 3) (state := state) (substate := substate)
      (destination := entry) (rest := args ++ ret :: rest) hjlt hjump (by omega) ventry
  have h3 := h ret rest (gas - 3 - 8) vret hroom (by omega)
  have hg : gas - 3 - 8 - cost = gas - (11 + cost) := by omega
  rw [hg] at h3
  exact (h1.seq h2).seq h3

end EthLib.Execution.Evm.Logic

module

public import EthLib.Execution.Proofs.Evm.Logic.Stack
public import EthLib.Execution.Proofs.Evm.Logic.NatCode

/-!
# Proofs: a tactic that steps through the opcodes of a code

A proof about a code applies one rule per opcode.

Each rule needs facts about the code.

These are that the program counter lies inside the code, the byte there, and the data of a PUSH.

The tactic here applies the rule of the opcode at the program counter, and proves those facts.

It takes a list of rewrite rules that turn the code into numbers.

For a code stored as one number, they are the equation of the code and the definition of its number.

The tactic rewrites each fact with that list, and evaluates it on the numbers.

It steps over PUSH0 to PUSH32, POP, DUP1 to DUP16 and SWAP1 to SWAP16.

It steps over each opcode of one, two or three operands that the fork runs on the stack alone.

It steps over JUMPDEST, CALLDATALOAD and JUMP.

It steps over JUMPI on a condition that is a number, or that a hypothesis proves zero or nonzero.

It steps over each opcode that pushes a word fixed by the frame, such as CALLVALUE, and over GAS.

It proves a jump destination valid by the walk along the opcodes.

So it steps over a jump only in a code stored as one number.

It fails on any other opcode, and on a step whose gas, fork or room on the stack it cannot prove.

It proves gas by linear arithmetic on the gas of the frame and the hypotheses.

It proves that the fork has an opcode when every fork has it.

It also does so when a hypothesis names a fork that has the opcode.

A second tactic closes a run at STOP, or at the end of the code.

A last rule replaces the stack, the memory and the gas of a frame by equal ones.

It ends a run whose last frame names its fields in another form.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- A frame reaches itself, named with an equal stack, an equal memory and an equal gas. -/
theorem reshape {code : ByteArray} {message : Message fork} {pc : Nat} {s s' : List U256}
    {m m' : ByteArray} {g g' : Nat} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray} (hs : s = s') (hm : m = m') (hg : g = g') :
    Hoare fork (At code message pc s m g st ss rd) (At code message pc s' m' g' st ss rd) := by
  subst hs hm hg
  exact Triple.of_imp fun _ h => h

/-- A specification also holds from a frame with an equal stack, memory and gas. -/
theorem Spec.reshape {code : ByteArray} {message : Message fork} {pc : Nat} {s s' : List U256}
    {m m' : ByteArray} {g g' : Nat} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray} {Q : Evm fork Nat → Prop} (hs : s = s') (hm : m = m') (hg : g = g')
    (h : Spec fork (At code message pc s' m' g' st ss rd) Q) :
    Spec fork (At code message pc s m g st ss rd) Q :=
  Spec.seq (Logic.reshape hs hm hg) h

open Lean.Parser.Tactic

/-- Proves a fact about the code from the rewrite rules `ls`, by evaluation on numbers.

The fact is that a position lies inside the code, the byte at a position, or the data of a PUSH.

A byte or a word left unknown in the goal is set to the value it evaluates to. -/
syntax "evm_code" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_code [$ls,*]) => `(tactic| (simp only [$ls,*, NatCode.size_ofNat,
      NatCode.getElem_ofNat, NatCode.pushData_ofNat, NatCode.natByte, Nat.reduceLT,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceMod,
      Nat.reduceShiftRight, UInt8.reduceOfNat, UInt8.reduceToNat, BitVec.reduceOfNat,
      ↓reduceIte]) <;> rfl)

/-- Proves that a jump destination is valid, by the walk along the opcodes from position 0. -/
syntax "evm_dest" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_dest [$ls,*]) => `(tactic|
      (simp only [$ls,*, BitVec.reduceToNat]
       refine NatCode.valid_of_walk ?walk ?byte
       case walk => decide +kernel
       case byte => decide))

/-- Proves that the fork has an opcode: every fork has it, or a hypothesis gives a later fork. -/
syntax "evm_fork" : tactic

macro_rules
  | `(tactic| evm_fork) => `(tactic| first
      | exact Fork.frontier_le _
      | (refine' Nat.le_trans ?_ ?h
         case h => assumption
         decide))

/-- The prices of the opcodes of the stack alone, and of those that push a word of the frame. -/
syntax "evm_prices" : tactic

macro_rules
  | `(tactic| evm_prices) => `(tactic| simp only [OPCODE_ADD, OPCODE_SUB, OPCODE_MUL,
      OPCODE_DIV, OPCODE_SDIV, OPCODE_MOD, OPCODE_SMOD, OPCODE_ADDMOD, OPCODE_MULMOD,
      OPCODE_SIGNEXTEND, OPCODE_LT, OPCODE_GT, OPCODE_SLT, OPCODE_SGT, OPCODE_EQ, OPCODE_ISZERO,
      OPCODE_AND, OPCODE_OR, OPCODE_XOR, OPCODE_NOT, OPCODE_BYTE, OPCODE_SHL, OPCODE_SHR,
      OPCODE_SAR, OPCODE_CLZ, OPCODE_ADDRESS, OPCODE_ORIGIN, OPCODE_CALLER, OPCODE_CALLVALUE,
      OPCODE_CALLDATASIZE, OPCODE_CODESIZE, OPCODE_PC, OPCODE_MSIZE, OPCODE_TIMESTAMP,
      OPCODE_NUMBER, BASE, VERY_LOW, LOW, MID])

/-- Proves that the frame holds enough gas for a step, by linear arithmetic.

A goal `a ≤ g - b` is first turned into `a + b ≤ g`.

On the first form with several atoms, linear arithmetic can exceed the recursion limit. -/
syntax "evm_gas" : tactic

macro_rules
  | `(tactic| evm_gas) => `(tactic| first
      | (apply Nat.le_sub_of_add_le; first | omega | (evm_prices; omega))
      | omega
      | (evm_prices; omega))

/-- Proves that the stack has room for one more word. -/
syntax "evm_room" : tactic

macro_rules
  | `(tactic| evm_room) => `(tactic|
      (simp only [List.length_cons, List.length_nil, STACK_LIMIT] <;> omega))

/-- Evaluates the program counter, the pushed word and the gas of the frame after a step. -/
syntax "evm_tidy" : tactic

macro_rules
  | `(tactic| evm_tidy) => `(tactic| ((try evm_prices) <;> (try simp only [UInt8.reduceToNat,
      BitVec.reduceToNat, Nat.reduceAdd, Nat.reduceSub, Nat.sub_sub, List.set_cons_zero,
      List.set_cons_succ])))

/-- Runs the opcode at the program counter of the first frame of the goal, by its rule.

The goal is a triple from a frame of a code at a known program counter.

The rewrite rules `ls` turn the facts about the code into facts about numbers.

The goal that is left starts from the frame after the step. -/
syntax "evm_step" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_step [$ls,*]) => `(tactic| ((try unfold Spec) <;> (first
      | (refine' Triple.seq (push_of_decode ?lt ?op ?dec ?n ?word ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => rfl
         case n => decide
         case word => evm_code [$ls,*]
         case gas => evm_gas
         case room => evm_room)
      | (refine' Triple.seq (push0 ?fork ?lt ?op ?gas ?room) ?next
         case fork => evm_fork
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case room => evm_room)
      | (refine' Triple.seq (binary ?lt ?op ?dec ?run ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => exact instruction_of_stackOnlyStep rfl
         case gas => evm_gas)
      | (refine' Triple.seq (dup_of_decode ?lt ?op ?dec ?x ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => rfl
         case x => rfl
         case gas => evm_gas
         case room => evm_room)
      | (refine' Triple.seq (swap_of_decode ?lt ?op ?dec ?x ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => rfl
         case x => rfl
         case gas => evm_gas)
      | (refine' Triple.seq (pop ?lt ?op ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas)
      | (refine' Triple.seq (unary ?lt ?op ?dec ?run ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => exact instruction_of_stackOnlyStep rfl
         case gas => evm_gas)
      | (refine' Triple.seq (ternary ?lt ?op ?dec ?run ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => exact instruction_of_stackOnlyStep rfl
         case gas => evm_gas)
      | (refine' Triple.seq (jumpdest ?lt ?op ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas)
      | (refine' Triple.seq (calldataload ?lt ?op ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas)
      | (refine' Triple.seq (jump ?lt ?op ?gas ?dest) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case dest => evm_dest [$ls,*])
      | (refine' Triple.seq (jumpi_taken ?lt ?op ?gas ?nz ?dest) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case nz => first | assumption | decide
         case dest => evm_dest [$ls,*])
      | (refine' Triple.seq (jumpi_of_eq_zero ?lt ?op ?gas ?zero) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case zero => first | assumption | decide)
      | (refine' Triple.seq (push_of_readFrame ?lt ?op ?dec ?run ?word ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => rfl
         case word => intro _ hc hm hp hmem; (try simp only [hc, hm, hp, hmem]); rfl
         case gas => evm_gas
         case room => evm_room)
      | (refine' Triple.seq (gas_rule ?lt ?op ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case room => evm_room)
      | fail "no rule of a step applies to the opcode at the program counter") <;> evm_tidy))

/-- Closes a specification at STOP, or at a program counter at or past the end of the code.

The rewrite rules `ls` turn the facts about the code into facts about numbers. -/
syntax "evm_stop" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_stop [$ls,*]) => `(tactic| first
      | (refine' stop ?lt ?op
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*])
      | (refine' stop_of_size_le ?le
         case le => simp only [$ls,*, NatCode.size_ofNat]; decide)
      | fail "the opcode at the program counter is not STOP, and the code does not end there")

end EthLib.Execution.Evm.Logic

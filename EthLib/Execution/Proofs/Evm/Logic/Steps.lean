module

public import EthLib.Execution.Proofs.Evm.Logic.Stack
public import EthLib.Execution.Proofs.Evm.Logic.NatCode
public import EthLib.Execution.Proofs.Evm.Logic.Environment
public import EthLib.Execution.Proofs.Evm.Logic.Known
public meta import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Delta

/-!
# Proofs: a tactic that steps through the opcodes of a code

A proof about a code applies one rule per opcode.

Each rule needs facts about the code.

These are that the program counter lies inside the code, the byte there, and the data of a PUSH.

The tactic here applies the rule of the opcode at the program counter, and proves those facts.

A second tactic does the same over frames that know a few ranges of memory.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- A frame reaches itself, named with an equal stack, an equal memory and an equal gas.

It ends a run whose last frame names its fields in another form. -/
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

/-! ## Operations on words of numbers -/

open Lean Meta Simp in
/-- Unfolds an operation on words once each operand is a number, so that simp evaluates it.

An operation with an operand that is not a number stays as it is. -/
meta def unfoldOfNumbers (e : Expr) : SimpM DStep := do
  for arg in e.getAppArgs do
    if (← getBitVecValue? arg).isNone then return .continue
  match ← delta? e with
  | some unfolded => return .visit unfolded
  | none => return .continue

/-- ADD of two numbers. -/
dsimproc_decl evalAdd (add _ _) := unfoldOfNumbers
/-- SUB of two numbers. -/
dsimproc_decl evalSub (sub _ _) := unfoldOfNumbers
/-- MUL of two numbers. -/
dsimproc_decl evalMul (mul _ _) := unfoldOfNumbers
/-- DIV of two numbers. -/
dsimproc_decl evalDiv (div _ _) := unfoldOfNumbers
/-- MOD of two numbers. -/
dsimproc_decl evalMod (mod _ _) := unfoldOfNumbers
/-- LT of two numbers. -/
dsimproc_decl evalLessThan (lessThan _ _) := unfoldOfNumbers
/-- GT of two numbers. -/
dsimproc_decl evalGreaterThan (greaterThan _ _) := unfoldOfNumbers
/-- EQ of two numbers. -/
dsimproc_decl evalEqual (equal _ _) := unfoldOfNumbers
/-- ISZERO of a number. -/
dsimproc_decl evalIsZero (isZero _) := unfoldOfNumbers
/-- AND of two numbers. -/
dsimproc_decl evalAnd (bitwiseAnd _ _) := unfoldOfNumbers
/-- OR of two numbers. -/
dsimproc_decl evalOr (bitwiseOr _ _) := unfoldOfNumbers
/-- XOR of two numbers. -/
dsimproc_decl evalXor (bitwiseXor _ _) := unfoldOfNumbers
/-- NOT of a number. -/
dsimproc_decl evalNot (bitwiseNot _) := unfoldOfNumbers
/-- SHL of two numbers. -/
dsimproc_decl evalShl (bitwiseShl _ _) := unfoldOfNumbers
/-- SHR of two numbers. -/
dsimproc_decl evalShr (bitwiseShr _ _) := unfoldOfNumbers

open Lean.Parser.Tactic

/-- Proves a fact about the code from the rewrite rules `ls`, by evaluation on numbers.

The fact is that a position lies inside the code, the byte at a position, or the data of a PUSH.

For a code stored as one number, the rules are its equation and the definition of its number.

A byte or a word left unknown in the goal is set to the value it evaluates to. -/
syntax "evm_code" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_code [$ls,*]) => `(tactic| (simp only [$ls,*, NatCode.size_ofNat,
      NatCode.getElem_ofNat, NatCode.pushData_ofNat, NatCode.natByte, Nat.reduceLT,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceMod,
      Nat.reduceShiftRight, UInt8.reduceOfNat, UInt8.reduceToNat, BitVec.reduceOfNat,
      ↓reduceIte]) <;> rfl)

/-- Proves that a jump destination is valid, by the walk along the opcodes from position 0.

So a step over a jump needs a code stored as one number. -/
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

It works on the gas of the frame and the hypotheses.

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

/-- Evaluates the arithmetic, comparison, bitwise and shift operations on words of numbers.

SDIV, SMOD, ADDMOD, MULMOD, EXP, SIGNEXTEND, BYTE, SAR, SLT and SGT are left as they are. -/
syntax "evm_words" : tactic

macro_rules
  | `(tactic| evm_words) => `(tactic| simp only [evalAdd, evalSub,
      evalMul, evalDiv, evalMod, evalLessThan, evalGreaterThan, evalEqual, evalIsZero, evalAnd,
      evalOr, evalXor, evalNot, evalShl, evalShr, BitVec.reduceAdd, BitVec.reduceSub,
      BitVec.reduceMul, BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceXOr, BitVec.reduceNot,
      BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight, BitVec.reduceToNat, BitVec.reduceEq,
      BitVec.reduceOfNat, Nat.reduceLT, Nat.reduceGT, Nat.reduceDiv, Nat.reduceMod, ↓reduceIte])

/-- A frame at an offset plus two numbers is the frame at the offset plus their sum.

So the program counter of a block at an offset `o` stays `o + k` from step to step. -/
theorem At.pc_add_add {code : ByteArray} {message : Message fork} {o a b : Nat}
    {stack : List U256} {memory : ByteArray} {gas : Nat} {state : State.TransactionState}
    {substate : Substate} {returnData : ByteArray} :
    At code message (o + a + b) stack memory gas state substate returnData =
      At code message (o + (a + b)) stack memory gas state substate returnData := by
  rw [Nat.add_assoc]

/-- Evaluates the program counter, the pushed word and the gas of the frame after a step.

It also evaluates each closed operation on words and each closed comparison.

It also reduces each `if` on numbers.

A program counter at an offset `o` comes back as `o + k`, with `k` a number. -/
syntax "evm_tidy" : tactic

macro_rules
  | `(tactic| evm_tidy) => `(tactic| ((try evm_prices) <;> (try simp only [UInt8.reduceToNat,
      BitVec.reduceToNat, Nat.reduceAdd, Nat.reduceSub, Nat.sub_sub, List.set_cons_zero,
      List.set_cons_succ, At.pc_add_add]) <;> (try evm_words)))

/-- Runs the opcode at the program counter of the first frame of the goal, by its rule.

The goal is a triple from a frame of a code at a known program counter.

The rewrite rules `ls` turn the facts about the code into facts about numbers.

The goal that is left starts from the frame after the step. -/
syntax "evm_step" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_step [$ls,*]) => `(tactic| ((try unfold Spec) <;> (first
      -- PUSH1 to PUSH32.
      | (refine' Triple.seq (push_of_decode ?lt ?op ?dec ?n ?word ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => rfl
         case n => decide
         case word => evm_code [$ls,*]
         case gas => evm_gas
         case room => evm_room)
      -- PUSH0.
      | (refine' Triple.seq (push0 ?fork ?lt ?op ?gas ?room) ?next
         case fork => evm_fork
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case room => evm_room)
      -- Each opcode of two operands that the fork runs on the stack alone.
      | (refine' Triple.seq (binary ?lt ?op ?dec ?run ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => exact instruction_of_stackOnlyStep rfl
         case gas => evm_gas)
      -- DUP1 to DUP16.
      | (refine' Triple.seq (dup_of_decode ?lt ?op ?dec ?x ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => rfl
         case x => rfl
         case gas => evm_gas
         case room => evm_room)
      -- SWAP1 to SWAP16.
      | (refine' Triple.seq (swap_of_decode ?lt ?op ?dec ?x ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => rfl
         case x => rfl
         case gas => evm_gas)
      -- POP.
      | (refine' Triple.seq (pop ?lt ?op ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas)
      -- Each opcode of one operand that the fork runs on the stack alone.
      | (refine' Triple.seq (unary ?lt ?op ?dec ?run ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => exact instruction_of_stackOnlyStep rfl
         case gas => evm_gas)
      -- Each opcode of three operands that the fork runs on the stack alone.
      | (refine' Triple.seq (ternary ?lt ?op ?dec ?run ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => exact instruction_of_stackOnlyStep rfl
         case gas => evm_gas)
      -- JUMPDEST, CALLDATALOAD and JUMP.
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
      -- JUMPI on a condition that is a number, or that a hypothesis proves zero or nonzero.
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
      -- Each opcode that pushes a word fixed by the frame, such as CALLVALUE.
      | (refine' Triple.seq (push_of_readFrame ?lt ?op ?dec ?run ?word ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => rfl
         case word => intro _ hc hm hp hmem; (try simp only [hc, hm, hp, hmem]); rfl
         case gas => evm_gas
         case room => evm_room)
      -- Each opcode that pushes an environment number, such as NUMBER.
      | (refine' Triple.seq (push_of_readNumber ?lt ?op ?dec ?run ?word ?fit ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => rfl
         case word => intro _ hc hm hp hmem; (try simp only [hc, hm, hp, hmem]); rfl
         -- A hypothesis or linear arithmetic must show that the number is below `2^256`.
         case fit => first | assumption | omega
         case gas => evm_gas
         case room => evm_room)
      -- GAS.
      | (refine' Triple.seq (gas_rule ?lt ?op ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case room => evm_room)
      -- CHAINID.
      | (refine' Triple.seq (chainid_rule ?fork ?lt ?op ?gas ?room) ?next
         case fork => evm_fork
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case room => evm_room)
      -- The tactic fails on any other opcode.
      --
      -- It also fails on a step whose gas, fork or room on the stack it cannot prove.
      | fail "no rule of a step applies to the opcode at the program counter") <;> evm_tidy))

/-- Runs the opcode at the program counter of the first frame of the goal, by its rule.

The goal is a triple over the steps from frames that are monotone in gas.

It starts from a frame of a code at a known program counter.

The rewrite rules `ls` turn the facts about the code into facts about numbers.

It steps over the same opcodes as the tactic above, except GAS, which is not monotone in gas.

The goal that is left starts from the frame after the step. -/
syntax "evm_stepG" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_stepG [$ls,*]) => `(tactic| ((try unfold SpecG) <;> (first
      | (refine' Triple.seq (push_of_decodeG ?lt ?op ?dec ?n ?word ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => rfl
         case n => decide
         case word => evm_code [$ls,*]
         case gas => evm_gas
         case room => evm_room)
      | (refine' Triple.seq (push0G ?fork ?lt ?op ?gas ?room) ?next
         case fork => evm_fork
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case room => evm_room)
      | (refine' Triple.seq (binaryG ?lt ?op ?dec ?run ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => exact instruction_of_stackOnlyStep rfl
         case gas => evm_gas)
      | (refine' Triple.seq (dup_of_decodeG ?lt ?op ?dec ?x ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => rfl
         case x => rfl
         case gas => evm_gas
         case room => evm_room)
      | (refine' Triple.seq (swap_of_decodeG ?lt ?op ?dec ?x ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => rfl
         case x => rfl
         case gas => evm_gas)
      | (refine' Triple.seq (popG ?lt ?op ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas)
      | (refine' Triple.seq (unaryG ?lt ?op ?dec ?run ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => exact instruction_of_stackOnlyStep rfl
         case gas => evm_gas)
      | (refine' Triple.seq (ternaryG ?lt ?op ?dec ?run ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => exact instruction_of_stackOnlyStep rfl
         case gas => evm_gas)
      | (refine' Triple.seq (jumpdestG ?lt ?op ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas)
      | (refine' Triple.seq (calldataloadG ?lt ?op ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas)
      | (refine' Triple.seq (jumpG ?lt ?op ?gas ?dest) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case dest => evm_dest [$ls,*])
      | (refine' Triple.seq (jumpi_takenG ?lt ?op ?gas ?nz ?dest) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case nz => first | assumption | decide
         case dest => evm_dest [$ls,*])
      | (refine' Triple.seq (jumpi_of_eq_zeroG ?lt ?op ?gas ?zero) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case zero => first | assumption | decide)
      | (refine' Triple.seq (push_of_readFrameG ?lt ?op ?dec ?run ?word ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => rfl
         case word => intro _ hc hm hp hmem; (try simp only [hc, hm, hp, hmem]); rfl
         case gas => evm_gas
         case room => evm_room)
      | (refine' Triple.seq (push_of_readNumberG ?lt ?op ?dec ?run ?word ?fit ?gas ?room) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case dec => refine ofByte_of_decode rfl ?_; evm_fork
         case run => rfl
         case word => intro _ hc hm hp hmem; (try simp only [hc, hm, hp, hmem]); rfl
         case fit => first | assumption | omega
         case gas => evm_gas
         case room => evm_room)
      | (refine' Triple.seq (chainid_ruleG ?fork ?lt ?op ?gas ?room) ?next
         case fork => evm_fork
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

/-! ## Steps over frames that know a few ranges of memory -/

/-- Evaluates the growth of memory, and its price, for ranges and a size that are numbers. -/
syntax "evm_mem" : tactic

macro_rules
  | `(tactic| evm_mem) => `(tactic| simp (config := { decide := true }) only [extendMemory,
      ceil32, wordCount, memoryGasCost, keccak256Cost, WORD_BYTES, MEMORY_PER_WORD,
      OPCODE_KECCAK256_BASE, OPCODE_KECCAK256_PER_WORD, BitVec.reduceToNat, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reducePow, ↓reduceIte,
      Nat.add_zero, Nat.zero_add, ByteArray.size_empty])

/-- Proves the gas of a step that may grow memory, by linear arithmetic once its price is known. -/
syntax "evm_memGas" : tactic

macro_rules
  | `(tactic| evm_memGas) => `(tactic| first | evm_gas | (evm_mem <;> evm_gas))

/-- Proves that a fact is in the list of a frame, by the first entry that matches it. -/
syntax "evm_fact" : tactic

macro_rules
  | `(tactic| evm_fact) => `(tactic| ((try simp only [BitVec.reduceToNat]) <;>
      (repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)))

/-- Proves a size or a bound of a range of bytes, from the sizes of its parts. -/
syntax "evm_size" : tactic

macro_rules
  | `(tactic| evm_size) => `(tactic| ((try simp only [size_wordBytes, ByteArray.size_append,
      size_bufferRead, BitVec.reduceToNat, Nat.reduceAdd]) <;> first | rfl | decide | omega))

/-- Evaluates the size of memory, the facts that a write keeps, and the gas after a step. -/
syntax "evm_tidyK" : tactic

macro_rules
  | `(tactic| evm_tidyK) => `(tactic| ((try evm_mem) <;> (try simp (config := { decide := true })
      only [keep, outside, List.flatMap_cons, List.flatMap_nil, List.nil_append,
        List.cons_append, List.append_nil, Apart, size_wordBytes, ByteArray.size_append,
        size_bufferRead, size_memoryReadBytes, memoryReadBytes_of_size, loadWord_wordBytes,
        wordBytes_loadWord, BitVec.reduceToNat, Nat.reduceAdd, Nat.reduceSub, ↓reduceIte]) <;>
      evm_tidy))

/-- Proves that a read along the facts of a frame gives some bytes, by evaluation.

The bytes are the parts of the facts that cover the range, joined in order. -/
syntax "evm_read" : tactic

macro_rules
  -- Each unfolding reads one piece, which is evaluated before the next unfolding.
  | `(tactic| evm_read) => `(tactic| ((repeat (rw [readFacts]; simp (config := { decide := true })
      only [List.find?_cons_of_pos, List.find?_cons_of_neg, List.find?_nil, Bool.and_eq_true,
        decide_eq_true_eq, Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not,
        Nat.not_le, Nat.not_lt, size_wordBytes, ByteArray.size_append, size_bufferRead,
        size_memoryReadBytes, memoryReadBytes_of_size, Nat.min_def, BitVec.reduceToNat,
        Nat.reduceAdd, Nat.reduceSub, ↓reduceIte, Option.map_some, Option.map_none])) <;>
      try rfl))

/-- Runs the opcode at the program counter of the first frame of the goal, by its rule.

The goal is a triple from a frame that knows a few ranges of memory, at a known program counter.

The rewrite rules `ls` turn the facts about the code into facts about numbers. -/
syntax "evm_stepK" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_stepK [$ls,*]) => `(tactic| ((try unfold Spec) <;> (first
      -- MSTORE, MLOAD, KECCAK256, CALLDATACOPY and MCOPY take their rules on such frames.
      --
      -- MLOAD, KECCAK256 and MCOPY read the first fact in the list that starts where they read.
      --
      -- Otherwise MLOAD and KECCAK256 read along the facts that cover the range.
      | (refine' Triple.seq (mstore_known ?lt ?op ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_memGas)
      | (refine' Triple.seq (mload_known ?lt ?op ?fact ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case fact => evm_fact
         case gas => evm_gas)
      -- MLOAD of a part of a fact, or of a range along adjacent facts.
      | (refine' Triple.seq (mload_known_read ?lt ?op ?read ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case read => evm_read
         case gas => evm_gas)
      | (refine' Triple.seq (keccak256_known ?lt ?op ?fact ?len ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case fact => evm_fact
         case len => evm_size
         case gas => evm_memGas)
      -- KECCAK256 of a part of a fact, or of a range along adjacent facts.
      | (refine' Triple.seq (keccak256_known_read ?lt ?op ?read ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case read => evm_read
         case gas => evm_memGas)
      | (refine' Triple.seq (calldatacopy_known ?lt ?op ?nz ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case nz => decide
         case gas => evm_memGas)
      -- MCOPY of the whole range of a fact, tried first.
      --
      -- The destination keeps only the parts of the facts outside it.
      | (refine' Triple.seq (mcopy_known ?fork ?lt ?op ?nz ?fact ?len ?gas) ?next
         case fork => evm_fork
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case nz => decide
         case fact => evm_fact
         case len => evm_size
         case gas => evm_memGas)
      -- MCOPY within the range of a fact.
      | (refine' Triple.seq (mcopy_known_within ?fork ?lt ?op ?fact ?s ?s' ?d ?d' ?gas) ?next
         case fork => evm_fork
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case fact => evm_fact
         case s => evm_size
         case s' => evm_size
         case d => evm_size
         case d' => evm_size
         case gas => evm_memGas)
      -- Every other opcode whose rule keeps memory, and does not read it, takes that rule.
      --
      -- It takes it for every memory.
      | (refine' Triple.seq (Known.of_at fun _ => ?step) ?next
         case step => (evm_step [$ls,*]) <;> exact Triple.of_imp fun _ h => h)
      | fail "no rule of a step applies to the opcode at the program counter")
      -- The goal that is left starts from the frame after the step.
      <;> evm_tidyK))

end EthLib.Execution.Evm.Logic

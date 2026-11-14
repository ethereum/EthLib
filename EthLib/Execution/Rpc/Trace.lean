module

public import EthLib.Execution.Blocks.Transition

/-!
# `Execution.Rpc.Trace`

The opcode trace of a transaction, as the opcode logger of the debug methods returns it.

It holds one entry for each step of a frame with code, up to a bound.

A step past the end of the code runs STOP, and it has an entry too.

A frame with no code has none, so a plain transfer gives no entry.

The trace is an observer of the one interpreter, so it changes nothing in the run.

[`opcode-tracer.yaml`][schema] defines the entries, the configuration and the trace.

Where it leaves a choice open, the docs of each field say what this specification picks.

[schema]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/opcode-tracer.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)
open EthLib.Execution.Transactions

/-- The mnemonic of an opcode at `fork`.

PREVRANDAO is DIFFICULTY before Paris, by EIP-4399. -/
def opMnemonic (fork : Fork) : Op → String
  | .stop => "STOP"
  | .add => "ADD"
  | .mul => "MUL"
  | .sub => "SUB"
  | .div => "DIV"
  | .sdiv => "SDIV"
  | .mod => "MOD"
  | .smod => "SMOD"
  | .addmod => "ADDMOD"
  | .mulmod => "MULMOD"
  | .exp => "EXP"
  | .signextend => "SIGNEXTEND"
  | .lt => "LT"
  | .gt => "GT"
  | .slt => "SLT"
  | .sgt => "SGT"
  | .eq => "EQ"
  | .iszero => "ISZERO"
  | .and => "AND"
  | .or => "OR"
  | .xor => "XOR"
  | .not => "NOT"
  | .byte => "BYTE"
  | .shl => "SHL"
  | .shr => "SHR"
  | .sar => "SAR"
  | .clz => "CLZ"
  | .keccak256 => "KECCAK256"
  | .address => "ADDRESS"
  | .balance => "BALANCE"
  | .origin => "ORIGIN"
  | .caller => "CALLER"
  | .callvalue => "CALLVALUE"
  | .calldataload => "CALLDATALOAD"
  | .calldatasize => "CALLDATASIZE"
  | .calldatacopy => "CALLDATACOPY"
  | .codesize => "CODESIZE"
  | .codecopy => "CODECOPY"
  | .gasprice => "GASPRICE"
  | .extcodesize => "EXTCODESIZE"
  | .extcodecopy => "EXTCODECOPY"
  | .returndatasize => "RETURNDATASIZE"
  | .returndatacopy => "RETURNDATACOPY"
  | .extcodehash => "EXTCODEHASH"
  | .blockhash => "BLOCKHASH"
  | .coinbase => "COINBASE"
  | .timestamp => "TIMESTAMP"
  | .number => "NUMBER"
  | .prevrandao => if fork < .paris then "DIFFICULTY" else "PREVRANDAO"
  | .gaslimit => "GASLIMIT"
  | .chainid => "CHAINID"
  | .selfbalance => "SELFBALANCE"
  | .basefee => "BASEFEE"
  | .blobhash => "BLOBHASH"
  | .blobbasefee => "BLOBBASEFEE"
  | .slotnum => "SLOTNUM"
  | .pop => "POP"
  | .mload => "MLOAD"
  | .mstore => "MSTORE"
  | .mstore8 => "MSTORE8"
  | .sload => "SLOAD"
  | .sstore => "SSTORE"
  | .jump => "JUMP"
  | .jumpi => "JUMPI"
  | .pc => "PC"
  | .msize => "MSIZE"
  | .gas => "GAS"
  | .jumpdest => "JUMPDEST"
  | .tload => "TLOAD"
  | .tstore => "TSTORE"
  | .mcopy => "MCOPY"
  | .push n => s!"PUSH{n.val}"
  | .dup n => s!"DUP{n.val + 1}"
  | .swap n => s!"SWAP{n.val + 1}"
  | .log n => s!"LOG{n.val}"
  | .dupn => "DUPN"
  | .swapn => "SWAPN"
  | .exchange => "EXCHANGE"
  | .create => "CREATE"
  | .call => "CALL"
  | .callcode => "CALLCODE"
  | .«return» => "RETURN"
  | .delegatecall => "DELEGATECALL"
  | .create2 => "CREATE2"
  | .staticcall => "STATICCALL"
  | .revert => "REVERT"
  | .selfdestruct => "SELFDESTRUCT"

/-- The mnemonic of an opcode at `fork`, or INVALID for a byte that is no opcode.

The name INVALID is the one that EIP-141 gives to `0xfe`; the source names no other byte. -/
def mnemonicOf (fork : Fork) : Option Op → String
  | some op => opMnemonic fork op
  | none => "INVALID"

/-- What the opcode logger records of one step of a frame. -/
structure StructLog where
  /-- The position of the opcode in the code. -/
  pc : Nat
  /-- The mnemonic of the opcode. -/
  op : String
  /-- The gas left before the step.

  From Glamsterdam, it is the execution gas, without the reservoir of state gas. -/
  gas : Nat
  /-- The gas that the step removes from the frame.

  A step that starts a message counts the gas that it passes to it.

  A call that starts no message gets that gas back in the same step, so it counts only its price.

  The source asks for the price that the step would charge if it succeeded.

  A step that fails does not give that price.

  So it counts all the gas left, which its halt burns. -/
  gasCost : Nat
  /-- The depth of the frame, 1 for the frame of the transaction. -/
  depth : Nat
  /-- The error of a step that fails, or none. -/
  error : Option EvmError
  /-- The refund counter before the step: that of the frame and of the frames that called it.

  The source asks for the counter of the transaction.

  This one leaves out the refund of EIP-7702 authorizations, which the steps do not show.

  A total below zero counts as zero. -/
  refund : Nat
  /-- The stack before the step, bottom first, or none when the stack is not recorded. -/
  stack : Option (List U256)
  /-- The memory before the step, or none when the memory is not recorded. -/
  memory : Option ByteArray
  /-- The return data before the step, or none when it is not recorded. -/
  returnData : Option ByteArray
  /-- At SLOAD and SSTORE, each slot of the current account that the trace has seen so far.

  Each slot holds its value after the last step that read or wrote it.

  A step that fails adds no slot.

  It is none at another opcode, or when the storage is not recorded. -/
  storage : Option (List (Bytes32 × U256))

/-- What the opcode logger records, and how many entries at most. -/
structure TraceConfig where
  /-- Leave out the stack of each entry. -/
  disableStack : Bool := false
  /-- Record the memory of each entry. -/
  enableMemory : Bool := false
  /-- Record the return data of each entry. -/
  enableReturnData : Bool := false
  /-- Leave out the storage of each entry. -/
  disableStorage : Bool := false
  /-- The most entries to record, or 0 for no bound.

  Past the bound, the run goes on and records nothing more. -/
  limit : Nat := 0

/-- The state of the opcode logger during a run. -/
structure Tracer where
  /-- The entries so far, oldest first. -/
  logs : Array StructLog := #[]
  /-- For each account, the slots that the trace has seen, with their last values. -/
  slots : List (Address × List (Bytes32 × U256)) := []
  /-- The refund counters of the frames that called the current one, outermost first. -/
  refunds : List Int := []

/-- The slots after one more slot is seen with its value, which replaces any earlier value. -/
def setSlot (slots : List (Bytes32 × U256)) (key : Bytes32) (value : U256) :
    List (Bytes32 × U256) :=
  if slots.any (·.1 == key) then slots.map fun (k, v) => (k, if k == key then value else v)
  else slots ++ [(key, value)]

/-- The gas that a step removes from the frame `evm`, or all its gas when the step fails. -/
def stepCost {fork : Fork} {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter) :
    Except EvmError (StepResult fork Meter) → Nat
  | .ok (.next after) => GasMeter.gasLeft evm.gas - GasMeter.gasLeft after.gas
  | .ok (.child caller _ _) => GasMeter.gasLeft evm.gas - GasMeter.gasLeft caller.gas
  | .error _ => GasMeter.gasLeft evm.gas

/-- The slot that an SLOAD or SSTORE step reads or writes, with its value after the step.

It is none for another opcode, or for a step that fails. -/
def touchedSlot {fork : Fork} {Meter : Type} [GasMeter Meter] (op : Option Op)
    (evm : Evm fork Meter) : Except EvmError (StepResult fork Meter) → Option (Bytes32 × U256)
  | .ok (.next after) =>
    if (op = some .sload ∨ op = some .sstore) ∧ after.error.isNone then
      evm.stack.val.head?.map fun word =>
        let key := word.toBeBytes
        (key, after.state.getStorage evm.message.currentTarget key)
    else none
  | _ => none

/-- The error of a step that fails, or none.

A step can fail by giving a frame that it halted, which holds the error.

A revert is no error of the step. -/
def stepError {fork : Fork} {Meter : Type} :
    Except EvmError (StepResult fork Meter) → Option EvmError
  | .error e => some e
  | .ok (.next after) => after.error.filter (· != .revert)
  | .ok (.child _ _ _) => none

/-- The opcode of the step of the frame `evm` at `fork`: STOP past the end of the code. -/
def stepOp {fork : Fork} {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter) : Option Op :=
  if h : evm.pc < evm.code.size then Op.ofByte fork evm.code[evm.pc] else some .stop

/-- The logger after it sees the step `result` of the frame `evm`, at `fork`.

A frame with no code adds no entry, so a plain transfer has none.

A frame with code adds one for each step, the STOP past the end of its code included.

A step past the bound adds no entry. -/
def Tracer.record (config : TraceConfig) {fork : Fork} {Meter : Type} [GasMeter Meter]
    (evm : Evm fork Meter) (result : Except EvmError (StepResult fork Meter))
    (tracer : Tracer) : Tracer :=
  if evm.code.size = 0 ∨ (config.limit ≠ 0 ∧ config.limit ≤ tracer.logs.size) then tracer
  else
    let op := stepOp evm
    let account := evm.message.currentTarget
    let storageOp := op = some .sload ∨ op = some .sstore
    let seen := (tracer.slots.lookup account).getD []
    let seen := match touchedSlot op evm result with
      | some (key, value) => setSlot seen key value
      | none => seen
    let slots := if storageOp then (account, seen) :: tracer.slots.filter (·.1 != account)
      else tracer.slots
    let callers := tracer.refunds.take evm.message.depth
    let entry : StructLog :=
      { pc := evm.pc
        op := mnemonicOf fork op
        gas := GasMeter.gasLeft evm.gas
        gasCost := stepCost evm result
        depth := evm.message.depth + 1
        error := stepError result
        refund := (callers.sum + evm.substate.refundCounter).toNat
        stack := if config.disableStack then none else some evm.stack.val.reverse
        memory := if config.enableMemory then some evm.memory else none
        returnData := if config.enableReturnData then some evm.returnData else none
        storage := if config.disableStorage ∨ ¬storageOp then none else some seen }
    let refunds := match result with
      | .ok (.child caller _ _) => callers ++ [caller.substate.refundCounter]
      | _ => callers
    { logs := tracer.logs.push entry, slots, refunds }

/-- The opcode trace of a transaction. -/
structure TransactionTrace where
  /-- The gas that the transaction used, after its refund. -/
  gas : Nat
  /-- Whether its message failed: a revert or an exceptional halt.

  The source names a revert and a lack of gas; this specification counts every halt. -/
  failed : Bool
  /-- The output of its message. -/
  returnValue : ByteArray
  /-- The entries of the opcode logger, oldest first. -/
  structLogs : Array StructLog

/-- The trace of a transaction from what its run gives and the logger at its end. -/
def TransactionTrace.ofRun (output : TransactionOutput) (tracer : Tracer) : TransactionTrace where
  gas := output.gasUsed
  failed := output.error.isSome
  returnValue := output.messageOutput
  structLogs := tracer.logs

/-- Run a transaction on the block state `block` at `fork`, with the opcode logger.

It gives what the run gives, and the logger at its end. -/
def traceRun {fork : Fork} (config : TraceConfig) (env : BlockEnvironment fork)
    (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address := some) (lifted : LiftedRules := {}) :
    Except EvmError (TransactionOutput × Tracer) :=
  (processTransactionWith (M := StateT Tracer (Except EvmError))
    (fun evm result => modify (Tracer.record config evm result)) env block included tx
    precompiles lifted).run {}

/-- The opcode trace of `tx`, the `index`-th transaction of its block, after the body so far.

It runs the transaction as the body of the block does. -/
def traceTransaction {fork : Fork} (config : TraceConfig) (env : BlockEnvironment fork)
    (index : Nat) (before : BodyOutput fork) (tx : Transaction) :
    Except BlockError TransactionTrace := do
  let included ← (checkInclusion env.chainId env before.gas (.ofBlock before.block) tx).mapError
    (.invalidTransaction index)
  let (output, tracer) ← (traceRun config env before.block included tx).mapError .aborted
  return .ofRun output tracer

end EthLib.Execution.Rpc

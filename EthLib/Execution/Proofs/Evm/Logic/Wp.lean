module

public import EthLib.Execution.Proofs.Evm.Logic.Triple

/-!
# Proofs: the weakest precondition of every opcode

For each opcode, fork and postcondition, a precondition holds of the frames whose step ends in it.

The step ends in the frame it gives, in an exceptional halt, or after a message.

After a message, it ends in the frame that resumes from the end of the message.

The rule of an opcode with an instruction, on a frame of a code, follows from it.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter] {bound : Nat}

/-- A result of an instruction on the frame `evm` ends in a frame that `Q` holds of.

That is the frame it gives, or the exceptional halt of `evm` on an error that does not abort. -/
def Ends (evm : Evm fork Meter) (Q : Evm fork Meter → Prop) :
    Except EvmError (Evm fork Meter) → Prop
  | .ok after => Q after
  | .error e => e.aborts = false ∧ Q (exceptionalHalt evm e)

/-- A result of a step of the frame `evm` ends in a frame that `Q` holds of, under a runner.

A message must have less gas than the bound, and the runner must end it with a frame.

The frame then resumes from that frame, or halts exceptionally. -/
def EndsBy (runChild : MessageRunner fork Meter bound) (evm : Evm fork Meter)
    (Q : Evm fork Meter → Prop) : Except EvmError (StepResult fork Meter) → Prop
  | .ok (.next after) => Q after
  | .ok (.child caller message resume) =>
    -- A runner that fails aborts the whole run, so no frame ends that step.
    ∃ lt : message.gas < bound, ∃ child, runChild caller message lt = .ok child ∧
      Ends evm Q (resume child.1)
  | .error e => e.aborts = false ∧ Q (exceptionalHalt evm e)

/-- A result of an instruction, as a step that gives the next frame, ends where it ends. -/
@[simp] theorem endsBy_map_next {runChild : MessageRunner fork Meter bound}
    {evm : Evm fork Meter} {Q : Evm fork Meter → Prop} (r : Except EvmError (Evm fork Meter)) :
    EndsBy runChild evm Q (StepResult.next <$> r) ↔ Ends evm Q r := by
  cases r <;> rfl

/-- The weakest precondition of the opcode `op` at fork `fork` for the postcondition `Q`.

It names the instruction of each opcode, so Lean rejects it if one is missing.

Its meaning holds for an opcode that the fork decodes, which gates each opcode by its fork. -/
def wp (fork : Fork) (runChild : MessageRunner fork Meter bound) (op : Op)
    (Q : Evm fork Meter → Prop) (evm : Evm fork Meter) : Prop :=
  match op with
  -- The opcodes that read and write the stack alone.
  | .add => Ends evm Q (binaryOp OPCODE_ADD add evm)
  | .mul => Ends evm Q (binaryOp OPCODE_MUL mul evm)
  | .sub => Ends evm Q (binaryOp OPCODE_SUB sub evm)
  | .div => Ends evm Q (binaryOp OPCODE_DIV div evm)
  | .sdiv => Ends evm Q (binaryOp OPCODE_SDIV sdiv evm)
  | .mod => Ends evm Q (binaryOp OPCODE_MOD mod evm)
  | .smod => Ends evm Q (binaryOp OPCODE_SMOD smod evm)
  | .addmod => Ends evm Q (ternaryOp OPCODE_ADDMOD addmod evm)
  | .mulmod => Ends evm Q (ternaryOp OPCODE_MULMOD mulmod evm)
  | .exp => Ends evm Q (expStep fork evm)
  | .signextend => Ends evm Q (binaryOp OPCODE_SIGNEXTEND signextend evm)
  | .lt => Ends evm Q (binaryOp OPCODE_LT lessThan evm)
  | .gt => Ends evm Q (binaryOp OPCODE_GT greaterThan evm)
  | .slt => Ends evm Q (binaryOp OPCODE_SLT signedLessThan evm)
  | .sgt => Ends evm Q (binaryOp OPCODE_SGT signedGreaterThan evm)
  | .eq => Ends evm Q (binaryOp OPCODE_EQ equal evm)
  | .iszero => Ends evm Q (unaryOp OPCODE_ISZERO isZero evm)
  | .and => Ends evm Q (binaryOp OPCODE_AND bitwiseAnd evm)
  | .or => Ends evm Q (binaryOp OPCODE_OR bitwiseOr evm)
  | .xor => Ends evm Q (binaryOp OPCODE_XOR bitwiseXor evm)
  | .not => Ends evm Q (unaryOp OPCODE_NOT bitwiseNot evm)
  | .byte => Ends evm Q (binaryOp OPCODE_BYTE getByte evm)
  | .shl => Ends evm Q (binaryOp OPCODE_SHL bitwiseShl evm)
  | .shr => Ends evm Q (binaryOp OPCODE_SHR bitwiseShr evm)
  | .sar => Ends evm Q (binaryOp OPCODE_SAR bitwiseSar evm)
  | .clz => Ends evm Q (unaryOp OPCODE_CLZ countLeadingZeros evm)
  | .keccak256 => Ends evm Q (keccak256Step evm)
  | .pop => Ends evm Q (popStep evm)
  | .push n => Ends evm Q (pushN n evm)
  | .dup n => Ends evm Q (dupN n evm)
  | .swap n => Ends evm Q (swapN n evm)
  | .dupn => .glamsterdam ≤ fork ∧ Ends evm Q (dupnStep evm)
  | .swapn => .glamsterdam ≤ fork ∧ Ends evm Q (swapnStep evm)
  | .exchange => .glamsterdam ≤ fork ∧ Ends evm Q (exchangeStep evm)
  -- The opcodes of control flow.
  | .stop => Ends evm Q (stopStep evm)
  | .jump => Ends evm Q (jumpStep evm)
  | .jumpi => Ends evm Q (jumpiStep evm)
  | .pc => Ends evm Q (readFrame OPCODE_PC (fun evm => BitVec.ofNat 256 evm.pc) evm)
  | .gas =>
    Ends evm Q (readFrame OPCODE_GAS (fun evm => BitVec.ofNat 256 (GasMeter.gasLeft evm.gas)) evm)
  | .jumpdest => Ends evm Q (jumpdestStep evm)
  -- The opcodes of memory, call data, code and return data.
  | .mload => Ends evm Q (mloadStep evm)
  | .mstore => Ends evm Q (mstoreStep evm)
  | .mstore8 => Ends evm Q (mstore8Step evm)
  | .msize => Ends evm Q (readFrame OPCODE_MSIZE (fun evm => BitVec.ofNat 256 evm.memory.size) evm)
  | .mcopy => Ends evm Q (mcopyStep evm)
  | .calldataload => Ends evm Q (calldataloadStep evm)
  | .calldatasize =>
    Ends evm Q (readFrame OPCODE_CALLDATASIZE (fun evm => BitVec.ofNat 256 evm.message.data.size)
      evm)
  | .calldatacopy => Ends evm Q (copyToMemory OPCODE_CALLDATACOPY_BASE evm.message.data evm)
  | .codesize =>
    Ends evm Q (readFrame OPCODE_CODESIZE (fun evm => BitVec.ofNat 256 evm.code.size) evm)
  | .codecopy => Ends evm Q (copyToMemory OPCODE_CODECOPY_BASE evm.code evm)
  | .returndatasize =>
    Ends evm Q (readFrame OPCODE_RETURNDATASIZE (fun evm => BitVec.ofNat 256 evm.returnData.size)
      evm)
  | .returndatacopy => Ends evm Q (returndatacopyStep evm)
  -- The opcodes that halt with output.
  | .«return» => Ends evm Q (returnStep evm)
  | .revert => .byzantium ≤ fork ∧ Ends evm Q (revertStep evm)
  -- The opcodes that read the message, the transaction and the block.
  | .address =>
    Ends evm Q (readFrame OPCODE_ADDRESS (fun evm => evm.message.currentTarget.toU256) evm)
  | .origin => Ends evm Q (readFrame OPCODE_ORIGIN (fun evm => evm.message.txEnv.origin.toU256) evm)
  | .caller => Ends evm Q (readFrame OPCODE_CALLER (fun evm => evm.message.caller.toU256) evm)
  | .callvalue => Ends evm Q (readFrame OPCODE_CALLVALUE (fun evm => evm.message.value) evm)
  | .gasprice => Ends evm Q (readNumber OPCODE_GASPRICE (fun evm => evm.message.txEnv.gasPrice) evm)
  | .blockhash => Ends evm Q (blockhashStep evm)
  | .coinbase =>
    Ends evm Q (readFrame OPCODE_COINBASE (fun evm => evm.message.blockEnv.coinbase.toU256) evm)
  | .timestamp =>
    Ends evm Q (readFrame OPCODE_TIMESTAMP (fun evm => evm.message.blockEnv.timestamp) evm)
  | .number => Ends evm Q (readNumber OPCODE_NUMBER (fun evm => evm.message.blockEnv.number) evm)
  | .prevrandao =>
    if h : .paris ≤ fork then
      Ends evm Q (readFrame OPCODE_PREVRANDAO
        (fun evm => U256.fromBeBytes (evm.message.blockEnv.prevRandao h)) evm)
    else Ends evm Q (readNumber OPCODE_PREVRANDAO (fun evm => evm.message.blockEnv.difficulty) evm)
  | .gaslimit =>
    Ends evm Q (readNumber OPCODE_GASLIMIT (fun evm => evm.message.blockEnv.gasLimit) evm)
  | .chainid =>
    .istanbul ≤ fork ∧ Ends evm Q (readFrame OPCODE_CHAINID
      (fun evm => BitVec.ofNat 256 evm.message.blockEnv.chainId.toNat) evm)
  | .basefee =>
    ∃ h : .london ≤ fork, Ends evm Q (readNumber OPCODE_BASEFEE
      (fun evm => evm.message.blockEnv.baseFeePerGas h) evm)
  | .blobhash => ∃ h : .dencun ≤ fork, Ends evm Q (blobhashStep h evm)
  | .blobbasefee =>
    ∃ h : .dencun ≤ fork, Ends evm Q (readNumber OPCODE_BLOBBASEFEE
      (fun evm => evm.message.blockEnv.blobBaseFee h) evm)
  | .slotnum =>
    ∃ h : .glamsterdam ≤ fork, Ends evm Q (readFrame OPCODE_SLOTNUM
      (fun evm => BitVec.ofNat 256 (evm.message.blockEnv.slotNumber h).toNat) evm)
  -- The opcodes that read accounts.
  | .balance => Ends evm Q (balanceStep evm)
  | .selfbalance =>
    .istanbul ≤ fork ∧ Ends evm Q (readFrame OPCODE_SELFBALANCE
      (fun evm => (evm.state.getAccount evm.message.currentTarget).balance)
      (recordAccountRead evm evm.message.currentTarget))
  | .extcodesize => Ends evm Q (extcodesizeStep evm)
  | .extcodecopy => Ends evm Q (extcodecopyStep evm)
  | .extcodehash => .constantinople ≤ fork ∧ Ends evm Q (extcodehashStep evm)
  -- The opcodes of storage, transient storage and logs.
  | .sload => Ends evm Q (sloadStep evm)
  | .sstore => Ends evm Q (sstoreStep evm)
  | .tload => .dencun ≤ fork ∧ Ends evm Q (tloadStep evm)
  | .tstore => .dencun ≤ fork ∧ Ends evm Q (tstoreStep evm)
  | .log n => Ends evm Q (logStep n.val evm)
  | .selfdestruct => Ends evm Q (selfdestructStep fork evm)
  -- The opcodes that send a message: the runner ends it, then the frame resumes.
  | .call => EndsBy runChild evm Q (callStep .call evm)
  | .callcode => EndsBy runChild evm Q (callStep .callcode evm)
  | .delegatecall => .homestead ≤ fork ∧ EndsBy runChild evm Q (callStep .delegatecall evm)
  | .staticcall => .byzantium ≤ fork ∧ EndsBy runChild evm Q (callStep .staticcall evm)
  | .create => EndsBy runChild evm Q (createStep false evm)
  | .create2 => .constantinople ≤ fork ∧ EndsBy runChild evm Q (createStep true evm)

/-- An error ends a step in the exceptional halt, unless it aborts the run. -/
theorem endsBy_throw {runChild : MessageRunner fork Meter bound} {evm : Evm fork Meter}
    {Q : Evm fork Meter → Prop} (e : EvmError) :
    EndsBy runChild evm Q (throw e) ↔ e.aborts = false ∧ Q (exceptionalHalt evm e) :=
  Iff.rfl

/-- An opcode with no instruction aborts the run, so its step ends in no frame.

The proof below uses it for the fork gates of the tables. -/
theorem endsBy_unspecified {runChild : MessageRunner fork Meter bound}
    {evm : Evm fork Meter} {Q : Evm fork Meter → Prop} (byte : UInt8) :
    EndsBy runChild evm Q (throw (.unspecifiedOpcode byte)) ↔ False :=
  iff_false_intro fun h => by cases h.1

attribute [local simp] endsBy_unspecified

/-- The weakest precondition of an opcode is that of its step, at every fork.

The byte at the program counter of the frame decodes to `op`.

Then it holds exactly when the step ends in `Q`, under the runner of messages. -/
theorem wp_iff_endsBy {runChild : MessageRunner fork Meter bound} {evm : Evm fork Meter}
    {Q : Evm fork Meter → Prop} {op : Op} (hlt : evm.pc < evm.code.size)
    (hop : Op.ofByte fork evm.code[evm.pc] = some op) :
    wp fork runChild op Q evm ↔ EndsBy runChild evm Q (step fork evm) := by
  unfold step
  simp only [hlt, ↓reduceDIte, hop]
  clear hop
  -- Each opcode runs one instruction, which some forks gate.
  --
  -- The weakest precondition of a gated opcode carries the same gate.
  cases op <;>
    simp only [wp, instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
      environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
      selfdestructOpStep, messageInstruction, callInstruction, createInstruction,
      HOrElse.hOrElse, OrElse.orElse, Option.orElse, endsBy_map_next] <;>
    first
    | rfl
    | (by_cases hf : Fork.homestead ≤ fork <;> simp [hf]; done)
    | (by_cases hf : Fork.byzantium ≤ fork <;> simp [hf]; done)
    | (by_cases hf : Fork.constantinople ≤ fork <;> simp [hf]; done)
    | (by_cases hf : Fork.istanbul ≤ fork <;> simp [hf]; done)
    | (by_cases hf : Fork.london ≤ fork <;> simp [hf]; done)
    | (by_cases hf : Fork.paris ≤ fork <;> simp [hf]; done)
    | (by_cases hf : Fork.dencun ≤ fork <;> simp [hf]; done)
    | (by_cases hf : Fork.glamsterdam ≤ fork <;> simp [hf]; done)

/-- The weakest precondition of the step of a frame, at every fork, for the postcondition `Q`.

Past the end of its code, the frame stops as STOP does.

A byte that is no opcode at the fork halts it exceptionally. -/
def wpFrame (fork : Fork) (runChild : MessageRunner fork Meter bound) (Q : Evm fork Meter → Prop)
    (evm : Evm fork Meter) : Prop :=
  if h : evm.pc < evm.code.size then
    match Op.ofByte fork evm.code[evm.pc] with
    | some op => wp fork runChild op Q evm
    | none => Q (exceptionalHalt evm (.invalidOpcode evm.code[evm.pc]))
  else Ends evm Q (stopStep evm)

/-- The weakest precondition of the step of a frame is that of its step, at every fork. -/
theorem wpFrame_iff_endsBy {runChild : MessageRunner fork Meter bound} {evm : Evm fork Meter}
    {Q : Evm fork Meter → Prop} :
    wpFrame fork runChild Q evm ↔ EndsBy runChild evm Q (step fork evm) := by
  rw [wpFrame]
  split
  · next hlt =>
    split
    · next op hop => exact wp_iff_endsBy hlt hop
    · next hop =>
      -- An invalid opcode is an exceptional halt, which does not abort the run.
      unfold step
      simp only [hlt, ↓reduceDIte, hop]
      rw [endsBy_throw]
      exact (and_iff_right rfl).symm
  · next hlt =>
    unfold step
    simp only [hlt, ↓reduceDIte, endsBy_map_next]

/-! ## The steps that send no message -/

/-- A running frame reaches a frame of `Q` in one step exactly when its instruction ends in `Q`.

The instruction is that of the opcode that the byte at the program counter decodes to. -/
theorem exists_step_iff_ends {evm : Evm fork Meter} {Q : Evm fork Meter → Prop} {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} (running : evm.running = true)
    (hlt : evm.pc < evm.code.size) (decoded : Op.ofByte fork evm.code[evm.pc] = some op)
    (hrun : instruction fork op = some run) :
    (∃ after, Step fork evm after ∧ Q after) ↔ Ends evm Q (run evm) := by
  have hs := step_of_instruction hlt decoded hrun
  constructor
  · rintro ⟨after, h, hq⟩
    cases h with
    | next _ hn =>
      rw [hs] at hn
      cases hr : run evm <;> rw [hr] at hn <;> cases hn
      exact hq
    | halt _ he ha =>
      rw [hs] at he
      cases hr : run evm <;> rw [hr] at he <;> cases he
      exact ⟨ha, hq⟩
  · intro h
    cases hr : run evm with
    | ok after =>
      rw [hr] at h
      exact ⟨after, .next running (by rw [hs, hr]; rfl), h⟩
    | error e =>
      rw [hr] at h
      exact ⟨_, .halt running (by rw [hs, hr]; rfl) h.1, h.2⟩

/-- The weakest precondition of an opcode with an instruction is that its instruction ends in `Q`.

It holds for every runner of messages, since the instruction sends none. -/
theorem wp_iff_ends {runChild : MessageRunner fork Meter bound} {evm : Evm fork Meter}
    {Q : Evm fork Meter → Prop} {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} (hlt : evm.pc < evm.code.size)
    (decoded : Op.ofByte fork evm.code[evm.pc] = some op) (hrun : instruction fork op = some run) :
    wp fork runChild op Q evm ↔ Ends evm Q (run evm) := by
  rw [wp_iff_endsBy hlt decoded, step_of_instruction hlt decoded hrun, endsBy_map_next]

/-- The weakest precondition of an opcode with an instruction, at every fork.

The frame runs, and its byte at the program counter decodes to the opcode.

Then it holds exactly when one step reaches a frame that `Q` holds of. -/
theorem wp_iff_step {runChild : MessageRunner fork Meter bound} {evm : Evm fork Meter}
    {Q : Evm fork Meter → Prop} {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} (running : evm.running = true)
    (hlt : evm.pc < evm.code.size) (decoded : Op.ofByte fork evm.code[evm.pc] = some op)
    (hrun : instruction fork op = some run) :
    wp fork runChild op Q evm ↔ ∃ after, Step fork evm after ∧ Q after :=
  (wp_iff_ends hlt decoded hrun).trans (exists_step_iff_ends running hlt decoded hrun).symm

/-- The runner of no message: its bound admits none. -/
def noMessage : MessageRunner fork Meter 0 := fun _ _ lt => absurd lt (Nat.not_lt_zero _)

/-- A triple of one step, from the weakest precondition of an opcode with an instruction.

Each frame of `P` runs, decodes the opcode, and meets the weakest precondition of `Q`. -/
theorem Hoare.of_wp {P Q : Evm fork Meter → Prop} {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : instruction fork op = some run)
    (h : ∀ evm, P evm → evm.running = true ∧ ∃ hlt : evm.pc < evm.code.size,
      Op.ofByte fork evm.code[evm.pc] = some op ∧ wp fork noMessage op Q evm) :
    Hoare fork P Q :=
  Triple.of_step fun evm hp =>
    let ⟨running, hlt, decoded, hwp⟩ := h evm hp
    (wp_iff_step running hlt decoded hrun).mp hwp

end EthLib.Execution.Evm.Logic

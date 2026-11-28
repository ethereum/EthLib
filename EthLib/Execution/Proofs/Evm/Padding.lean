module

public import EthLib.Execution.Proofs.Evm.CodeKept
public import EthLib.Execution.Evm.Interpreter
public import EthLib.Execution.Proofs.Evm.Padding.Instructions
public import EthLib.Execution.Proofs.Evm.Padding.JumpDest

/-!
# Proofs: zero bytes after the code change nothing but CODESIZE

The scan of the padded code finds the same jump destinations, and adds none.

The immediate byte of DUPN, SWAPN and EXCHANGE stays the same.

A padded frame holds the destinations of its padded code.

Every step but CODESIZE gives the same result, with the padding in each frame.

The frame must hold the destinations of its code.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork byteAtOrZero byteAtOrZero_append_zeros byteAtOrZero_of_size_le)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The frame with `k` zero bytes after its code, and the jump destinations of the padded code. -/
def Evm.padCode (evm : Evm fork Meter) (k : Nat) : Evm fork Meter :=
  { evm with
    code := evm.code ++ ByteArray.mk (Array.replicate k 0)
    -- The destinations come from a scan of the padded code.
    validJumpDestinations :=
      _root_.EthLib.Execution.Evm.validJumpDestinations
        (evm.code ++ ByteArray.mk (Array.replicate k 0)) }

/-- A result of a step, with `k` zero bytes after the code of each frame that it gives. -/
def StepResult.padCode (k : Nat) : StepResult fork Meter → StepResult fork Meter
  | .next after => .next (after.padCode k)
  | .child caller message resume =>
    .child (caller.padCode k) message fun child => (Evm.padCode · k) <$> resume child

/-- Zero bytes after the code keep each jump destination, and add none. -/
theorem isValidJumpDest_append_zeros (code : ByteArray) (k pc : Nat) :
    isValidJumpDest (validJumpDestinations (code ++ ByteArray.mk (Array.replicate k 0))) pc =
      isValidJumpDest (validJumpDestinations code) pc := by
  rw [Bool.eq_iff_iff, isValidJumpDest_iff_boundaryFrom, isValidJumpDest_iff_boundaryFrom,
    byteAtOrZero_append_zeros]
  by_cases hpc : pc < code.size
  · rw [boundaryFrom_append_zeros_iff hpc]
  · -- Past the end of the code the byte is zero, which is no JUMPDEST.
    rw [byteAtOrZero_of_size_le (Nat.le_of_not_lt hpc)]
    simp [JUMPDEST]

/-- Zero bytes after the code keep the immediate byte of every opcode. -/
theorem immediateByte_append_zeros (code : ByteArray) (k pc : Nat) :
    immediateByte (code ++ ByteArray.mk (Array.replicate k 0)) pc = immediateByte code pc :=
  byteAtOrZero_append_zeros code k (pc + 1)

/-- A step of a frame with zero bytes after its code is the step of the frame, padded.

The frame holds the destinations of its code.

The opcode at the program counter must not be CODESIZE, which reads the size of the code. -/
theorem step_padCode {evm : Evm fork Meter} (k : Nat)
    (flags : HasDestinations evm)
    (hsize : ∀ hlt : evm.pc < evm.code.size, Op.ofByte fork evm.code[evm.pc] ≠ some .codesize) :
    step fork (evm.padCode k) = StepResult.padCode k <$> step fork evm := by
  -- The padded code has the same bytes and the same destinations.
  have hb := byteAtOrZero_append_zeros evm.code k
  have hj : ∀ i, isValidJumpDest
      (validJumpDestinations (evm.code ++ ByteArray.mk (Array.replicate k 0))) i =
        isValidJumpDest evm.validJumpDestinations i := by
    intro i
    rw [flags]
    exact isValidJumpDest_append_zeros evm.code k i
  -- A frame with the code of the step pads to the frame with the padded code.
  have pad : ∀ after : Evm fork Meter, after.code = evm.code →
      { after with
        code := evm.code ++ ByteArray.mk (Array.replicate k 0)
        validJumpDestinations :=
          validJumpDestinations (evm.code ++ ByteArray.mk (Array.replicate k 0)) } =
        after.padCode k := by
    intro after h
    simp only [Evm.padCode, h]
  have hsizes : (evm.code ++ ByteArray.mk (Array.replicate k 0)).size = evm.code.size + k := by
    simp
  unfold step
  simp only [Evm.padCode]
  by_cases hlt : evm.pc < evm.code.size
  · have hlt' : evm.pc < (evm.code ++ ByteArray.mk (Array.replicate k 0)).size := by omega
    simp only [hlt, hlt', ↓reduceDIte]
    -- The byte at the program counter is the same.
    have hbyte : (evm.code ++ ByteArray.mk (Array.replicate k 0))[evm.pc] = evm.code[evm.pc] := by
      have := hb evm.pc
      simp only [byteAtOrZero, hlt, hlt', ↓reduceDIte] at this
      exact this
    simp only [hbyte]
    rcases hop : Op.ofByte fork evm.code[evm.pc] with _ | op
    · rfl
    have hop' : op ≠ .codesize := fun h => hsize hlt (h ▸ hop)
    dsimp only
    rcases hi : instruction fork op with _ | run
    · rcases hm : messageInstruction fork op with _ | run
      · rfl
      · dsimp only
        rw [messageInstruction_swapsCode hm evm _ _ hb hj]
        rcases hr : run evm with e | result
        · rfl
        -- Each frame of the result keeps the code of the step.
        have self := (messageInstruction_swapsCode hm).withCode_self hr
        refine congrArg Except.ok ?_
        cases result with
        | next after =>
          have hc : after.code = evm.code := congrArg (fun r => match r with
            | .next a => a.code | .child c _ _ => c.code) self |>.symm
          exact congrArg StepResult.next (pad after hc)
        | child caller message resume =>
          simp only [StepResult.withCode, StepResult.child.injEq] at self
          obtain ⟨hcaller, -, hresume⟩ := self
          simp only [StepResult.withCode, StepResult.padCode]
          congr 1
          · exact pad caller (congrArg Evm.code hcaller).symm
          · funext child
            rcases hres : resume child with e | after
            · rfl
            · have hc := congrFun hresume child
              rw [hres] at hc
              exact congrArg Except.ok (pad after (congrArg Evm.code (Except.ok.inj hc)).symm)
    · dsimp only
      rw [instruction_swapsCode hi hop' evm _ _ hb hj]
      rcases hr : run evm with e | after
      · rfl
      · exact congrArg (Except.ok ∘ StepResult.next)
          (pad after ((instruction_swapsCode hi hop').code_eq hr).1)
  · simp only [hlt, ↓reduceDIte]
    by_cases hlt' : evm.pc < (evm.code ++ ByteArray.mk (Array.replicate k 0)).size
    · -- Past the end of the code, the padded frame reads a zero byte, which is STOP.
      have hzero : (evm.code ++ ByteArray.mk (Array.replicate k 0))[evm.pc] = 0 := by
        have := hb evm.pc
        simp only [byteAtOrZero, hlt, hlt', ↓reduceDIte] at this
        exact this
      -- STOP dates from Frontier, the first fork.
      have hstop : Op.ofByte fork 0 = some .stop :=
        Op.ofByte_eq_some_iff.mpr ⟨rfl, Nat.zero_le fork.ctorIdx⟩
      have hinst : instruction (Meter := Meter) fork .stop = some stopStep := rfl
      simp only [hlt', ↓reduceDIte, hzero, hstop, hinst]
      rfl
    · simp only [hlt', ↓reduceDIte]
      rfl

end EthLib.Execution.Evm

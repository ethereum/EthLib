module

public import EthLib.Networking.Exports.Rlpx
public import EthLib.Networking.Proofs.Rlpx.Frame
import all EthLib.Networking.Exports.Rlpx

/-!
# Proofs: the frame reader that the RLPx exports call

It reads each frame where the one before ends, and gives what reading the rest of the stream gives.
-/

@[expose] public section

namespace EthLib.Networking.Rlpx.Exports

/-- The bytes after a frame are the last bytes of the input, as many as there are of them. -/
private theorem extract_rest {st st' : FrameState} {input data rest : ByteArray}
    (h : readFrame st input = .ok (data, st', rest)) :
    input.extract (input.size - rest.size) input.size = rest := by
  -- The reader gives the bytes from the offset where the frame ends.
  unfold readFrame at h
  cases hr : readFrameAt st input 0 with
  | error e => simp [hr, bind, Except.bind] at h
  | ok r =>
    obtain ⟨d, s, k⟩ := r
    simp only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    -- Both cuts start at the same place, or both are empty past the end.
    apply ByteArray.extract_eq_extract_left.mpr
    simp only [ByteArray.size_extract]
    omega

/-- Reading from an offset gives what reading the bytes from that offset gives. -/
theorem readFrames_extract (fuel : Nat) (st : FrameState) (input : ByteArray) (pos : Nat) :
    readFrames fuel st input pos = readFrames fuel st (input.extract pos input.size) 0 := by
  induction fuel generalizing st input pos with
  | zero => simp [readFrames]
  | succ fuel ih =>
    -- The bytes from the offset are as many as the input has left there.
    have hB : (input.extract pos input.size).size = input.size - pos := by simp
    -- Both sides read the frame at the start of the bytes from the offset.
    rw [readFrames, readFrames, readFrameAt_eq, readFrameAt_eq, ByteArray.extract_zero_size, hB,
      Nat.sub_zero]
    split_ifs with h0
    · rfl
    cases hr : readFrame st (input.extract pos input.size) with
    | error e => rfl
    | ok r =>
      obtain ⟨data, st', rest⟩ := r
      have hrest := extract_rest hr
      -- The bytes after the frame are at most the bytes from the offset.
      have hle : rest.size ≤ input.size - pos := by
        have := congrArg ByteArray.size hrest
        rw [ByteArray.size_extract] at this
        omega
      -- The input from the end of the frame is the rest of the bytes from the offset.
      have hcut : input.extract (input.size - rest.size) input.size = rest := by
        refine Eq.trans ?_ hrest
        rw [ByteArray.extract_extract, hB]
        congr 1 <;> omega
      -- Each side goes on from the bytes after the frame.
      simp only [Except.map, bind, Except.bind]
      rw [hB] at hrest
      rw [ih, ih (input := input.extract pos input.size), hcut, hB, hrest]

/-- With no fuel, the reader accepts only an empty stream. -/
theorem readFrames_zero (st : FrameState) (input : ByteArray) :
    readFrames 0 st input 0 =
      if input.size = 0 then .ok [] else .error (.tooShort 32 input.size) := by
  simp [readFrames]

/-- The reader reads the frame at the start of the stream, then the frames of the rest. -/
theorem readFrames_succ (fuel : Nat) (st : FrameState) (input : ByteArray) :
    readFrames (fuel + 1) st input 0 =
      if input.size = 0 then .ok [] else do
        let (data, st, rest) ← readFrame st input
        return data :: (← readFrames fuel st rest 0) := by
  -- The frame at offset 0 is the frame at the start of the stream.
  rw [readFrames, readFrameAt_eq, ByteArray.extract_zero_size, Nat.sub_zero]
  split_ifs with h0
  · rfl
  cases hr : readFrame st input with
  | error e => rfl
  | ok r =>
    obtain ⟨data, st', rest⟩ := r
    -- The rest of the stream starts at the offset where the frame ends.
    simp only [Except.map, bind, Except.bind]
    rw [readFrames_extract, extract_rest hr]

end EthLib.Networking.Rlpx.Exports

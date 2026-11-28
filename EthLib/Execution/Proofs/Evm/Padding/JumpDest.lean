module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Execution.Proofs.Evm.Machine.JumpDest

/-!
# Proofs: zero bytes after the code keep the opcode boundaries in it

The next opcode depends only on the bytes, which the zeros do not change inside the code.

So the boundaries inside the code are the same, and the scan finds the same destinations there.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (byteAtOrZero byteAtOrZero_append_zeros)

/-- Zero bytes after the code keep the next opcode of every position. -/
theorem nextOpcode_append_zeros (code : ByteArray) (k pc : Nat) :
    nextOpcode (code ++ ByteArray.mk (Array.replicate k 0)) pc = nextOpcode code pc := by
  simp only [nextOpcode, byteAtOrZero_append_zeros]

/-- Zero bytes after the code keep each boundary inside the code, and add none there. -/
theorem boundaryFrom_append_zeros_iff {code : ByteArray} {k start pc : Nat}
    (hpc : pc < code.size) :
    BoundaryFrom (code ++ ByteArray.mk (Array.replicate k 0)) start pc ↔
      BoundaryFrom code start pc := by
  constructor
  · intro h
    induction h with
    | here _ => exact .here hpc
    | @step start pc _ rest ih =>
      -- The start lies before the boundary, so inside the code.
      have := rest.bounds
      have := lt_nextOpcode (code ++ ByteArray.mk (Array.replicate k 0)) start
      rw [nextOpcode_append_zeros] at ih
      exact .step (by omega) (ih hpc)
  · intro h
    induction h with
    | here hs => exact .here (by simp; omega)
    | step hs _ ih =>
      exact .step (by simp; omega) (by rw [nextOpcode_append_zeros]; exact ih hpc)

end EthLib.Execution.Evm

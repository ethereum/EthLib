import EthLib.Consensus.Ssz.Codec.Layout

/-! Sequence layouts preserve the caller’s mixing word. -/

namespace EthLib.Consensus.Ssz

/-- Sequence layouts retain the exact mixing word supplied by their caller. -/
theorem sequenceLayout_mixin {element : Desc} {values : List Value} {positions : Option Nat}
    {word : Option Bytes} {layout : MerkleLayout}
    (success : sequenceLayout element values positions word = .ok layout) : layout.mixin = word := by
  -- The packing decision changes only the leaves and capacity, leaving the supplied metadata unchanged.
  unfold sequenceLayout at success
  split at success
  · cases wrote : serializeEach element values <;>
      simp only [wrote, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        reduceCtorEq] at success
    exact congrArg MerkleLayout.mixin success.symm
  · cases success
    rfl

end EthLib.Consensus.Ssz

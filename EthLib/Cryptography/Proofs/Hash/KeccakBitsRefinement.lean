module

public import EthLib.Cryptography.Proofs.Hash.KeccakBitsBlocks

/-!
# Keccak-256 sponge refinement

FIPS 202 section 4, Algorithm 8, absorbs each padded rate block in order.
The output is the first 256 state bits.
The bit model uses the original Keccak padding from section 5.1.
-/

@[expose] public section
namespace EthLib.Cryptography.Hash.KeccakBits

private theorem block_step (msg : ByteArray) (i : Fin (Keccak.blockCount msg.size)) (a : Keccak.State) :
    ofLanes (Keccak.keccakF (Keccak.Internal.absorbBlock a (paddedByteBlock msg i).toList)) =
      permutation (absorb (ofLanes a) (paddedBlock msg (bitIndex msg i))) := by
  rw [permutation_ofLanes, absorbBlock_ofLanes, byteBlock_eq_paddedBlock]
private theorem fold_blocks (msg : ByteArray) (indices : List (Fin (Keccak.blockCount msg.size)))
    (a : Keccak.State) :
    ofLanes (indices.foldl (fun a i => Keccak.keccakF (Keccak.Internal.absorbBlock a (paddedByteBlock msg i).toList)) a) =
      indices.foldl (fun a i => permutation (absorb a (paddedBlock msg (bitIndex msg i)))) (ofLanes a) := by
  induction indices generalizing a with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih, block_step]
private theorem zero_ofLanes : ofLanes Keccak.State.zero = (fun _ _ _ => false) := by
  funext x y z
  simp [ofLanes, Keccak.State.zero]
/-- Complete block absorption agrees for every byte message. -/
theorem absorbAll_eq (msg : ByteArray) :
    ofLanes ((Keccak.Internal.chunks Keccak.RATE (Keccak.blockCount msg.size) (Keccak.pad msg).data.toList).foldl
      (fun a block => Keccak.keccakF (Keccak.Internal.absorbBlock a block)) Keccak.State.zero) =
      absorbAll msg := by
  unfold absorbAll
  rw [show Keccak.RATE = 136 by rfl, sourceChunks_eq, List.foldl_map]
  rw [← blockIndices_eq msg, List.foldl_map]
  rw [← zero_ofLanes]
  exact fold_blocks msg _ _

/-- The lane implementation agrees with the independent bit sponge for every input. -/
theorem keccak256_eq (msg : ByteArray) : Keccak.keccak256 msg = KeccakBits.keccak256 msg := by
  change (show Vector UInt8 32 from Keccak.keccak256 msg) = KeccakBits.keccak256 msg
  apply Vector.ext
  intro i hi
  let state : Keccak.State := (Keccak.Internal.chunks Keccak.RATE (Keccak.blockCount msg.size)
    (Keccak.pad msg).data.toList).foldl
      (fun a block => Keccak.keccakF (Keccak.Internal.absorbBlock a block)) Keccak.State.zero
  have source : (Keccak.keccak256 msg)[i]'(by simpa [Keccak.DIGEST_LEN] using hi) =
      (Keccak.Internal.squeeze state)[i]'(by simpa [Keccak.DIGEST_LEN] using hi) := by rfl
  have independent : (KeccakBits.keccak256 msg)[i]'hi = outputByte (absorbAll msg) i := by
    simp only [KeccakBits.keccak256, Vector.getElem_ofFn]
  have same : ofLanes state = absorbAll msg := absorbAll_eq msg
  have out := outputByte_eq_squeeze state ⟨i, hi⟩
  change outputByte (ofLanes state) i = (Keccak.Internal.squeeze state)[i]'(by simpa [Keccak.DIGEST_LEN] using hi) at out
  rw [same] at out
  exact source.trans (out.symm.trans independent.symm)

end EthLib.Cryptography.Hash.KeccakBits

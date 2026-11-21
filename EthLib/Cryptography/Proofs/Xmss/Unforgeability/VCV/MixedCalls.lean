module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedMixed
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedPhases
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# A single physical public hash in the mixed program

The same mixed port carries an adversary's raw bytes, a signing trial and a verifier's word.

A positive cutoff produces the complete native reply from the shared graph.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig TwoLayerGraph Honest OracleComp OracleSpec
open CanonicalGraph.PairedQueries
open Constants

@[expose] def mixedHash (b : ByteArray) : OracleComp MixedWorld (Vector UInt8 32) :=
  ofOutput <$> MixedWorld.query (.inl (.inr b.data.toList))

private theorem expand_hash (b : ByteArray) :
    simulateQ (expand PairedHashWord.halves) (mixedHash b) = Honest.hash b := by
  simp [mixedHash, expand, Honest.hash, RandomOraclePairedValue.readHalves, simulateQ_bind,
    liftPublic, Functor.map_map]

/-- Raw bytes are charged before either half, independent of the address or a previous cache hit. -/
theorem mixed_hash (pp : PublicParam) (b : ByteArray) :
    SameMixed pp (simulateQ (selectedImpl pp) (markedFindHash b)) (liftM (mixedHash b)) := by
  intro q r
  cases q with
  | zero =>
    simp [selected_find_zero, mixedHash, mixedImpl, WeightedCap.guard, mixedCost, rawCost,
      visible, OptionT.run_map, StateT.run_map]
  | succ left =>
    rw [selected_find_succ]
    simp only [StateT.run_map, StateT.run_monadLift, monadLift_self, Functor.map_map]
    rw [← expand_hash b]
    simp [mixedHash, mixedImpl, WeightedCap.guard, mixedCost, rawCost, expand, visible,
      OptionT.run_map, StateT.run_map, Functor.map_map]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedSignature
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedPhases
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ResidualGameSchedule
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedStructure

/-!
# The native key at the entry of the guarded client

The sampled parameter fixes the top tree before the client receives its public key.

Key generation consumes no selected public budget and exposes only the low root.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig OracleComp OracleSpec Constants TwoLayerGraph Honest
open LayerGraph.Hidden

noncomputable abbrev topRoot (pp : PublicParam) :=
  simulateQ (selection pp .top).liftQuery (beforeNode pp .top LAYER_HEIGHT 0 >>=
    fun _ => LayerGraph.readOutput (LayerGraph.treeRole LAYER_HEIGHT 0))

attribute [local irreducible] selection beforeNode LayerGraph.readOutput Xmss.node simulateQ inGraph

/-- All successful and refused continuations start from the same sampled public key. -/
theorem guarded_root (pp : PublicParam) :
    SameCap pp (simulateQ (selectedImpl pp) (simulateQ (mark (fun _ => False))
      (Xmss.node (hashOf sourcePass) pp sourcePrf .top LAYER_HEIGHT 0)))
      (liftM (topRoot pp) : Selected pp _) := by
  let native := Xmss.node (hashOf sourcePass) pp sourcePrf .top LAYER_HEIGHT 0
  have core : SameLocal pp (inGraph pp native)
      (liftM (topRoot pp) : WithLocal (ResidualCache pp) _) := root_same pp
  have step : SameCap pp (liftM (inGraph pp native) : Selected pp _) (liftM (topRoot pp)) := by
    simpa only [lift_twice] using sameCap_lift core
  rw [unmarked_phase]
  exact step

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

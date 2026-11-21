module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedCalls
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ResidualGameSchedule

/-!
# Free source phases and charged verification

Key generation uses the unmarked port for every call.

The verifier and adversary use a separate selected port.

It charges even byte strings that encode honest chain or tree addresses.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig OracleSpec OracleComp TwoLayerGraph Constants

/-- The whole unmarked phase retains the complete native state and the unspent budget. -/
theorem unmarked_phase {α : Type} (pp : PublicParam) (p : OracleComp Source α) :
    simulateQ (selectedImpl pp) (simulateQ (mark (fun _ => False)) p) =
      (liftM (inGraph pp p) : Selected pp α) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [inGraph_pure]
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, inGraph_bind, liftM_bind, ih]
    congr 1
    rcases t with ((n | (b | u)) | k) <;> simp [mark, selected_original]

/-- Even an arbitrary chain-shaped byte string is charged when the adversary supplies it. -/
theorem public_phase_call (pp : PublicParam) (b : ByteArray) :
    simulateQ (selectedImpl pp) (simulateQ (mark (fun _ => True)) (hashOf sourcePass b)) =
      simulateQ (selectedImpl pp) (markedFindHash b) := by
  rw [hash_chosen _ _ trivial]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

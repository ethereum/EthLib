module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedGraph
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedSignerRoles

/-!
# Charging the public word at the point of issue

Honest structural hashing lifts the shared hash without inspecting the budget.

A finder trial spends one unit before either half is read.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig TwoLayerGraph OracleSpec OracleComp

/-- Any unmarked physical operation keeps the remaining budget. -/
theorem selected_original (pp : PublicParam) (t : Source.Domain) :
    selectedImpl pp (.inl t) = (liftM (inGraph pp (liftM (Source.query t))) : Selected pp _) := by
  ext budget : 2
  simp [selectedImpl, WeightedCap.guard, selectedFee, eraseMark, StateT.run_monadLift,
    OptionT.run_monadLift, Functor.map_map]

/-- The unmarked structural port reads exactly the two shared rows and keeps both private tables. -/
theorem selected_chainHash (pp : PublicParam) (b : ByteArray) :
    simulateQ (selectedImpl pp) (markedChainHash b) = (liftM (Honest.hash b) : Selected pp _) := by
  rw [markedChainHash, simulateQ_map, simulateQ_spec_query, selected_original]
  have raw := inGraph_hash pp b
  change (inGraph pp (ofOutput <$> (liftM (Source.query (.inl (.inr (.inl b.data.toList)))) :
    OracleComp Source HashOutput))) = _ at raw
  rw [← bind_pure_comp, inGraph_bind] at raw
  simp only [inGraph_pure, bind_pure_comp] at raw
  calc
    _ = (liftM (ofOutput <$> inGraph pp (liftM (Source.query (.inl (.inr (.inl b.data.toList)))))) :
        Selected pp _) := (liftM_map _ _).symm
    _ = _ := by rw [raw]; rfl

/-- No action occurs on the graph at zero budget. -/
theorem selected_find_zero (pp : PublicParam) (b : ByteArray) :
    ((simulateQ (selectedImpl pp) (markedFindHash b)).run).run 0 = pure (none, 0) := by
  simp [markedFindHash, selectedImpl, WeightedCap.guard, selectedFee, OptionT.run_map,
      StateT.run_map]

/-- A positive remaining budget reads both halves of exactly one word. -/
theorem selected_find_succ (pp : PublicParam) (b : ByteArray) (q : Nat) :
    ((simulateQ (selectedImpl pp) (markedFindHash b)).run).run (q + 1) =
      (fun a => (some a, q)) <$> (liftM (Honest.hash b) : Honest.WithLocal
        (ResidualCache pp) _) := by
  have raw := inGraph_hash pp b
  change (inGraph pp (ofOutput <$> (liftM (Source.query (.inl (.inr (.inl b.data.toList)))) :
    OracleComp Source HashOutput))) = _ at raw
  rw [← bind_pure_comp, inGraph_bind] at raw
  simp only [inGraph_pure, bind_pure_comp] at raw
  rw [← raw]
  simp [markedFindHash, selectedImpl, WeightedCap.guard, selectedFee, eraseMark, OptionT.run_map,
    StateT.run_map, Functor.map_map]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

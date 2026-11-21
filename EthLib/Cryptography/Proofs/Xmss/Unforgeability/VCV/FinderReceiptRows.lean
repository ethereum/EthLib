module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderSigningReceipt
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerSignerReplay
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedCalls
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# The physical digest and bottom root in each registration

Every successful finder names its real randomizer and selected codeword.

A later conflict-free extension therefore decodes to the exact registered digest.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open EthLib.Cryptography HashSig Constants OracleSpec OracleComp TwoLayerGraph
    Honest LayerGraph.Hidden
open ChainGraph (digestEquiv)

attribute [local irreducible] simulateQ TwoLayerGraph.graph Xmss.Internal.findCodeword mixedFind
  selection emitStructure Xmss.verifyWith

private theorem trial_of_find {pp q l e m r s rho x out t}
    (ran : Ran q (find pp l e m) r s (some (rho,x)) out t) :
    Trial pp l e m rho x (physical t.1).1 := by
  have actual := ran.project
  rw [forget_find] at actual
  obtain ⟨bytes, afterR, _, finder⟩ := find_cut pp (deferredMixed pp) l e m actual
  refine ⟨halfOf 0 bytes,afterR,physical t.1,?_,le_rfl⟩
  rw [deferredMixed, QueryImpl.simulateQ_compose] at finder
  let base : Randomizer := halfOf 0 bytes
  have image := findCodeword_map_monad
    (simulateQ (CanonicalGraph.PairedQueries.expand PairedHashWord.halves))
    (simulateQ_pure _) (simulateQ_bind _) mixedHash pp l e m base 0 MAX_RANDOMIZER_TRIALS
  simp only [expand_hash] at image
  rw [← image]
  exact finder

private theorem read_trial {pp l e m rho x s last}
    (trial : Trial pp l e m rho x s) (later : s ≤ last) (clean : ¬ (graph pp).Conflict last) :
    messageDigest (VerifierProbe.hashAt pp last) pp l e m rho = some (selectedDigest x) := by
  obtain ⟨d, read, good⟩ := Option.bind_eq_some_iff.mp (trial.decoded later clean)
  simpa only [selectedDigest_eq good] using read

/-- Read back the exact lower registered message digest in the common clean state. -/
theorem Receipt.lower_digest {pp q idx msg sig} (c : Receipt pp q idx msg sig) {last}
    (later : (physical c.lowerPrior).1 ≤ last) (clean : ¬ (graph pp).Conflict last) :
    messageDigest (VerifierProbe.hashAt pp last) pp .bottom (UInt32.ofNat idx.toNat) (packBytes msg)
      sig.bottom.randomizer = some (selectedDigest c.x) := by
  obtain ⟨_,_,_,_,actual,ext⟩ := c.lower
  exact read_trial (trial_of_find actual) (ext.trans later) clean

/-- Read back the exact upper registered message digest at the root signed by this invocation. -/
theorem Receipt.upper_digest {pp q idx msg sig} (c : Receipt pp q idx msg sig) {last}
    (later : (physical c.upperPrior).1 ≤ last) (clean : ¬ (graph pp).Conflict last) :
    messageDigest (VerifierProbe.hashAt pp last) pp .top (UInt32.ofNat (bottomTree idx))
      (packBytes c.root)
      sig.top.randomizer = some (selectedDigest c.y) := by
  obtain ⟨_,_,_,_,actual,ext⟩ := c.upper
  exact read_trial (trial_of_find actual) (ext.trans later) clean

private theorem witnessed {pp : PublicParam} {α : Type} {p : OracleComp SharedSpec α} {s a t}
    (actual : (a,t) ∈ support ((simulateQ (graph pp).deferredImpl p).run s)) : ∃ xs,
      Logged pp p s a xs t := by
  rw [← loggingOracle.fst_map_run_simulateQ p, simulateQ_map, StateT.run_map, support_map] at actual
  obtain ⟨⟨⟨_, xs⟩, _⟩, ran, eq⟩ := actual
  cases eq
  exact ⟨xs, ran⟩

/-- Every returned bottom root occupies its cell, even if the upper search fails. -/
theorem Ran.bottom_root {pp q idx r s root out t}
    (actual : Ran q (carry (emitted emitStructure pp (bottomRootSchedule pp idx))) r s root out t)
    {last : SharedState} (later : (physical t.1).1 ≤ last) :
    last.2 (.inr (.inl (.bottom, LayerGraph.treeRole LAYER_HEIGHT (bottomTree idx)))) =
      some (digestEquiv root) := by
  have seen := actual.project
  rw [forget_carry] at seen
  obtain ⟨_, core⟩ := seen.lifted
  rw [deferredMixed, QueryImpl.simulateQ_compose,
    (root_structural pp .bottom LAYER_HEIGHT (bottomTree idx)).1] at core
  obtain ⟨_, run⟩ := witnessed (pp := pp) core
  exact later.2 (logged_root_value pp .bottom LAYER_HEIGHT (bottomTree idx) run)

/-- The root used by the upper registration is stored in the authentic shared bottom-tree cell. -/
theorem Receipt.bottom_root {pp q idx msg sig} (c : Receipt pp q idx msg sig) {last : SharedState}
    (later : (physical c.lowerPrior).1 ≤ last) :
    last.2 (.inr (.inl (.bottom, LayerGraph.treeRole LAYER_HEIGHT (bottomTree idx)))) =
      some (digestEquiv c.root) := by
  obtain ⟨_,_,_,t,actual,ext⟩ := c.tree
  exact actual.bottom_root (ext.trans later)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedGameProgram
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ClientRelease
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedStructure
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedCalls
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# Actual deferred disclosure traces of the mixed signer

Expanding the concrete mixed caller gives the original free graph program before any interpretation.

This equality therefore preserves its deferred trace as well as its eager distribution.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants OracleComp OracleSpec TwoLayerGraph Honest
open LayerGraph.Hidden

open CanonicalGraph.PairedQueries

@[expose] noncomputable def expandLocal {α : Type} (pp : PublicParam) (p : MixedLocal pp α) :
    WithLocal (ResidualCache pp) α := StateT.mk fun r =>
      simulateQ (expand PairedHashWord.halves) (p.run r)

private theorem pure_image {α : Type} (pp : PublicParam) (a : α) :
    expandLocal pp (pure a) = pure a := by ext r : 1; simp [expandLocal]

private theorem bind_image {α β : Type} (pp : PublicParam) (p : MixedLocal pp α)
    (f : α → MixedLocal pp β) :
    expandLocal pp (p >>= f) = expandLocal pp p >>= fun x => expandLocal pp (f x) := by
  ext r : 1
  simp only [expandLocal, StateT.run_mk, StateT.run_bind, simulateQ_bind]

private theorem lift_image {α : Type} (pp : PublicParam) (p : OracleComp MixedWorld α) :
    expandLocal pp (liftM p) = liftM (simulateQ (expand PairedHashWord.halves) p) := by
  ext s : 1
  simp [expandLocal, StateT.run_monadLift]

private theorem emitted_image {α : Type} (pp : PublicParam) {op : OracleComp SharedSpec α}
    (h : StructuralSchedule op) :
    expandLocal pp (emitted emitStructure pp op) = liftM op := by rw [emitted, lift_image, h.1]

private theorem rnd_image (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    expandLocal pp (mixedRandomizer pp l e msg) = graphPrf pp pp (addrRnd l e) msg := by
  ext r : 1
  exact expand_randomizer pp l e msg r

-- The digest and the randomizer have separately named 16-byte lengths.
set_option backward.isDefEq.respectTransparency false in
private theorem find_image (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    expandLocal pp (mixedFind pp l e msg) = (do
      let base ← randomizerBase pp (graphPrf pp) l e msg
      liftM (Xmss.Internal.findCodeword Honest.hash pp l e msg base 0 MAX_RANDOMIZER_TRIALS)) := by
  have image (base : Randomizer) :
      simulateQ (expand PairedHashWord.halves)
        (Xmss.Internal.findCodeword mixedHash pp l e msg base 0 MAX_RANDOMIZER_TRIALS) =
        Xmss.Internal.findCodeword Honest.hash pp l e msg base 0 MAX_RANDOMIZER_TRIALS := by
    rw [findCodeword_map_monad (simulateQ (expand PairedHashWord.halves)) (simulateQ_pure _)
      (simulateQ_bind _)]
    rw [expand_hash_fun]
  simp only [mixedFind, bind_image, lift_image, rnd_image, image, randomizerBase, bind_assoc,
    pure_bind]

private theorem ots_image (pp : PublicParam) (e : UInt32) (msg : ByteArray) :
    expandLocal pp (mixedOts emitStructure pp .top e msg) = localOts pp (graphPrf pp) .top e msg :=
      by
  unfold mixedOts localOts
  simp only [bind_image, find_image, bind_assoc]
  apply bind_congr
  intro b
  apply bind_congr
  rintro (_ | ⟨rho,x⟩)
  · apply pure_image
  · rw [bind_image, emitted_image]
    · simp only [pure_image]
    · rw [simulateQ_bind]
      exact bind_structural (beforeValues_structural pp .top e x) fun _ =>
        revealValues_structural pp .top e x

private theorem upper_image (pp : PublicParam) (e : Nat) (msg : ByteArray) :
    expandLocal pp (mixedTop emitStructure pp e msg) = localLayer pp (graphPrf pp) .top e msg := by
  unfold mixedTop localLayer
  rw [bind_image, ots_image]
  apply bind_congr
  rintro (_ | ⟨rho,ys⟩)
  · apply pure_image
  · simp only [bind_image, emitted_image pp (path_structural pp .top e), pure_image]

private theorem tree_image (pp : PublicParam) (idx : LeafIndex) :
    expandLocal pp (mixedTree emitStructure pp idx) = localTree pp (graphPrf pp) idx := by
  unfold mixedTree localTree
  rw [bind_image, emitted_image pp (root_structural pp .bottom _ _)]
  apply bind_congr
  intro root
  rw [bind_image, upper_image]
  apply bind_congr
  rintro (_ | top)
  · apply pure_image
  · simp only [bind_image, emitted_image pp (bottomPath_structural pp idx), pure_image]

/-- The deferred logger sees the same raw signature and shared graph queries. -/
theorem signature_image (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    expandLocal pp (mixedSignature emitStructure pp idx msg)
      = localReleased pp (graphPrf pp) idx msg := by
  unfold mixedSignature localReleased
  simp only [bind_image, find_image, bind_assoc]
  apply bind_congr
  intro base
  apply bind_congr
  rintro (_ | ⟨rho, x⟩)
  · apply pure_image
  · dsimp only
    rw [bind_image, emitted_image pp (beforeValues_structural pp .bottom _ x)]
    apply bind_congr
    intro _
    rw [bind_image, tree_image]
    apply bind_congr
    rintro (_ | top)
    · apply pure_image
    · simp only [bind_image, emitted_image pp (revealValues_structural pp .bottom _ x), pure_image]

/-- Each direct chain read belongs to the same successful raw signing entry. -/
theorem mixed_logged_cells (pp : PublicParam) (req : SignRequest) (r : ResidualCache pp)
    {s a out log t}
    (ran : Logged pp ((expandLocal pp (mixedSignature emitStructure pp req.leafIndex
      req.message)).run r)
      s (a,out) log t) : LogWithin (releasedCells pp t.1 [(req,a)]) log := by
  rw [signature_image] at ran
  exact logged_signer_cells pp req r ran

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

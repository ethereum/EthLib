module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SigningComponents
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SigningComponents
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedVerifierCut

/-!
# Authentic components of a successful signing request

The top layer signs the bottom root returned on that same invocation.

The lower digits and siblings are disclosed after the top signature succeeds.

Both layers' searches and all returned words remain identifiable in the final state.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleSpec OracleComp
  LayerGraph.Hidden
open ChainGraph (digestEquiv)

attribute [local irreducible] simulateQ graph mixedFind mixedTop mixedOts
  selection beforeValues revealValues Xmss.verifyWith

private theorem facts_tree (pp : PublicParam) (idx : LeafIndex) {r s path sig out t}
    (ran : MixedRun (deferredMixed pp) (mixedTree emitStructure pp idx) r s (.ok (path,
      sig)) out t) :
    r.2 ≤ out.2 ∧ ∃ root y,
      t.1.2 (.inr (.inl (.bottom,LayerGraph.treeRole LAYER_HEIGHT (bottomTree idx)))) =
        some (digestEquiv root) ∧ Stored (sibling .bottom idx.toNat) path t.1 ∧
      LayerFact pp .top (bottomTree idx) (packBytes root) sig y out t.1 := by
  unfold mixedTree at ran
  obtain ⟨root,mid,g,rootRun,afterRoot⟩ := ran.bind
  obtain ⟨upper,localTop,afterTop,top,tail⟩ := afterRoot.bind
  obtain ⟨preserved, actual⟩ := emitted_run (root_structural pp .bottom LAYER_HEIGHT
      (bottomTree idx)) rootRun
  obtain ⟨_,log⟩ := logged_of_run (pp := pp) actual
  have cell := logged_root_value pp .bottom LAYER_HEIGHT (bottomTree idx) log
  cases upper with
  | error err => have eq := tail.pure_result.1; cases eq
  | ok topSig =>
    obtain ⟨route,localPath,last,pathRun,done⟩ := tail.bind
    obtain ⟨eq,rfl,rfl⟩ := done.pure_result
    cases eq
    obtain ⟨unchanged,physical⟩ := emitted_run (bottomPath_structural pp idx) pathRun
    obtain ⟨grows,y,facts⟩ := facts_top pp (bottomTree idx) (packBytes root) top
    have endRows := le_of_eq (congrArg Prod.snd unchanged.symm)
    exact ⟨(le_of_eq (congrArg Prod.snd preserved.symm)).trans (grows.trans endRows),root,y,
      (top.public_mono.trans pathRun.public_mono).2 cell,bottom_rows pp idx physical,
      facts.mono endRows pathRun.public_mono⟩

/-- Every successful request identifies both WOTS+C words and all the digests it returned. -/
theorem signing_facts (pp : PublicParam) (req : SignRequest) {r s sig out t}
    (ran : MixedRun (deferredMixed pp) (mixedSignature emitStructure pp req.leafIndex req.message)
      r s (.ok sig) out t) : SignedFact pp req sig out t.1 := by
  unfold mixedSignature at ran
  obtain ⟨found,mid,g,finder,rest⟩ := ran.bind
  cases found with
  | none => have eq := rest.pure_result.1; cases eq
  | some pair =>
    obtain ⟨rho,x⟩ := pair
    obtain ⟨_,before,marked,touch,afterTouch⟩ := rest.bind
    obtain ⟨upper,localTree,g₂,tree,tail⟩ := afterTouch.bind
    obtain ⟨same,_⟩ := touch.lifted
    cases upper with
    | error err => have eq := tail.pure_result.1; cases eq
    | ok pair =>
      obtain ⟨path,top⟩ := pair
      obtain ⟨values,localEnd,last,read,done⟩ := tail.bind
      obtain ⟨eq,rfl,rfl⟩ := done.pure_result
      cases eq
      obtain ⟨unchanged,physical⟩ := emitted_run (revealValues_structural pp .bottom _ x) read
      obtain ⟨grows,root,y,cell,siblings,upper⟩ := facts_tree pp req.leafIndex tree
      have endRows := le_of_eq (congrArg Prod.snd unchanged.symm)
      have lower := (find_cut pp _ .bottom _ _ finder).fact
      have growth := (le_of_eq (congrArg Prod.snd same.symm)).trans (grows.trans endRows)
      exact ⟨rfl,root,x,y,read.public_mono.2 cell,
        ⟨lower.mono growth (touch.public_mono.trans (tree.public_mono.trans read.public_mono)),
        chain_rows pp .bottom _ x physical,siblings.mono read.public_mono⟩,
        upper.mono endRows read.public_mono⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SigningRows
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SigningSearchFact
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedStructure
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedVerifierCut

/-!
# Signing components on one completed mixed execution

The finder, chain values and siblings of each successful signature share the same final tables.

This also ties the top message to the bottom root actually read by the signer.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleSpec OracleComp
  LayerGraph.Hidden

/-- The returned randomizer, all selected chain values and the sibling vector use these exact rows.
-/
structure LayerFact (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature)
    (x : Vector (Fin CHAIN_LENGTH) V) (r : ResidualCache pp) (s : SharedState) : Prop where
  find : SearchFact pp l (UInt32.ofNat e) msg (some (sig.randomizer,x)) r s
  chains : Stored (chainAt l (UInt32.ofNat e) x) sig.chainValues s
  route : Stored (sibling l e) sig.path s

theorem LayerFact.mono {pp l e msg sig x r s r' s'} (h : LayerFact pp l e msg sig x r s)
    (privateRows : r.2 ≤ r'.2) (publicRows : s ≤ s') : LayerFact pp l e msg sig x r' s' :=
  ⟨h.find.mono privateRows publicRows, h.chains.mono publicRows, h.route.mono publicRows⟩

/--
Authentic components of this raw successful reply at the supplied later graph and private tables.
-/
@[expose] def SignedFact (pp : PublicParam) (req : SignRequest) (sig : Signature)
    (r : ResidualCache pp) (s : SharedState) : Prop :=
  sig.leafIndex = req.leafIndex ∧ ∃ root x y,
    s.2 (.inr (.inl (.bottom,LayerGraph.treeRole LAYER_HEIGHT (bottomTree req.leafIndex)))) =
      some (ChainGraph.digestEquiv root) ∧
    LayerFact pp .bottom req.leafIndex.toNat (packBytes req.message) sig.bottom x r s ∧
    LayerFact pp .top (bottomTree req.leafIndex) (packBytes root) sig.top y r s

theorem SignedFact.mono {pp req sig r s r' s'} (h : SignedFact pp req sig r s)
    (privateRows : r.2 ≤ r'.2) (publicRows : s ≤ s') : SignedFact pp req sig r' s' := by
  obtain ⟨idx,root,x,y,row,low,high⟩ := h
  exact ⟨idx,root,x,y,publicRows.2 row,low.mono privateRows publicRows,
      high.mono privateRows publicRows⟩

private theorem emitted_run {pp : PublicParam} {α : Type} {op : OracleComp SharedSpec α}
    (regular : StructuralSchedule op) {r s a out t} (run : MixedRun (deferredMixed pp)
      (emitted emitStructure pp op) r s a out t) :
    out = r ∧ (a,t) ∈ support ((simulateQ (graph pp).deferredImpl op).run s) := by
  obtain ⟨same, actual⟩ := run.lifted
  rw [deferredMixed, QueryImpl.simulateQ_compose, regular.1] at actual
  exact ⟨same,actual⟩

attribute [local irreducible] simulateQ graph Xmss.Internal.findCodeword mixedFind
  selection beforeValues revealValues graphPrf Xmss.verifyWith

private theorem facts_ots (pp : PublicParam) (e : UInt32) (msg : ByteArray) {rho ys r s out t}
    (ran : MixedRun (deferredMixed pp) (mixedOts emitStructure pp .top e msg) r s (some (rho,
      ys)) out t) :
    r.2 ≤ out.2 ∧ ∃ x, SearchFact pp .top e msg (some (rho,x)) out t.1 ∧
      Stored (chainAt .top e x) ys t.1 := by
  unfold mixedOts at ran
  obtain ⟨answer,mid,g,finder,tail⟩ := ran.bind
  cases answer with
  | none => have eq := tail.pure_result.1; cases eq
  | some pair =>
    obtain ⟨rng,x⟩ := pair
    obtain ⟨values,last,graph,read,done⟩ := tail.bind
    obtain ⟨eq, rfl, rfl⟩ := done.pure_result
    cases eq
    have regular : StructuralSchedule (simulateQ (selection pp .top).liftQuery
        (beforeValues pp .top e x >>= fun _ => revealValues e x)) := by
      rw [simulateQ_bind]
      exact bind_structural (beforeValues_structural pp .top e x) fun _ =>
        revealValues_structural pp .top e x
    obtain ⟨same, actual⟩ := emitted_run regular read
    obtain ⟨_, core⟩ := logged_of_run (pp := pp) actual
    rw [simulateQ_bind] at core
    obtain ⟨_,_,_,_,_, valuesRead,_⟩ := core.bind
    have grow : ExtendsPrivate (mixedFind pp .top e msg) := by
      unfold mixedFind
      exact ExtendsPrivate.bind (fun s _ h => mixedRandomizer_extends pp .top e msg s h)
        (fun _ => ExtendsPrivate.lift _)
    refine ⟨(finder.private_mono grow).trans (le_of_eq (congrArg Prod.snd same.symm)),
      x,?_,chain_rows pp .top e x valuesRead.raw⟩
    exact (find_cut pp _ .top e msg finder).fact.mono (le_of_eq
      (congrArg Prod.snd same.symm)) read.public_mono

private theorem facts_top (pp : PublicParam) (e : Nat) (msg : ByteArray) {r s sig out t}
    (ran : MixedRun (deferredMixed pp) (mixedTop emitStructure pp e msg) r s (.ok sig) out t) :
    r.2 ≤ out.2 ∧ ∃ x, LayerFact pp .top e msg sig x out t.1 := by
  unfold mixedTop at ran
  obtain ⟨answer,mid,g,ots,tail⟩ := ran.bind
  cases answer with
  | none => have eq := tail.pure_result.1; cases eq
  | some pair =>
    obtain ⟨rho,ys⟩ := pair
    obtain ⟨grows,x, search, chains⟩ := facts_ots pp _ msg ots
    obtain ⟨path,last,after,read,done⟩ := tail.bind
    obtain ⟨eq, rfl, rfl⟩ := done.pure_result
    cases eq
    obtain ⟨same, raw⟩ := emitted_run (path_structural pp .top e) read
    exact ⟨grows.trans (le_of_eq (congrArg Prod.snd same.symm)),x,
      search.mono (le_of_eq (congrArg Prod.snd same.symm)) read.public_mono,
      chains.mono read.public_mono,top_rows pp e raw⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

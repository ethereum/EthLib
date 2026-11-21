module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedCuts
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedRows
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderReceiptRows
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedStructure

/-!
# The two marked finder returns of one successful signing call

Each stop is retained alongside its registration.

All physical message words at the corresponding key agree at these two cuts.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open EthLib.Cryptography HashSig Constants OracleSpec OracleComp TwoLayerGraph Honest
open LayerGraph.Hidden

/-- Both returned searches and their registration states belong to the same signature. -/
structure Stops (pp : PublicParam) (q : Nat) (idx : LeafIndex) (msg : Message)
    (sig : Signature) (s t : State pp) where
  root : Digest
  x : Vector (Fin CHAIN_LENGTH) V
  y : Vector (Fin CHAIN_LENGTH) V
  low : Finish pp
  high : Finish pp
  lowerPrior : JointState
  upperPrior : JointState
  marks : t.2 = high :: low :: s.2
  lowerCall : (low.call.layer,low.call.epoch,low.call.msg) = (.bottom,
    UInt32.ofNat idx.toNat,packBytes msg)
  upperCall : (high.call.layer,high.call.epoch,high.call.msg) = (.top,
    UInt32.ofNat (bottomTree idx),packBytes root)
  lowerResult : low.result.1 = some (sig.bottom.randomizer,x)
  upperResult : high.result.1 = some (sig.top.randomizer,y)
  lowerFind : Ran q (find pp low.call.layer low.call.epoch low.call.msg)
    low.call.privateIn low.before low.result.1 low.result.2 low.after_
  upperFind : Ran q (find pp high.call.layer high.call.epoch high.call.msg)
    high.call.privateIn high.before high.result.1 high.result.2 high.after_
  lowerNote : Arrival.note (selectedNotice pp .bottom (UInt32.ofNat idx.toNat)
    (packBytes msg) sig.bottom.randomizer x) lowerPrior ∈ t.1.2
  upperNote : Arrival.note (selectedNotice pp .top (UInt32.ofNat (bottomTree idx))
    (packBytes root) sig.top.randomizer y) upperPrior ∈ t.1.2
  lowerRows : SameRows pp (.bottom,UInt32.ofNat idx.toNat) low.after_.1 lowerPrior
  upperRows : SameRows pp (.top,UInt32.ofNat (bottomTree idx)) high.after_.1 upperPrior
  rootRow : (FinderNotices.physical t.1.1).1.2 (.inr (.inl (.bottom,
    LayerGraph.treeRole LAYER_HEIGHT (bottomTree idx)))) =
    some (ChainGraph.digestEquiv root)

attribute [local irreducible] find mixedFind emitStructure beforeValues revealValues pathSchedule

/-- Read the two original returns, notes and keys from this same marked invocation. -/
theorem signing_stops {pp q idx msg r s sig out t}
    (ran : Done q (signing pp idx msg) r s (.ok sig) out t) :
    Nonempty (Stops pp q idx msg sig s t) := by
  unfold signing at ran
  obtain ⟨a,lowR,lowS,lower,rest⟩ := ran.bind
  rcases a with _ | ⟨rho,x⟩
  · cases rest.pure_result.1
  obtain ⟨_,_,_,chain,rest⟩ := rest.bind
  obtain ⟨root,atUpper,upperState,tree,rest⟩ := rest.bind
  obtain ⟨a,hiR,hiS,high,ret⟩ := rest.bind
  rcases a with _ | ⟨tau,y⟩
  · cases ret.pure_result.1
  obtain ⟨actual,lastMarks⟩ := ret.physical
  change Ran q (afterUpper pp idx (packBytes msg)
    (packBytes root) rho tau x y) hiR hiS.1 (.ok sig) out t.1 at actual
  have grew := actual.graph_mono
  unfold afterUpper at actual
  obtain ⟨tops,_,_,a,rest⟩ := actual.bind
  obtain ⟨auth,_,_,b,rest⟩ := rest.bind
  obtain ⟨path,_,_,c,rest⟩ := rest.bind
  obtain ⟨ys,_,g,d,rest⟩ := rest.bind
  obtain ⟨_,_,g',lo,rest⟩ := rest.bind
  obtain ⟨_,_,_,hi,ret⟩ := rest.bind
  obtain ⟨eq,_,finish⟩ := ret.pure_result
  obtain rfl := Except.ok.inj eq
  have structural : StructuralSchedule (simulateQ (selection pp .top).liftQuery
      (beforeValues pp .top (UInt32.ofNat (bottomTree idx)) y >>=
        fun _ => revealValues (UInt32.ofNat (bottomTree idx)) y)) := by
    rw [simulateQ_bind]
    exact bind_structural (beforeValues_structural ..) fun _ => revealValues_structural ..
  have frame (k : EarlierDigest.Key) : SameRows pp k hiS.1.1 g.1 :=
    (a.structural_rows k structural).trans ((b.structural_rows k (path_structural ..)).trans
      ((c.structural_rows k (bottomPath_structural ..)).trans (d.structural_rows k
        (revealValues_structural ..))))
  obtain ⟨cl,ml⟩ := lower.search
  obtain ⟨cu,mu⟩ := high.search
  obtain ⟨cc,mc⟩ := chain.physical
  obtain ⟨ct,mt⟩ := tree.physical
  let bot : Finish pp := ⟨⟨.bottom,UInt32.ofNat idx.toNat,packBytes msg,r⟩,s.1,
      (some (rho,x),lowR),lowS.1⟩
  let top : Finish pp := ⟨⟨.top,UInt32.ofNat (bottomTree idx),packBytes root,atUpper⟩,
      upperState.1,(some (tau,y),hiR),hiS.1⟩
  refine ⟨⟨root,x,y,bot,top,g.1,g'.1,?_,rfl,rfl,rfl,rfl,cl,cu,?_,?_,?_,?_,?_⟩⟩
  · rw [lastMarks,mu,mt,mc,ml]
  · rw [finish,hi.emitted,lo.emitted]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [finish,hi.emitted]
    exact List.mem_cons_self
  · exact (Ran.structural_rows cc _ (beforeValues_structural ..)).trans
      ((Ran.structural_rows ct _ (root_structural ..)).trans
        ((Ran.outside_rows cu (find_outside pp .top _ _ (.bottom,
          UInt32.ofNat idx.toNat) (by simp) _)).trans (frame _)))
  · exact (frame _).trans (lo.notice_rows _)
  · exact Ran.bottom_root ct ((Ran.graph_mono cu).trans grew)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

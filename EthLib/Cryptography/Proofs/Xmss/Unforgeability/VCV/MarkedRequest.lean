module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedSignature
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedProjection

/-!
# Which request produced a completed finder mark

A lower mark names the signed leaf and message.

An upper mark names the shared lower root, even when its finder exhausted its counter.

Only a fully successful response supplies a registration for its marks.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open EthLib.Cryptography HashSig Constants OracleSpec OracleComp TwoLayerGraph Honest
open LayerGraph.Hidden

/-- The address and message at a finder mark belong to the request that reached it. -/
@[expose] def Addressed {pp} (x : Finish pp) (idx : LeafIndex) (msg : Message)
    (g : SharedState) : Prop :=
  match x.call.layer with
  | .bottom => x.call.epoch = UInt32.ofNat idx.toNat ∧ x.call.msg = packBytes msg
  | .top => x.call.epoch = UInt32.ofNat (bottomTree idx) ∧ ∃ root : Digest,
    x.call.msg = packBytes root ∧
    g.2 (.inr (.inl (.bottom, LayerGraph.treeRole LAYER_HEIGHT (bottomTree idx)))) =
      some (ChainGraph.digestEquiv root)

/-- The actual successful invocation registered the returned vector at its own finder input. -/
@[expose] def RegisteredStop {pp} (x : Finish pp) (arrivals : List Arrival) : Prop :=
  ∃ rho y prior, x.result.1 = some (rho,y) ∧
    Arrival.note (selectedNotice pp x.call.layer x.call.epoch x.call.msg rho y) prior ∈ arrivals ∧
    SameRows pp (x.call.layer,x.call.epoch) x.after_.1 prior

/-- An upper failure carries its complete failed finder.

A lower selection can also precede that upper failure. -/
@[expose] def IssuedAt {pp} (x : Finish pp) (idx : LeafIndex) (msg : Message)
    (ans : Except XmssError Signature) (g : SharedState) (arrivals : List Arrival) : Prop :=
  Addressed x idx msg g ∧ match ans with
    | .error _ => x.call.layer = .bottom ∨ x.result.1 = none
    | .ok _ => RegisteredStop x arrivals

theorem IssuedAt.mono {pp} {x : Finish pp} {i m a g h xs ys} (fact : IssuedAt x i m a g xs)
    (rows : g ≤ h) (notes : xs ⊆ ys) : IssuedAt x i m a h ys := by
  obtain ⟨addr,auth⟩ := fact
  constructor
  · unfold Addressed at *
    cases l : x.call.layer <;> simp only [l] at addr ⊢
    · exact addr
    · obtain ⟨e,r,msg,lookup⟩ := addr
      exact ⟨e,r,msg,rows.2 lookup⟩
  · cases a with
    | error why => exact auth
    | ok sig =>
      obtain ⟨rho,y,p,sel,old,rows⟩ := auth
      exact ⟨rho,y,p,sel,notes old,rows⟩

private theorem issued_ok {pp q idx msg sig s t} (h : Stops pp q idx msg sig s t)
    (x : Finish pp) (mem : x ∈ t.2) (new : x ∉ s.2) :
    IssuedAt x idx msg (.ok sig) (FinderNotices.physical t.1.1).1 t.1.2 := by
  rw [h.marks,List.mem_cons,List.mem_cons] at mem
  rcases mem with rfl | rfl | old
  · obtain ⟨layer,rest⟩ := Prod.mk.inj h.upperCall
    obtain ⟨epoch,bytes⟩ := Prod.mk.inj rest
    constructor
    · simp only [Addressed,layer]
      exact ⟨epoch,h.root,bytes,h.rootRow⟩
    · refine ⟨_,_,h.upperPrior,h.upperResult,?_,?_⟩
      · simpa only [layer,epoch,bytes] using h.upperNote
      · simpa only [layer,epoch] using h.upperRows
  · obtain ⟨layer,rest⟩ := Prod.mk.inj h.lowerCall
    obtain ⟨epoch,bytes⟩ := Prod.mk.inj rest
    constructor
    · simpa only [Addressed,layer] using And.intro epoch bytes
    · refine ⟨_,_,h.lowerPrior,h.lowerResult,?_,?_⟩
      · simpa only [layer,epoch,bytes] using h.lowerNote
      · simpa only [layer,epoch] using h.lowerRows
  · exact (new old).elim

attribute [local irreducible] search find mixedFind emitStructure beforeValues revealValues
attribute [local irreducible] pathSchedule

/-- Every new mark of this invocation belongs to its actual request, including on either error. -/
theorem signing_issued {pp q idx msg r s ans out t}
    (ran : Done q (signing pp idx msg) r s ans out t) :
    ∀ x ∈ t.2, x ∉ s.2 → IssuedAt x idx msg ans (FinderNotices.physical t.1.1).1 t.1.2 := by
  cases ans with
  | ok sig =>
    obtain ⟨h⟩ := signing_stops ran
    exact issued_ok h
  | error why =>
    unfold signing at ran
    obtain ⟨a,_,_,lower,rest⟩ := ran.bind
    rcases a with _ | ⟨rho,y⟩
    · obtain ⟨_,_,rfl⟩ := rest.pure_result
      intro x mem new
      rw [lower.search.2,List.mem_cons] at mem
      rcases mem with rfl | old
      · exact ⟨⟨rfl,rfl⟩,Or.inl rfl⟩
      · exact (new old).elim
    · obtain ⟨_,_,_,chain,rest⟩ := rest.bind
      obtain ⟨root,_,_,tree,rest⟩ := rest.bind
      obtain ⟨b,_,_,upper,ret⟩ := rest.bind
      rcases b with _ | ⟨tau,z⟩
      · obtain ⟨_,_,rfl⟩ := ret.pure_result
        intro x mem new
        rw [upper.search.2,tree.physical.2,chain.physical.2,lower.search.2,
          List.mem_cons,List.mem_cons] at mem
        rcases mem with rfl | rfl | old
        · exact ⟨⟨rfl,root,rfl,Ran.bottom_root (idx := idx)
              (pp := pp) tree.physical.1 (Ran.graph_mono upper.search.1)⟩,Or.inr rfl⟩
        · exact ⟨⟨rfl,rfl⟩,Or.inl rfl⟩
        · exact (new old).elim
      · obtain ⟨actual,_⟩ := ret.physical
        change Ran q (afterUpper pp idx _ _ rho tau y z) _ _ (.error why) _ _ at actual
        unfold afterUpper at actual
        obtain ⟨_,_,_,_,tail⟩ := actual.bind
        obtain ⟨_,_,_,_,tail⟩ := tail.bind
        obtain ⟨_,_,_,_,tail⟩ := tail.bind
        obtain ⟨_,_,_,_,tail⟩ := tail.bind
        obtain ⟨_,_,_,_,tail⟩ := tail.bind
        obtain ⟨_,_,_,_,tail⟩ := tail.bind
        cases tail.pure_result.1

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

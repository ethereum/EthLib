module

public import EthLib.Cryptography.Proofs.Xmss.MapMonad
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerGraph
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphBuild
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphPath
public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential.EagerSubgraph

/-!
# Honest Merkle computations in the shared public graph

The leanXMSS draft, sections "WOTS+C" and "Trees", includes the layer in every address.
The two layers share the ordinary hash table while each path only draws labels of its own layer.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph

open Constants HashSig OracleComp OracleSpec Merkle
open ChainGraph (Word Public digestEquiv)
namespace Honest

/-- Embed the graph of one layer, retaining each ordered child and each physical input. -/
@[expose] def selection (pp : PublicParam) (l : Layer) : (LayerGraph.graph pp l).Subgraph (graph pp) where
  cell := ⟨inLayer l, by
    intro a b eq
    cases a with
    | inl x => cases b <;> simp_all [inLayer]
    | inr x =>
      cases b with
      | inl y => simp [inLayer] at eq
      | inr y => cases x <;> cases y <;> simp_all [inLayer]⟩
  node := Sum.map (fun r => (l, r)) (fun r => (l, r))
  node_cell k := by cases k <;> rfl
  children k := by cases k <;> rfl
  point k vs := by cases k <;> rfl

abbrev SharedSpec := Public.withLabels Start Row Word
abbrev SharedState := RelabelState Public Start Row Word

private theorem collect (pp : PublicParam) (l : Layer) {α : Type} (n : Nat)
    (f : Fin n → OracleComp LayerGraph.Spec α) (entries : ∀ i, (selection pp l).Preserves (f i)) :
    (selection pp l).Preserves (ofFnInOrder n f) := by
  let v := selection pp l
  induction n with
  | zero => exact v.preserves_pure _
  | succ n ih =>
    rw [ofFnInOrder]
    exact v.preserves_bind (entries 0) fun _ => v.preserves_bind
      (ih (fun i => f i.succ) (fun i => entries i.succ)) fun _ => v.preserves_pure _

private theorem start_calls (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec))
    (e : UInt32) : (selection pp l).Preserves (chainStarts pp (LayerGraph.startPrf pp l other) l e) := by
  let v := selection pp l
  simp only [chainStarts, LayerGraph.startPrf_pair]
  apply v.preserves_bind (collect pp l _ _ ?_) (fun _ => v.preserves_pure _)
  intro j
  unfold LayerGraph.readPair
  exact v.preserves_bind (v.preserves_readCell _) fun _ =>
    v.preserves_bind (v.preserves_readCell _) fun _ => v.preserves_pure _

private theorem step_calls (pp : PublicParam) (l : Layer) (e : UInt32) (i : Fin V)
    (j : Fin (CHAIN_LENGTH - 1)) (d : Digest) :
    (selection pp l).Preserves (chainStep LayerGraph.hash pp l e i j d) := by
  let v := selection pp l
  rw [LayerGraph.chainStep_eq]
  unfold Wots.GraphChain.publicStep
  exact v.preserves_bind (v.preserves_public _ _ rfl) fun _ =>
    v.preserves_bind (v.preserves_public _ _ rfl) fun _ => v.preserves_pure _

private theorem chain_calls (pp : PublicParam) (l : Layer) (e : UInt32) (i : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (d : Digest) :
    (selection pp l).Preserves (Xmss.chain LayerGraph.hash pp l e i start steps h d) := by
  let v := selection pp l
  unfold Xmss.chain
  induction steps with
  | zero => exact v.preserves_pure _
  | succ n ih =>
    rw [Wots.chain]
    exact v.preserves_bind (ih (by omega)) (step_calls pp l e i _)

private theorem th_calls (pp : PublicParam) (l : Layer) (r : LayerGraph.Role)
    (vs : List Word) (width : vs.length = LayerGraph.arity r) (a : Address) (d : ByteArray)
    (raw : LayerGraph.input pp l r vs = (thInput pp a d).data.toList) :
    (selection pp l).Preserves (th LayerGraph.hash pp a d) := by
  let v := selection pp l
  unfold th
  rw [LayerGraph.hash_eq, ← raw]
  apply v.preserves_bind
  · apply v.preserves_bind (v.preserves_public (.inl r) vs (width.trans (LayerGraph.length_children r).symm))
    exact fun _ => v.preserves_bind
      (v.preserves_public (.inr r) vs (width.trans (LayerGraph.length_children r).symm)) fun _ => v.preserves_pure _
  · exact fun _ => v.preserves_pure _

theorem leaf_calls (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec))
    (e : UInt32) : (selection pp l).Preserves
      (otsPublicLeaf LayerGraph.hash pp (LayerGraph.startPrf pp l other) l e) := by
  let v := selection pp l
  unfold otsPublicLeaf
  apply v.preserves_bind (start_calls pp l other e)
  intro starts
  apply v.preserves_bind (collect pp l _ _ (fun i => chain_calls pp l e i _ _ _ _))
  intro ends
  apply th_calls pp l (.leaf e) (LayerGraph.endWords ends) (by simp [LayerGraph.endWords, LayerGraph.arity])
  change (thInput pp _ (packDigests (LeafGraph.digests V (LayerGraph.endWords ends)))).data.toList = _
  rw [LayerGraph.endWords_digests]
  rfl

private theorem node_hash_calls (pp : PublicParam) (l : Layer) (h j : Nat) (valid : h < LAYER_HEIGHT)
    (a b : Digest) : (selection pp l).Preserves (nodeHash LayerGraph.hash pp l ⟨h+1,j⟩ a b) := by
  apply th_calls pp l (LayerGraph.treeRole (h+1) j) [digestEquiv a, digestEquiv b]
    (by simp [LayerGraph.treeRole_succ _ _ valid, LayerGraph.arity])
  exact LayerGraph.node_input pp l h j valid a b

theorem build_calls (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec))
    (h j : Nat) (bound : h ≤ LAYER_HEIGHT) : (selection pp l).Preserves
      (Xmss.build LayerGraph.hash pp (LayerGraph.startPrf pp l other) l h j) := by
  let v := selection pp l
  induction h generalizing j with
  | zero =>
    rw [Xmss.build, build_zero]
    exact v.preserves_bind (leaf_calls pp l other _) fun _ => v.preserves_pure _
  | succ h ih =>
    rw [Xmss.build, build_succ]
    exact v.preserves_bind (ih _ (by omega)) fun a => v.preserves_bind (ih _ (by omega)) fun b =>
      v.preserves_bind (node_hash_calls pp l h j (by omega) a.value b.value) fun _ => v.preserves_pure _

theorem node_calls (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec))
    (h j : Nat) (bound : h ≤ LAYER_HEIGHT) : (selection pp l).Preserves
      (Xmss.node LayerGraph.hash pp (LayerGraph.startPrf pp l other) l h j) := by
  unfold Xmss.node
  rw [← value_build]
  exact (selection pp l).preserves_map Built.value (build_calls pp l other h j bound)

private theorem path_calls_at (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec))
    (height e : Nat) (bound : height ≤ LAYER_HEIGHT) : (selection pp l).Preserves
      (Merkle.path (nodeHash LayerGraph.hash pp l) (leaves LayerGraph.hash pp (LayerGraph.startPrf pp l other) l)
        height e) := by
  rw [Merkle.path, LayerGraph.siblings_in_order]
  simp only [Nat.zero_add]
  exact collect pp l height _ (fun k => node_calls pp l other k.val _ ((Nat.le_of_lt k.isLt).trans bound))

theorem path_calls (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec))
    (e : Nat) : (selection pp l).Preserves (Xmss.path LayerGraph.hash pp (LayerGraph.startPrf pp l other) l e) :=
  path_calls_at pp l other LAYER_HEIGHT e le_rfl

/-- Both tagged public rows have the original physical hash input. -/
@[expose] noncomputable def hash (pp : PublicParam) (l : Layer) (bytes : ByteArray) : OracleComp SharedSpec (Vector UInt8 32) :=
  simulateQ (selection pp l).liftQuery (LayerGraph.hash bytes)

/-- Each original private start-pair call reads the two start labels in its own layer. -/
@[expose] noncomputable def prf (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec)) :
    SeedPrf (OracleComp SharedSpec) := fun p a d =>
  simulateQ (selection pp l).liftQuery (LayerGraph.startPrf pp l other p a d)

/-- The shared run satisfies the selected layer's cache condition and retains every unselected cell. -/
@[expose] def Records {α : Type} (pp : PublicParam) (l : Layer) (op : OracleComp SharedSpec α)
    (post : α → LayerGraph.State → Prop) : Prop :=
  ∀ (s : SharedState) (z : α × SharedState),
    z ∈ support ((simulateQ (graph pp).eagerImpl op).run s) →
      post z.1 ((selection pp l).project z.2) ∧ (selection pp l).Framed s z.2

private theorem transfer {α : Type} (pp : PublicParam) (l : Layer) (p : OracleComp LayerGraph.Spec α)
    (post : α → LayerGraph.State → Prop) (calls : (selection pp l).Preserves p)
    (localPost : ∀ (s : LayerGraph.State) (z : α × LayerGraph.State),
      z ∈ support ((simulateQ (LayerGraph.graph pp l).eagerImpl p).run s) → post z.1 z.2) :
    Records pp l (simulateQ (selection pp l).liftQuery p) post := by
  intro s z hz
  obtain ⟨supported, frame⟩ := calls s z hz
  exact ⟨localPost _ _ supported, frame⟩

/-- Every path of the actual built tree is recorded in the shared graph. -/
theorem build_recorded (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec))
    (h j : Nat) (bound : h ≤ LAYER_HEIGHT) : Records pp l
      (Xmss.build (hash pp l) pp (prf pp l other) l h j) (LayerGraph.BuildRecorded h j) := by
  let v := selection pp l
  have eqn := Xmss.build_map_monad (fun {_} p => simulateQ v.liftQuery p)
    (simulateQ_pure _) (simulateQ_bind _) LayerGraph.hash (LayerGraph.startPrf pp l other) pp l h j
  rw [show Xmss.build (hash pp l) pp (prf pp l other) l h j = _ from eqn.symm]
  exact transfer pp l _ _ (build_calls pp l other h j bound) (LayerGraph.build_recorded pp l other h j bound)

private theorem lifted_path (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec))
    (n e : Nat) (bound : n ≤ LAYER_HEIGHT) : Records pp l
      (simulateQ (selection pp l).liftQuery (Merkle.path (nodeHash LayerGraph.hash pp l)
        (leaves LayerGraph.hash pp (LayerGraph.startPrf pp l other) l) n e))
      (fun path st => ∀ k : Fin n, LayerGraph.Recorded
        (LayerGraph.treeRole k.val ((e / 2 ^ k.val) ^^^ 1)) path[k] st) :=
  transfer pp l _ _ (path_calls_at pp l other n e bound) (LayerGraph.siblings_recorded pp l other n e bound)

/-- Each height of the original path reads its true sibling in the one graph shared by both layers. -/
theorem path_recorded (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec))
    (e : Nat) : Records pp l (Xmss.path (hash pp l) pp (prf pp l other) l e)
    (fun path st => ∀ k : Fin LAYER_HEIGHT, LayerGraph.Recorded
      (LayerGraph.treeRole k.val ((e / 2 ^ k.val) ^^^ 1)) path[k] st) := by
  let v := selection pp l
  have eqn := Xmss.path_map_monad (fun {_} p => simulateQ v.liftQuery p)
    (simulateQ_pure _) (simulateQ_bind _) LayerGraph.hash (LayerGraph.startPrf pp l other) pp l e
  rw [show Xmss.path (hash pp l) pp (prf pp l other) l e = _ from eqn.symm]
  exact lifted_path pp l other LAYER_HEIGHT e le_rfl

end Honest
end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph

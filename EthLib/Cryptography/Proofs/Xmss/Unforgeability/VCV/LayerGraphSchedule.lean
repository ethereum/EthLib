module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphLeaf

/-!
# The private operations inside an honest Merkle leaf

The leanXMSS draft, section "WOTS+C", publishes the hash of the completed chains.

The start words and the intermediate digits reach the hash without being disclosed.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

open Constants HashSig OracleSpec OracleComp Wots
open ChainGraph (Word digestEquiv indexAt)

namespace Hidden

/-- Visit every entry in the order used by the scheme. -/
def visit : (n : Nat) → (Fin n → OracleComp Spec Unit) → OracleComp Spec Unit
  | 0, _ => pure ()
  | n + 1, f => f 0 >>= fun _ => visit n fun i => f i.succ

private theorem bind_forget {α β : Type} {p : ProbComp (α × State)} {t : ProbComp (Unit × State)}
    (eqn : (fun z => ((), z.2)) <$> p = t) (k : State → ProbComp β) :
    (p >>= fun z => k z.2) = (t >>= fun z => k z.2) := by
  rw [← eqn, bind_map_left]

private theorem forget_collect (pp : PublicParam) (layer : Layer) {α : Type}
    (n : Nat) (f : Fin n → OracleComp Spec α) (g : Fin n → OracleComp Spec Unit)
    (s : State) (entries : ∀ i t, s ≤ t →
      (fun z => ((), z.2)) <$> (simulateQ (graph pp layer).eagerImpl (f i)).run t =
        (simulateQ (graph pp layer).eagerImpl (g i)).run t) :
    (fun z => ((), z.2)) <$> (simulateQ (graph pp layer).eagerImpl (ofFnInOrder n f)).run s =
      (simulateQ (graph pp layer).eagerImpl (visit n g)).run s := by
  induction n generalizing s with
  | zero => simp [visit, ofFnInOrder]
  | succ n ih =>
    simp only [visit, ofFnInOrder, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, map_bind, map_pure]
    rw [← bind_forget (entries 0 s le_rfl)]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro head hhead
    have ext := state_extends pp layer (f 0) s hhead
    simpa only [← bind_pure_comp] using ih (fun i => f i.succ) (fun i => g i.succ) head.2
      (fun i t ht => entries i.succ t (ext.trans ht))

/-- Both halves of a private word are scheduled in their original order. -/
def startPair (e : UInt32) (j : Fin (V / 2)) : OracleComp Spec Unit := do
  touchCell (some (.inl (e, indexAt j 0)))
  touchCell (some (.inl (e, indexAt j 1)))

private theorem starts (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec))
    (e : UInt32) (s : State) :
    (fun z => ((), z.2)) <$> (simulateQ (graph pp layer).eagerImpl
      (chainStarts pp (startPrf pp layer other) layer e)).run s =
      (simulateQ (graph pp layer).eagerImpl (visit (V / 2) (startPair e))).run s := by
  simp only [chainStarts, startPrf_pair, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, map_bind, map_pure]
  rw [bind_pure_comp]
  apply forget_collect pp layer
  intro j st _
  simp only [readPair, startPair, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, CanonicalGraph.simulateQ_eagerImpl_touchCell, ← bind_pure_comp,
    bind_assoc, pure_bind]

/-- Each physical chain hash schedules its two reply cells. -/
def chainEdges (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V) :
    OracleComp Spec Unit :=
  Wots.chain (GraphChain.touchStep (schedule pp layer e i)) 0 (CHAIN_LENGTH - 1) (by decide) ()

private theorem chains (pp : PublicParam) (layer : Layer) (e : UInt32) (starts : Vector Digest V)
    (s : State) (ready : ∀ i : Fin V, s.2 (.inl (e, i)) = some (digestEquiv starts[i])) :
    (fun z => ((), z.2)) <$> (simulateQ (graph pp layer).eagerImpl (ofFnInOrder V fun i =>
      Xmss.chain hash pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) starts[i])).run s =
      (simulateQ (graph pp layer).eagerImpl (visit V (chainEdges pp layer e))).run s := by
  apply forget_collect pp layer
  intro i t old
  exact GraphChain.chain_touches_run (schedule pp layer e i) digestEquiv
    (chainStep hash pp layer e i)
    (fun j v => congrArg (simulateQ (graph pp layer).eagerImpl) (chainStep_eq pp layer e i j v))
    0 (CHAIN_LENGTH - 1) (by decide) starts[i] t (old.2 (ready i))

/-- The private start words and the edges of an undisclosed one-time key are only touched. -/
def beforeLeaf (pp : PublicParam) (layer : Layer) (e : UInt32) : OracleComp Spec Unit := do
  visit (V / 2) (startPair e)
  visit V (chainEdges pp layer e)

private theorem fusion {α β γ : Type} (pp : PublicParam) (layer : Layer)
    (first : OracleComp Spec α) (first' : OracleComp Spec Unit)
    (body : α → OracleComp Spec β) (body' : OracleComp Spec Unit)
    (last : β → OracleComp Spec γ) (last' : OracleComp Spec γ)
    (dropFirst : ∀ s, (fun z => ((), z.2)) <$> (simulateQ (graph pp layer).eagerImpl first).run s =
      (simulateQ (graph pp layer).eagerImpl first').run s)
    (dropBody : ∀ s a, a ∈ support ((simulateQ (graph pp layer).eagerImpl first).run s) →
      (fun z => ((), z.2)) <$> (simulateQ (graph pp layer).eagerImpl (body a.1)).run a.2 =
        (simulateQ (graph pp layer).eagerImpl body').run a.2)
    (replaceLast : ∀ s a, a ∈ support ((simulateQ (graph pp layer).eagerImpl first).run s) →
      ∀ b, b ∈ support ((simulateQ (graph pp layer).eagerImpl (body a.1)).run a.2) →
        (simulateQ (graph pp layer).eagerImpl (last b.1)).run b.2 =
          (simulateQ (graph pp layer).eagerImpl last').run b.2) :
    simulateQ (graph pp layer).eagerImpl (first >>= fun a => body a >>= last) =
      simulateQ (graph pp layer).eagerImpl ((first' >>= fun _ => body') >>= fun _ => last') := by
  ext s : 1
  simp only [bind_assoc, simulateQ_bind, StateT.run_bind]
  rw [← dropFirst s, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro z hz
  rw [← dropBody s z hz, bind_map_left]
  exact OracleComp.bind_congr_of_forall_mem_support _ (replaceLast s z hz)

attribute [local irreducible] chainStarts ofFnInOrder Xmss.chain visit

/-- The actual one-time leaf can hide all 58 starts and every chain value.

Only the leaf's low digest is read, and the complete eager cache is retained. -/
theorem leaf (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec))
    (e : UInt32) :
    simulateQ (graph pp layer).eagerImpl (otsPublicLeaf hash pp (startPrf pp layer other) layer e) =
      simulateQ (graph pp layer).eagerImpl
        (beforeLeaf pp layer e >>= fun _ => readOutput (.leaf e)) := by
  apply fusion pp layer (chainStarts pp (startPrf pp layer other) layer e)
    (visit (V / 2) (startPair e)) (fun xs => ofFnInOrder V fun i =>
      Xmss.chain hash pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) xs[i])
    (visit V (chainEdges pp layer e)) (otsLeafHash hash pp layer e) (readOutput (.leaf e))
    (starts pp layer other e)
  · exact fun s a ha => chains pp layer e a.1 a.2 (starts_stored pp layer other e s (z := a) ha)
  intro s start runStart endValues runChains
  have ready := starts_stored pp layer other e s (z := start) runStart
  apply leafHash_of_recorded
  exact collect_recorded pp layer V
    (fun i => Xmss.chain hash pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) start.1[i])
    (fun i d t => Recorded (.chain e i ⟨CHAIN_LENGTH - 2, by decide⟩) d t) start.2
    (fun _ _ _ _ ext old => ext.2 old)
    (fun i t ext _ ran => chain_end_recorded pp layer e i _ t (ext.2 (ready i)) ran) runChains

/-- The two outputs of an internal role are both touched when its digest stays private. -/
def touchOutput (r : Role) : OracleComp Spec Unit := do
  touchCell (some (.inr (.inl r)))
  touchCell (some (.inr (.inr r)))

private theorem forget_output (pp : PublicParam) (layer : Layer) (r : Role) (s : State) :
    (fun z => ((), z.2)) <$> (simulateQ (graph pp layer).eagerImpl (readOutput r)).run s =
      (simulateQ (graph pp layer).eagerImpl (touchOutput r)).run s := by
  simp only [readOutput, touchOutput, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, CanonicalGraph.simulateQ_eagerImpl_touchCell, ← bind_pure_comp,
    bind_assoc, pure_bind]

/-- Traverse both full subtrees, postponing the current node's two outputs.

Every operation in this traversal is a touch. -/
def beforeNode (pp : PublicParam) (layer : Layer) : Nat → Nat → OracleComp Spec Unit
  | 0, j => beforeLeaf pp layer (UInt32.ofNat j)
  | h + 1, j => do
    beforeNode pp layer h (2*j)
    touchOutput (treeRole h (2*j))
    beforeNode pp layer h (2*j+1)
    touchOutput (treeRole h (2*j+1))

private theorem tree (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec)) :
    ∀ h j, simulateQ (graph pp layer).eagerImpl
        (normalizedNode (leaves hash pp (startPrf pp layer other) layer) h j) =
      simulateQ (graph pp layer).eagerImpl
        (beforeNode pp layer h j >>= fun _ => readOutput (treeRole h j)) := by
  intro h
  induction h with
  | zero =>
    intro j
    exact leaf pp layer other (UInt32.ofNat j)
  | succ h ih =>
    intro j
    have left := ih (2*j)
    have right := ih (2*j+1)
    simp only [normalizedNode, Merkle.node] at left right ⊢
    simp only [Merkle.node.go, simulateQ_bind, beforeNode, bind_assoc]
    rw [left, right]
    ext s : 1
    simp only [StateT.run_bind, simulateQ_bind]
    simp only [bind_assoc]
    apply bind_congr
    intro leftState
    rw [← forget_output pp layer (treeRole h (2*j)) leftState.2, bind_map_left]
    apply bind_congr
    intro leftRead
    apply bind_congr
    intro rightState
    rw [← forget_output pp layer (treeRole h (2*j+1)) rightState.2, bind_map_left]

/-- The specification reads its returned root and touches every hidden cell. -/
theorem node (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec))
    (h j : Nat) (bound : h ≤ LAYER_HEIGHT) :
    simulateQ (graph pp layer).eagerImpl (Xmss.node hash pp (startPrf pp layer other) layer h j) =
      simulateQ (graph pp layer).eagerImpl
        (beforeNode pp layer h j >>= fun _ => readOutput (treeRole h j)) :=
  (node_settles pp layer other h j bound).1.trans (tree pp layer other h j)

end Hidden
end EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

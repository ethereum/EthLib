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

private theorem collect_cached {α : Type} (pp : PublicParam) (l : Layer) (s : State)
    (n : Nat) (f : Fin n → OracleComp Spec α) (v : Fin n → Id α)
    (entries : ∀ i, (simulateQ (graph pp l).eagerImpl (f i)).run s = pure ((v i).run, s)) :
    (simulateQ (graph pp l).eagerImpl (ofFnInOrder n f)).run s =
      pure ((ofFnInOrder n v).run, s) := by
  induction n with
  | zero => simp [ofFnInOrder]
  | succ n ih =>
    simp only [ofFnInOrder, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      entries 0, pure_bind, Id.run_bind, Id.run_pure]
    rw [ih (fun i => f i.succ) (fun i => v i.succ) (fun i => entries i.succ), pure_bind]

theorem bounded_digit (d : Fin CHAIN_LENGTH) : 0 + d.val ≤ CHAIN_LENGTH - 1 := by
  have limit := d.isLt
  omega

/-- Touch the private start pairs and both halves of each selected chain prefix. -/
def beforeValues (pp : PublicParam) (l : Layer) (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V) :
    OracleComp Spec Unit := do
  visit (V / 2) (startPair e)
  visit V fun i => Wots.chain (GraphChain.touchStep (schedule pp l e i))
    0 (x[i]).val (bounded_digit x[i]) ()

/-- Reading a signature exposes each chain only at its chosen digit, in its original order. -/
noncomputable def revealValues (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V) :
    OracleComp Spec (Vector Digest V) :=
  ofFnInOrder V fun i => digestEquiv.symm <$> readCell (some (position e i (x[i]).val))

/-- Reading stored digests in order returns their vector and preserves the state. -/
theorem read_cached (pp : PublicParam) (l : Layer) {n : Nat} (cells : Fin n → Cell)
    (ys : Vector Digest n) (s : State)
    (ready : ∀ i : Fin n, s.2 (cells i) = some (digestEquiv ys[i])) :
    (simulateQ (graph pp l).eagerImpl
      (ofFnInOrder n fun i => digestEquiv.symm <$> readCell (some (cells i)))).run s =
      pure (ys, s) := by
  have law := collect_cached pp l s n
    (fun i => digestEquiv.symm <$> readCell (some (cells i)))
    (fun i => (ys[i] : Id Digest)) (fun i => by
      rw [simulateQ_map, StateT.run_map, CanonicalGraph.eagerImpl_readCell_run,
        RelabelState.drawCell_run_of_cell_eq_some (ready i)]
      simp [Id.run])
  have same : (ofFnInOrder (m := Id) n (fun i : Fin n => ys[i])).run = ys := by
    rw [HashSig.ofFnInOrder_run]
    apply Vector.ext
    intro j hj
    simp [Id.run]
  rw [same] at law
  exact law

theorem reveal_cached (pp : PublicParam) (l : Layer) (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V)
    (ys : Vector Digest V) (s : State)
    (ready : ∀ i : Fin V, s.2 (position e i (x[i]).val) = some (digestEquiv ys[i])) :
    (simulateQ (graph pp l).eagerImpl (revealValues e x)).run s = pure (ys, s) :=
  read_cached pp l _ ys s ready

private def walkDigits (pp : PublicParam) (l : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) (ys : Vector Digest V) :=
  ofFnInOrder V fun i => Xmss.chain hash pp l e i 0 (x[i]).val (by simp) ys[i]

private def markDigits (pp : PublicParam) (l : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) :=
  visit V fun i => Wots.chain (GraphChain.touchStep (schedule pp l e i))
    0 (x[i]).val (bounded_digit x[i]) ()

private theorem walk_drops (pp : PublicParam) (l : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) (ys : Vector Digest V) (s : State)
    (ready : ∀ i : Fin V, s.2 (.inl (e, i)) = some (digestEquiv ys[i])) :
    (fun z => ((), z.2)) <$> (simulateQ (graph pp l).eagerImpl (walkDigits pp l e x ys)).run s =
      (simulateQ (graph pp l).eagerImpl (markDigits pp l e x)).run s := by
  apply forget_collect pp l
  intro i t ext
  unfold Xmss.chain
  exact GraphChain.chain_touches_run (schedule pp l e i) digestEquiv
    (chainStep hash pp l e i) (fun j d => congrArg (simulateQ (graph pp l).eagerImpl)
      (chainStep_eq pp l e i j d)) 0 (x[i]).val (bounded_digit x[i]) ys[i] t (ext.2 (ready i))

private theorem walk_stores (pp : PublicParam) (l : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) (ys : Vector Digest V) (s : State)
    (ready : ∀ i : Fin V, s.2 (.inl (e, i)) = some (digestEquiv ys[i])) {z}
    (ran : z ∈ support ((simulateQ (graph pp l).eagerImpl (walkDigits pp l e x ys)).run s)) :
    ∀ i : Fin V, z.2.2 (position e i (x[i]).val) = some (digestEquiv z.1[i]) := by
  apply collect_recorded pp l V _ (fun i d t => t.2 (position e i (x[i]).val) =
    some (digestEquiv d)) s (fun _ _ _ _ ext old => ext.2 old) _ ran
  intro i t ext w hw
  unfold Xmss.chain at hw
  have stored := GraphChain.chain_records_result (schedule pp l e i) digestEquiv
    (chainStep hash pp l e i) (fun j d => congrArg (simulateQ (graph pp l).eagerImpl)
      (chainStep_eq pp l e i j d)) 0 (x[i]).val (bounded_digit x[i]) ys[i] t (ext.2 (ready i)) hw
  change w.2.2 (position e i (0 + (x[i]).val)) = some (digestEquiv w.1) at stored
  rw [Nat.zero_add] at stored
  exact stored

/-- After a successful trial, all touches can precede every disclosed chain read.

The original eager output and both caches are preserved even when a chosen digit is zero. -/
theorem values (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp Spec))
    (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V) :
    simulateQ (graph pp l).eagerImpl (do
      let xs ← chainStarts pp (startPrf pp l other) l e
      ofFnInOrder V fun i => Xmss.chain hash pp l e i 0 (x[i]).val (by simp) xs[i]) =
    simulateQ (graph pp l).eagerImpl (beforeValues pp l e x >>= fun _ => revealValues e x) := by
  have eqn := fusion pp l (chainStarts pp (startPrf pp l other) l e)
    (visit (V / 2) (startPair e)) (walkDigits pp l e x) (markDigits pp l e x)
    (fun ys => pure ys) (revealValues e x) (starts pp l other e) ?_ ?_
  · simpa only [walkDigits, markDigits, beforeValues, bind_pure] using eqn
  · exact fun s a ha => walk_drops pp l e x a.1 a.2 (starts_stored pp l other e s (z := a) ha)
  · intro s a ha b hb
    rw [simulateQ_pure, StateT.run_pure]
    exact (reveal_cached pp l e x b.1 b.2
      (walk_stores pp l e x a.1 a.2 (starts_stored pp l other e s (z := a) ha) hb)).symm

private theorem hidden_pair {α β : Type} (head : ProbComp (α × State))
    (blank : ProbComp (Unit × State))
    (body : α → State → ProbComp (β × State)) (touch : State → ProbComp (Unit × State))
    (post : β → State → Prop) (first : (fun z => ((), z.2)) <$> head = blank)
    (second : ∀ a ∈ support head, (fun z => ((), z.2)) <$> body a.1 a.2 = touch a.2)
    (record : ∀ a ∈ support head, ∀ b ∈ support (body a.1 a.2), post b.1 b.2)
    (final : State) (ran : ((), final) ∈ support (blank >>= fun z => touch z.2)) :
    ∃ b, post b final := by
  rw [← first, bind_map_left, mem_support_bind_iff] at ran
  obtain ⟨a, ha, tail⟩ := ran
  rw [← second a ha, support_map] at tail
  obtain ⟨⟨b, last⟩, hb, same⟩ := tail
  have eqn : last = final := congrArg Prod.snd same
  exact ⟨b, eqn ▸ record a ha (b, last) hb⟩

private theorem marked_stores {α β : Type} (pp : PublicParam) (l : Layer)
    (head : OracleComp Spec α) (blank : OracleComp Spec Unit) (body : α → OracleComp Spec β)
    (touch : OracleComp Spec Unit) (post : β → State → Prop)
    (first : ∀ s, (fun z => ((), z.2)) <$> (simulateQ (graph pp l).eagerImpl head).run s =
      (simulateQ (graph pp l).eagerImpl blank).run s)
    (second : ∀ s a, a ∈ support ((simulateQ (graph pp l).eagerImpl head).run s) →
      (fun z => ((), z.2)) <$> (simulateQ (graph pp l).eagerImpl (body a.1)).run a.2 =
        (simulateQ (graph pp l).eagerImpl touch).run a.2)
    (store : ∀ s a, a ∈ support ((simulateQ (graph pp l).eagerImpl head).run s) →
      ∀ b, b ∈ support ((simulateQ (graph pp l).eagerImpl (body a.1)).run a.2) → post b.1 b.2)
    (s t : State) (ran : ((), t) ∈ support ((simulateQ (graph pp l).eagerImpl
      (blank >>= fun _ => touch)).run s)) : ∃ b, post b t := by
  let G := graph pp l
  simp only [simulateQ_bind, StateT.run_bind] at ran
  exact hidden_pair _ _ (fun a st => (simulateQ G.eagerImpl (body a)).run st)
    (fun st => (simulateQ G.eagerImpl touch).run st) post (first s) (second s) (store s) t ran

/-- After the touch-only signing prefix, every selected value is already stored. -/
theorem beforeValues_stored (pp : PublicParam) (l : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) (initial final : State)
    (ran : ((), final) ∈ support ((simulateQ (graph pp l).eagerImpl
      (beforeValues pp l e x)).run initial)) :
    ∃ ys : Vector Digest V, ∀ i : Fin V, final.2 (position e i (x[i]).val) =
      some (digestEquiv ys[i]) := by
  let aux : SeedPrf (OracleComp Spec) := fun _ _ _ => pure (Vector.replicate 32 0)
  apply marked_stores pp l (chainStarts pp (startPrf pp l aux) l e) (visit (V / 2) (startPair e))
    (walkDigits pp l e x) (markDigits pp l e x)
    (fun (ys : Vector Digest V) (t : State) => ∀ i : Fin V,
      t.2 (position e i (x[i]).val) = some (digestEquiv ys[i])) (starts pp l aux e) _ _
      initial final ran
  · exact fun s a ha => walk_drops pp l e x a.1 a.2 (starts_stored pp l aux e s (z := a) ha)
  · exact fun s a ha b hb => walk_stores pp l e x a.1 a.2
      (starts_stored pp l aux e s (z := a) ha) hb

/-- The actual finder controls entry into the chain schedule.

A failed finder returns immediately and touches no chain starts. -/
noncomputable def sign (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp Spec))
    (e : UInt32) (msg : ByteArray) : OracleComp Spec (Option (Randomizer × Vector Digest V)) := do
  let base ← randomizerBase pp (startPrf pp l other) l e msg
  let some (rho, x) ← Xmss.Internal.findCodeword hash pp l e msg base 0 MAX_RANDOMIZER_TRIALS
    | return none
  beforeValues pp l e x
  let ys ← revealValues e x
  return some (rho, ys)

attribute [local irreducible] Xmss.Internal.findCodeword

/-- The actual one-time signer and the schedule give the same result and complete eager state. -/
theorem ots (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp Spec))
    (e : UInt32) (msg : ByteArray) :
    simulateQ (graph pp l).eagerImpl (otsSign hash pp (startPrf pp l other) l e msg) =
      simulateQ (graph pp l).eagerImpl (sign pp l other e msg) := by
  unfold otsSign sign
  simp only [simulateQ_bind]
  apply bind_congr
  intro base
  apply bind_congr
  rintro (_ | ⟨rho, x⟩)
  · rfl
  · have complete := congrArg
      (fun p : StateT State ProbComp (Vector Digest V) =>
        p >>= fun ys => pure (some (rho, ys))) (values pp l other e x)
    simpa only [simulateQ_bind, simulateQ_pure, bind_assoc] using complete

end Hidden
end EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

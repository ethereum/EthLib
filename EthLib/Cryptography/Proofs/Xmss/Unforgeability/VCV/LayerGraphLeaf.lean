module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphStarts

/-! # Chain endpoints of a complete leanXMSS leaf

The leanXMSS draft, section "WOTS+C", hashes the last value of every chain in chain order.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

open Constants HashSig OracleSpec OracleComp Wots
open ChainGraph (Word digestEquiv)

def position (e : UInt32) (i : Fin V) (pos : Nat) : Cell :=
  if pos = 0 then .inl (e, i)
  else .inr (.inl (.chain e i (Fin.ofNat 3 (pos - 1))))

theorem chainCell_eq (e : UInt32) (i : Fin V) (j : Fin (CHAIN_LENGTH - 1)) :
    chainCell e i j = position e i j.val := by
  by_cases h : j.val = 0
  · simp [chainCell, position, h]
  · have bound : j.val < 3 := j.isLt
    have step : Fin.ofNat 3 (j.val - 1) = ⟨j.val - 1, by omega⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    simp [chainCell, position, h]
    exact congrArg (Role.chain e i) step.symm

def schedule (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V) :
    GraphChain.Schedule (graph pp layer) (CHAIN_LENGTH - 1) where
  cell := position e i
  low j := .inl (.chain e i j)
  high j := .inr (.chain e i j)
  low_children j := congrArg (fun c => [c]) (chainCell_eq e i j)
  high_children j := congrArg (fun c => [c]) (chainCell_eq e i j)
  next j := by
    have idx : Fin.ofNat 3 j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    simp [position]
    exact congrArg (Role.chain e i) idx

theorem chainStep_eq (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (j : Fin (CHAIN_LENGTH - 1)) (d : Digest) :
    chainStep hash pp layer e i j d = GraphChain.publicStep (schedule pp layer e i) digestEquiv j d := by
  let bytes := (thInput pp (addrChain layer e j) (packBytes d ++ packBytes (uintToBytes 16 i.val))).data.toList
  have raw : input pp layer (.chain e i j) [digestEquiv d] = bytes := by
    change (thInput pp _ (packBytes (ofBV 16 (digestEquiv d)) ++ packBytes (uintToBytes 16 i.val))).data.toList = _
    rw [show ofBV 16 (digestEquiv d) = d from digestEquiv.symm_apply_apply d]
    rfl
  unfold GraphChain.publicStep
  change _ = (do
    let lo ← query (spec := Spec) (.inl (.inl (.inr (.inl (input pp layer (.chain e i j) [digestEquiv d])))))
    let _ ← query (spec := Spec) (.inl (.inl (.inr (.inr (input pp layer (.chain e i j) [digestEquiv d])))))
    pure (digestEquiv.symm lo))
  rw [raw]
  simp only [chainStep, th, hash_eq, bind_assoc, pure_bind, PairedHashWord.first_half_bytes,
    Equiv.apply_symm_apply]
  rfl

/-- The third physical chain step records the digest that the leaf reads. -/
theorem chain_end_recorded (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (d : Digest) (st : State) (start : st.2 (.inl (e, i)) = some (digestEquiv d)) {z}
    (run : z ∈ support ((simulateQ (graph pp layer).eagerImpl
      (chain hash pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) d)).run st)) :
    Recorded (.chain e i ⟨CHAIN_LENGTH - 2, by decide⟩) z.1 z.2 :=
  GraphChain.chain_records_result (schedule pp layer e i) digestEquiv
    (chainStep hash pp layer e i)
    (fun j v => congrArg (simulateQ (graph pp layer).eagerImpl) (chainStep_eq pp layer e i j v))
    0 (CHAIN_LENGTH - 1) (by decide) d st start run

def endWords (ends : Vector Digest V) : List Word := List.ofFn fun i : Fin V => digestEquiv ends[i]

theorem endWords_digests (ends : Vector Digest V) : LeafGraph.digests V (endWords ends) = ends := by
  apply Vector.ext
  intro i hi
  have input : (endWords ends)[i]? = some (digestEquiv ends[i]) := by
    rw [List.getElem?_eq_getElem (by simpa [endWords] using hi)]
    simp [endWords]
  calc
    _ = ofBV 16 ((endWords ends)[i]?.getD 0) :=
      Vector.getElem_ofFn (f := fun j : Fin V => ofBV 16 ((endWords ends)[j.val]?.getD 0)) hi
    _ = _ := by rw [input]; exact digestEquiv.symm_apply_apply _

theorem leafHash_of_recorded (pp : PublicParam) (layer : Layer) (e : UInt32)
    (ends : Vector Digest V) (st : State)
    (record : ∀ i : Fin V, Recorded (.chain e i ⟨CHAIN_LENGTH - 2, by decide⟩) ends[i] st) :
    (simulateQ (graph pp layer).eagerImpl (otsLeafHash hash pp layer e ends)).run st =
      (simulateQ (graph pp layer).eagerImpl (readOutput (.leaf e))).run st := by
  apply th_of_ready pp layer (.leaf e) (endWords ends)
  · apply List.forall₂_of_length_eq_of_get (by simp [endWords, children])
    intro i hi hj
    have bound : i < V := by simpa [children] using hi
    have slot : (children (.leaf e))[i]'hi =
        (.inr (.inl (.chain e ⟨i,bound⟩ ⟨CHAIN_LENGTH - 2, by decide⟩)) : Cell) :=
      List.getElem_ofFn (f := fun ix : Fin V => (Sum.inr (Sum.inl (Role.chain e ix
        ⟨CHAIN_LENGTH - 2, by decide⟩)) : Cell)) _
    have value {a b : Cell} (same : a = b) : st.2 a = st.2 b := by cases same; rfl
    refine (value slot).trans ?_
    simpa only [endWords, List.get_eq_getElem, List.getElem_ofFn, Recorded] using record ⟨i,bound⟩
  · change (thInput pp (addrLeaf layer e) (packDigests (LeafGraph.digests V (endWords ends)))).data.toList = _
    rw [endWords_digests]

private theorem settles_sequence {α β : Type} (pp : PublicParam) (layer : Layer) (r : Role)
    (first : OracleComp Spec α) (walk : α → OracleComp Spec β) (finish : β → OracleComp Spec Digest)
    (ready : α → State → Prop) (done_ : β → State → Prop)
    (startReady : ∀ (st : State) (z : α × State), z ∈ support ((simulateQ (graph pp layer).eagerImpl first).run st) → ready z.1 z.2)
    (walkDone : ∀ a st, ready a st → ∀ z ∈ support
      ((simulateQ (graph pp layer).eagerImpl (walk a)).run st), done_ z.1 z.2)
    (finishDone : ∀ b st, done_ b st → ∀ z ∈ support
      ((simulateQ (graph pp layer).eagerImpl (finish b)).run st), Recorded r z.1 z.2) :
    Settles pp layer r (first >>= fun a => walk a >>= finish) := by
  intro st z hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨a, ha, b, hb, last⟩ := hz
  exact finishDone b.1 b.2 (walkDone a.1 a.2 (startReady st a ha) b hb) z last

/-- An honest leaf reads its 29 private words, walks each of its 58 chains for three steps,
then stores the returned leaf digest in the row read by its Merkle parent. -/
theorem otsPublicLeaf_settles (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec))
    (e : UInt32) : Settles pp layer (.leaf e) (otsPublicLeaf hash pp (startPrf pp layer other) layer e) := by
  apply settles_sequence pp layer (.leaf e)
    (chainStarts pp (startPrf pp layer other) layer e)
    (fun starts => ofFnInOrder V fun i => chain hash pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) starts[i])
    (otsLeafHash hash pp layer e)
    (fun starts st => ∀ i : Fin V, st.2 (.inl (e,i)) = some (digestEquiv (starts[i.val]'i.isLt)))
    (fun ends st => ∀ i : Fin V, Recorded (.chain e i ⟨CHAIN_LENGTH - 2, by decide⟩) ends[i] st)
  · exact @starts_stored pp layer other e
  · intro starts st first
    exact fun _ => collect_recorded pp layer V
      (fun i => chain hash pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) starts[i])
      (fun i d s => Recorded (.chain e i ⟨CHAIN_LENGTH - 2, by decide⟩) d s) st
      (fun _ _ _ _ ext old => ext.2 old)
      (fun i s ext _ hr => chain_end_recorded pp layer e i _ s (ext.2 (first i)) hr)
  · intro ends st last z
    rw [leafHash_of_recorded pp layer e ends st last]
    exact readOutput_recorded pp layer (.leaf e) st

/-- Every original node and layer root built with the paired private interface has the same
output and complete caches as the recursively normalized Merkle walk, with no leaf premise. -/
theorem node_settles (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec))
    (l j : Nat) (valid : l ≤ LAYER_HEIGHT) :
    let prf := startPrf pp layer other
    simulateQ (graph pp layer).eagerImpl (Xmss.node hash pp prf layer l j) =
      simulateQ (graph pp layer).eagerImpl (normalizedNode (leaves hash pp prf layer) l j) ∧
    Settles pp layer (treeRole l j) (Xmss.node hash pp prf layer l j) :=
  node_of_settled_leaves pp layer (startPrf pp layer other)
    (fun i => otsPublicLeaf_settles pp layer other (UInt32.ofNat i)) l j valid

end EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

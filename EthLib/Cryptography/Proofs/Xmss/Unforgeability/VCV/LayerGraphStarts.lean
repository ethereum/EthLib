module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphSubtree
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ChainStarts

/-! # The private start words of one leanXMSS layer

The leanXMSS draft, section "WOTS+C", derives the starts of chains `2j` and `2j+1` together.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

open Constants HashSig OracleSpec OracleComp
open ChainGraph (Word digestEquiv pairIndex indexAt)

/-- Each recorded value remains true along the rest of an ordered vector computation. -/
theorem collect_recorded (pp : PublicParam) (layer : Layer) {α : Type} (n : Nat)
    (f : Fin n → OracleComp Spec α) (record : Fin n → α → State → Prop) (initial : State)
    (mono : ∀ i a {s t}, s ≤ t → record i a s → record i a t)
    (entry : ∀ (i : Fin n) (s : State), initial ≤ s → ∀ z ∈ support
      ((simulateQ (graph pp layer).eagerImpl (f i)).run s), record i z.1 z.2)
    {z : Vector α n × State}
    (run : z ∈ support ((simulateQ (graph pp layer).eagerImpl (ofFnInOrder n f)).run initial)) :
    ∀ i : Fin n, record i z.1[i] z.2 := by
  induction n generalizing initial with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
    simp only [ofFnInOrder, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨head, first, tail, rest, rfl⟩ := run
    have extHead := state_extends pp layer _ initial first
    have extTail := state_extends pp layer _ head.2 rest
    have previous := entry 0 initial le_rfl head first
    have tailWords := ih (fun j => f j.succ) (fun j => record j.succ) head.2
      (fun j => mono j.succ) (fun j s h => entry j.succ s (extHead.trans h)) rest
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using mono 0 head.1 extTail previous
    · simpa using tailWords j

abbrev PairKey := UInt32 × Fin (V / 2)

/-- Reassemble one full private PRF reply from its two chain starts, in physical byte order. -/
noncomputable def readPair (key : PairKey) : OracleComp Spec (Vector UInt8 32) := do
  let lo ← readCell (some (.inl (key.1, indexAt key.2 0)))
  let hi ← readCell (some (.inl (key.1, indexAt key.2 1)))
  pure (ofOutput (PairedHashWord.halves.symm (lo, hi)))

/-- Translate the chain-start requests for this parameter and layer.

All other full-word requests go through the supplied private oracle. -/
noncomputable def startPrf (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec)) :
    SeedPrf (OracleComp Spec) := open Classical in fun p a suffix =>
  if h : ∃ k : PairKey, p = pp ∧ a = addrPrf layer k.1 k.2 ∧ suffix = ByteArray.empty then
    readPair h.choose
  else other p a suffix

theorem startPrf_pair (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec))
    (e : UInt32) (j : Fin (V / 2)) :
    startPrf pp layer other pp (addrPrf layer e j) ByteArray.empty = readPair (e, j) := by
  have h : ∃ k : PairKey, pp = pp ∧ addrPrf layer e j = addrPrf layer k.1 k.2 ∧
      ByteArray.empty = ByteArray.empty := ⟨(e,j), rfl, rfl, rfl⟩
  have eqn := addrPrf_inj.mp h.choose_spec.2.1
  exact (dite_eq_left h).trans (congrArg readPair (Prod.ext eqn.2.1.symm eqn.2.2.symm))

private def PairStored (e : UInt32) (j : Fin (V / 2)) (full : Vector UInt8 32)
    (st : State) : Prop :=
  ∀ h : Fin 2, st.2 (.inl (e, indexAt j h)) = some (digestEquiv (halfOf h full))

private theorem pair_low (a b : Word) :
    digestEquiv (halfOf 0 (ofOutput (PairedHashWord.halves.symm (a,b)))) = a := by
  have bytes := (PairedHashWord.first_half_bytes (PairedHashWord.halves.symm (a,b))).trans
    (congrArg (fun p : Word × Word => ofBV 16 p.1) (PairedHashWord.halves.apply_symm_apply (a,b)))
  exact (congrArg digestEquiv bytes).trans (digestEquiv.apply_symm_apply a)

private theorem pair_high (a b : Word) :
    digestEquiv (halfOf 1 (ofOutput (PairedHashWord.halves.symm (a,b)))) = b := by
  have bytes := (PairedHashWord.second_half_bytes (PairedHashWord.halves.symm (a,b))).trans
    (congrArg (fun p : Word × Word => ofBV 16 p.2) (PairedHashWord.halves.apply_symm_apply (a,b)))
  exact (congrArg digestEquiv bytes).trans (digestEquiv.apply_symm_apply b)

private theorem readPair_stored (pp : PublicParam) (layer : Layer) (e : UInt32) (j : Fin (V / 2))
    (st : State) {z} (run : z ∈ support
      ((simulateQ (graph pp layer).eagerImpl (readPair (e,j))).run st)) :
        PairStored e j z.1 z.2 := by
  simp only [readPair, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    CanonicalGraph.eagerImpl_readCell_run, mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨a, ha, b, hb, rfl⟩ := run
  obtain ⟨_, low⟩ := RelabelState.le_and_cell_eq_of_mem_support_drawCell ha
  obtain ⟨extendsState, high⟩ := RelabelState.le_and_cell_eq_of_mem_support_drawCell hb
  intro h
  have choices : h = 0 ∨ h = 1 := by
    have : h.val = 0 ∨ h.val = 1 := by omega
    exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  rcases choices with rfl | rfl
  · exact (extendsState.2 low).trans (congrArg some (pair_low a.1 b.1).symm)
  · exact high.trans (congrArg some (pair_high a.1 b.1).symm)

private def splitWords (pairs : Vector (Vector UInt8 32) (V / 2)) : Vector Digest V :=
  Vector.ofFn fun i => halfOf ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
    (pairs[(pairIndex i).val]'(pairIndex i).isLt)

private theorem split_recorded (pp : PublicParam) (layer : Layer) (e : UInt32)
    (p : OracleComp Spec (Vector (Vector UInt8 32) (V / 2))) (st : State)
    (stored : ∀ w ∈ support ((simulateQ (graph pp layer).eagerImpl p).run st),
      ∀ j : Fin (V / 2), PairStored e j w.1[j] w.2) {z : Vector Digest V × State}
    (run : z ∈ support ((simulateQ (graph pp layer).eagerImpl
      (do let w ← p; pure (splitWords w))).run st)) :
    ∀ i : Fin V, z.2.2 (.inl (e, i)) = some (digestEquiv (z.1[i.val]'i.isLt)) := by
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨words, draws, rfl⟩ := run
  intro i
  let h : Fin 2 := ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
  have hc := stored words draws (pairIndex i) h
  rw [show indexAt (pairIndex i) h = i from ChainGraph.indexAt_parts i] at hc
  have value := Vector.getElem_ofFn (f := fun j : Fin V =>
    halfOf ⟨j.val % 2, Nat.mod_lt _ (by decide)⟩
      (words.1[(pairIndex j).val]'(pairIndex j).isLt)) i.isLt
  exact hc.trans (congrArg (fun d => some (digestEquiv d)) value).symm

/-- A run of the real 29-pair collector records every one of its 58 returned digests. -/
theorem starts_stored (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec))
    (e : UInt32) (st : State) {z : Vector Digest V × State} :
    z ∈ support ((simulateQ (graph pp layer).eagerImpl
      (chainStarts (m := OracleComp Spec) pp (startPrf pp layer other) layer e)).run st) →
    ∀ i : Fin V, z.2.2 (.inl (e, i)) = some (digestEquiv (z.1[i.val]'i.isLt)) := by
  simp only [chainStarts, startPrf_pair]
  apply split_recorded pp layer e (ofFnInOrder (V / 2) fun j => readPair (e, j)) st
  exact fun _ => collect_recorded pp layer _ (fun j => readPair (e, j)) (PairStored e) st
    (fun _ _ _ _ ext old half => ext.2 (old half))
    (fun j s _ _ hr => readPair_stored pp layer e j s hr)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

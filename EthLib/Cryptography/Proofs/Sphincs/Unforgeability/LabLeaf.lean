module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.LabSteps

/-!
# Proofs: a key's leaf in the eager game

The honest leaf of a key derives its chain starts, walks each chain to its end, and hashes the ends.

The lab leaf touches the starts, runs the lab chain of each chain to its end, and reads the leaf.

It never reads a start or a value inside a chain, so a later game can defer those draws.

- In the eager game, a derivation asks its two halves, and each half is drawn in its cell.
- The honest derivation of the starts and the lab touches of their cells leave one law of the state.
- The honest leaf and the lab leaf have one law of the output and the final state.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open OracleSpec OracleComp

/-! ## Loops -/

section Loops

variable {ι : Type} {spec : OracleSpec ι} {σ : Type} {so : QueryImpl spec (StateT σ ProbComp)}

/-- **Loops in order.**

Let each pair of components form a triple that keeps `Inv` and relates its output by `R i`.

Then the two vectors computed in order form a triple, if each `R i` survives every later step. -/
theorem ofFnInOrder_eqDistTriple {α : Type} {r : σ → σ → Prop} [IsPreorder σ r]
    (Inv : σ → Prop) : ∀ {k : Nat} (R : Fin k → α → σ → Prop),
      (∀ i a s s', r s s' → R i a s → R i a s') → ∀ {f g : Fin k → OracleComp spec α},
      (∀ i, so.EqDistTriple r Inv (f i) (g i) fun a s => Inv s ∧ R i a s) →
      so.EqDistTriple r Inv (Xmss.ofFnInOrder k f) (Xmss.ofFnInOrder k g)
        fun v s => Inv s ∧ ∀ i, R i v[i] s
  | 0, _, _, _, _, _ => QueryImpl.EqDistTriple.pure _ fun _ h => ⟨h, fun i => i.elim0⟩
  | k + 1, R, hR, f, g, h => by
    simp only [Xmss.ofFnInOrder]
    refine (h 0).bind fun a => ?_
    refine ((ofFnInOrder_eqDistTriple Inv (fun i => R i.succ) (fun i => hR i.succ)
      fun i => h i.succ).frame (hR 0 a)).bind fun v => ?_
    refine QueryImpl.EqDistTriple.pure _ fun s ⟨⟨hI, hv⟩, ha⟩ => ⟨hI, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa using hv j

/-- Running a program and returning nothing is the program's result discarded. -/
theorem bind_pure_unit_eq_map {γ : Type} (x : StateT σ ProbComp γ) :
    (x >>= fun _ => pure ()) = (fun _ => ()) <$> x := by
  rw [map_eq_bind_pure_comp]
  rfl

/-- Two loops in order whose components leave one law of the state leave one law of the state. -/
theorem simulateQ_ofFnInOrder_discard {α β : Type} :
    ∀ {k : Nat} {f : Fin k → OracleComp spec α} {g : Fin k → OracleComp spec β},
      (∀ i, (fun _ => ()) <$> simulateQ so (f i) = (fun _ => ()) <$> simulateQ so (g i)) →
      (fun _ => ()) <$> simulateQ so (Xmss.ofFnInOrder k f) =
        (fun _ => ()) <$> simulateQ so (Xmss.ofFnInOrder k g)
  | 0, _, _, _ => by simp only [Xmss.ofFnInOrder, simulateQ_pure, map_pure]
  | k + 1, f, g, h => by
    have ih := simulateQ_ofFnInOrder_discard fun i => h i.succ
    have e : ∀ {γ δ : Type} (x : StateT σ ProbComp γ) (y : StateT σ ProbComp δ),
        (x >>= fun _ => y) = ((fun _ => ()) <$> x) >>= fun _ => y := fun x y => by
      rw [bind_map_left]
    simp only [Xmss.ofFnInOrder, simulateQ_bind, simulateQ_pure, map_bind, map_pure]
    rw [e (simulateQ so (f 0)), h 0, ← e, bind_pure_unit_eq_map, bind_pure_unit_eq_map, ih]

end Loops

/-! ## Derivations -/

/-- The derivations of the game that skips the thrown-away halves, in the lab world. -/
noncomputable def labPrf : SeedPrf (OracleComp LabWorld) :=
  mapPrf (fun oa => liftComp oa LabWorld) skipPrf

/-- In the lab world, a derivation reads the cells of its two halves and joins them. -/
theorem labPrf_eq (pp : PublicParam) {A : Address} (hA : IsDerivationAddress A)
    (suffix : ByteArray) :
    labPrf pp A suffix = (do
      let u ← readCell (some (.inl (⟨(pp, A, suffix), hA⟩, 0)))
      let v ← readCell (some (.inl (⟨(pp, A, suffix), hA⟩, 1)))
      return outputOf (hashHalves.symm (u, v))) := by
  simp only [labPrf, mapPrf, skipPrf, derivationPrf, hA, ↓reduceDIte, simulateQ_map,
    simulateQ_spec_query, skipHalves_inr, map_bind, map_pure, liftComp_bind,
    liftComp_pure]
  rfl

/-- A read of a cell draws it: the cell then holds the value read. -/
theorem readCell_self_labTriple (P : PublicParam) (c : Cell) :
    LabTriple P (fun _ => True) (readCell (some c)) (readCell (some c))
      fun y st => st.2 c = some y :=
  QueryImpl.EqDistTriple.of_support fun st _ z hz => by
    rw [(graph P).eagerImpl_readCell_run] at hz
    exact RelabelState.le_and_cell_eq_of_mem_support_drawCell hz

/-- A derivation from the seed leaves each half in its cell. -/
theorem derivation_labTriple (P : PublicParam) {A : Address} (hA : IsDerivationAddress A) :
    LabTriple P (fun _ => True) (labPrf P A .empty) (labPrf P A .empty)
      fun out st => ∀ h : Fin 2, st.2 (.inl (⟨(P, A, .empty), hA⟩, h)) = some (halfOf h out) := by
  rw [labPrf_eq P hA]
  refine (readCell_self_labTriple P _).bind fun u => ?_
  refine (((readCell_self_labTriple P _).frame
    (F := fun st => st.2 (.inl (⟨(P, A, .empty), hA⟩, 0)) = some u)
    fun _ _ hle h => hle.2 h).mono (fun _ h => ⟨trivial, h⟩) fun _ _ h => h).bind fun v => ?_
  refine QueryImpl.EqDistTriple.pure _ fun st ⟨hv, hu⟩ h => ?_
  fin_cases h
  · exact hu.trans (congrArg some (halfOf_zero_hashHalves_symm u v).symm)
  · exact hv.trans (congrArg some (halfOf_one_hashHalves_symm u v).symm)

/-- The lab touch of a derivation: both of its halves, half 0 first. -/
noncomputable def touchDerivation (x : DerivationInput) : OracleComp LabWorld Unit := do
  touchCell (some (.inl (x, 0)))
  touchCell (some (.inl (x, 1)))

/-- In the eager game, touching a derivation leaves the state as deriving it does. -/
theorem simulateQ_eagerImpl_touchDerivation (P : PublicParam) {A : Address}
    (hA : IsDerivationAddress A) :
    simulateQ (graph P).eagerImpl (touchDerivation ⟨(P, A, .empty), hA⟩) =
      (fun _ => ()) <$> simulateQ (graph P).eagerImpl (labPrf P A .empty) := by
  rw [labPrf_eq P hA]
  simp only [touchDerivation, simulateQ_bind, simulateQ_pure,
    (graph P).simulateQ_eagerImpl_touchCell, map_bind, map_pure, ← bind_pure_unit_eq_map]
  simp only [bind_assoc, pure_bind]

/-! ## The starts of the chains -/

/-- The derivation that starts chains `2j` and `2j + 1` of a key. -/
def pairInput (P : PublicParam) (key : GraphKey) (j : Fin (V / 2)) : DerivationInput :=
  ⟨(P, addrPrf key.toOtsKey j, .empty), isDerivationAddress_addrPrf _ _⟩

/-- **The starts of a key's chains.**

The honest derivation of the starts leaves the start of each chain in the chain's first cell. -/
theorem chainStarts_labTriple (P : PublicParam) (key : GraphKey) :
    LabTriple P (fun _ => True) (chainStarts P labPrf key.toOtsKey)
      (chainStarts P labPrf key.toOtsKey)
      fun starts st => ∀ i, Holds st (chainCell P key i 0) starts[i] := by
  simp only [chainStarts]
  refine (ofFnInOrder_eqDistTriple (fun _ => True)
    (fun j out st => ∀ h : Fin 2, st.2 (.inl (pairInput P key j, h)) = some (halfOf h out))
    (fun _ _ _ _ hle h half => hle.2 (h half))
    fun _ => (derivation_labTriple P (isDerivationAddress_addrPrf _ _)).mono (fun _ h => h)
      fun _ _ h => ⟨trivial, h⟩).bind
      fun pairs => QueryImpl.EqDistTriple.pure _ fun st ⟨_, h⟩ i => ⟨_, rfl, ?_⟩
  have hi := h ⟨i.val / 2, by have := i.isLt; simp only [V] at *; omega⟩
    ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact hi

/-- The lab touch of the starts of a key's chains: each pair in the honest order. -/
noncomputable def touchStarts (P : PublicParam) (key : GraphKey) : OracleComp LabWorld Unit := do
  let _ ← Xmss.ofFnInOrder (V / 2) fun j => touchDerivation (pairInput P key j)
  pure ()

/-- In the eager game, touching the starts leaves the state as deriving them does. -/
theorem simulateQ_eagerImpl_touchStarts (P : PublicParam) (key : GraphKey) :
    simulateQ (graph P).eagerImpl (touchStarts P key) =
      (fun _ => ()) <$> simulateQ (graph P).eagerImpl (chainStarts P labPrf key.toOtsKey) := by
  have hc := simulateQ_ofFnInOrder_discard (so := (graph P).eagerImpl)
    (f := fun j => touchDerivation (pairInput P key j))
    (g := fun j => labPrf P (addrPrf key.toOtsKey j) .empty) fun j => by
      rw [pairInput, simulateQ_eagerImpl_touchDerivation P (isDerivationAddress_addrPrf _ _),
        Functor.map_map]
  simp only [touchStarts, chainStarts, simulateQ_bind, simulateQ_pure, map_bind, map_pure]
  rw [bind_pure_unit_eq_map, bind_pure_unit_eq_map, hc]

/-! ## The key's leaf -/

/-- The lab leaf of a key: touch the starts, run each lab chain to its end, read the leaf. -/
noncomputable def labOtsLeaf (P : PublicParam) (key : GraphKey) : OracleComp LabWorld Digest := do
  touchStarts P key
  let _ ← Xmss.ofFnInOrder V fun i => labChain P key i (CHAIN_LENGTH - 1)
  readNode (.otsLeaf key)

/-- **A key's leaf.**

The honest leaf of a key and its lab leaf have one law of the output and the final state.

The leaf's cell then holds the result. -/
theorem otsPublicLeaf_labTriple (P : PublicParam) (key : GraphKey) :
    LabTriple P (fun _ => True) (otsPublicLeaf labH P labPrf key.toOtsKey) (labOtsLeaf P key)
      fun y st => st.2 (.inr (.otsLeaf key)) = some y := by
  have hlab : simulateQ (graph P).eagerImpl (labOtsLeaf P key) =
      simulateQ (graph P).eagerImpl (do
        let _ ← chainStarts P labPrf key.toOtsKey
        let _ ← Xmss.ofFnInOrder V fun i => labChain P key i (CHAIN_LENGTH - 1)
        readNode (.otsLeaf key)) := by
    simp only [labOtsLeaf, simulateQ_bind, simulateQ_eagerImpl_touchStarts, bind_map_left]
  refine QueryImpl.EqDistTriple.of_simulateQ_eq_right ?_ hlab.symm
  simp only [otsPublicLeaf, Sphincs.chain]
  refine (chainStarts_labTriple P key).bind fun starts => ?_
  refine (ofFnInOrder_eqDistTriple (fun st => ∀ i, Holds st (chainCell P key i 0) starts[i])
    (fun i y st => Holds st (chainCell P key i (CHAIN_LENGTH - 1)) y)
    (fun _ _ _ _ hle h => h.mono hle)
    fun i => (((labChain_labTriple P key i starts[i] le_rfl).frame
      (F := fun st => ∀ i, Holds st (chainCell P key i 0) starts[i])
      fun _ _ hle h i => (h i).mono hle).mono (fun st h => ⟨h i, h⟩)
        fun _ _ h => ⟨h.2, h.1⟩)).bind fun ends => ?_
  exact (otsLeafHash_labTriple P key ends).mono (fun _ h => h.2) fun _ _ h => h

end EthLib.Cryptography.Sphincs.Unforgeability

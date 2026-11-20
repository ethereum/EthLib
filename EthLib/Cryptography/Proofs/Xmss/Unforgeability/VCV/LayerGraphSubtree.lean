module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraph

/-!
# Merkle subtrees in the leanXMSS layer graph

The leanXMSS draft, section "Trees", computes a node by hashing its left and right subtrees.
Both subtrees retain their low output at a known row.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

open Constants HashSig OracleSpec OracleComp
open ChainGraph (Word Public digestEquiv)

abbrev Spec := Public.withLabels Start Row Word
abbrev State := RelabelState Public Start Row Word

def liftRows : QueryImpl (unifSpec + Public) (OracleComp Spec) :=
  Sum.rec (fun j => query (spec := Spec) (.inl (.inl (.inl j))))
    (fun b => query (spec := Spec) (.inl (.inl (.inr b))))

/-- A physical full-word call, translated into the public rows of the common layer graph. -/
def hash (bytes : ByteArray) : OracleComp Spec (Vector UInt8 32) :=
  simulateQ liftRows (simulateQ PairedHashWord.readHalves (queryH (m := OracleComp OracleWorld) bytes))

theorem hash_eq (bytes : ByteArray) : hash bytes = (do
    let lo ← query (spec := Spec) (.inl (.inl (.inr (.inl bytes.data.toList))))
    let hi ← query (spec := Spec) (.inl (.inl (.inr (.inr bytes.data.toList))))
    pure (ofOutput (PairedHashWord.halves.symm (lo, hi)))) := by
  change simulateQ liftRows (simulateQ PairedHashWord.readHalves (ofOutput <$>
    (liftM (OracleWorld.query (.inr bytes.data.toList)) : OracleComp OracleWorld HashOutput))) = _
  simp [PairedHashWord.readHalves, RandomOraclePairedValue.readHalves, liftRows, ← bind_pure_comp]

/-- A node forwards the low digest and keeps its high reply in the graph. -/
noncomputable def readOutput (r : Role) : OracleComp Spec Digest := do
  let lo ← readCell (some (.inr (.inl r)))
  touchCell (some (.inr (.inr r)))
  pure (digestEquiv.symm lo)

def treeRole (level j : Nat) : Role :=
  atDepth (Fin.ofNat (LAYER_HEIGHT + 1) level) (UInt32.ofNat j)

private theorem treeRole_eq (l j : Nat) (h : l ≤ LAYER_HEIGHT) :
    treeRole l j = atDepth ⟨l, by omega⟩ (UInt32.ofNat j) := by
  unfold treeRole
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt (by omega)

theorem treeRole_succ (l j : Nat) (h : l < LAYER_HEIGHT) :
    treeRole (l + 1) j = .node ⟨l, h⟩ (UInt32.ofNat j) := by
  rw [treeRole_eq _ _ (by omega)]
  simp [atDepth]

/-- At every valid depth, the library's two recursive calls land at the graph's two child roles. -/
theorem treeRole_children (l j : Nat) (h : l < LAYER_HEIGHT) :
    children (treeRole (l + 1) j) =
      [.inr (.inl (treeRole l (2 * j))), .inr (.inl (treeRole l (2 * j + 1)))] := by
  rw [treeRole_succ _ _ h, treeRole_eq l _ (Nat.le_of_lt h), treeRole_eq l _ (Nat.le_of_lt h)]
  simp [children]

theorem node_input (pp : PublicParam) (layer : Layer) (l j : Nat) (h : l < LAYER_HEIGHT)
    (a b : Digest) : input pp layer (treeRole (l + 1) j) [digestEquiv a, digestEquiv b] =
      (thInput pp (addrNode layer (Fin.ofNat _ (l + 1)) (UInt32.ofNat j))
        (packBytes a ++ packBytes b)).data.toList := by
  let ds := LeafGraph.digests 2 [digestEquiv a, digestEquiv b]
  have slot (i : Fin 2) : ds[i.val] =
      ofBV 16 (([digestEquiv a, digestEquiv b] : List Word)[i.val]?.getD 0) :=
    Vector.getElem_ofFn (f := fun k : Fin 2 =>
      ofBV 16 (([digestEquiv a, digestEquiv b] : List Word)[k.val]?.getD 0)) i.isLt
  have first : ds[0] = a := (slot 0).trans (digestEquiv.symm_apply_apply a)
  have second : ds[1] = b := (slot 1).trans (digestEquiv.symm_apply_apply b)
  have level : Fin.ofNat (LAYER_HEIGHT + 1) (l + 1) = (⟨l, h⟩ : Fin LAYER_HEIGHT).succ :=
    Fin.ext (Nat.mod_eq_of_lt (by omega))
  rw [treeRole_succ _ _ h, level]
  change (thInput pp _ (packDigests ds)).data.toList = _
  rw [LeafGraph.pack_pair, first, second]
  rfl

def Recorded (r : Role) (d : Digest) (st : State) : Prop := st.2 (.inr (.inl r)) = some (digestEquiv d)

theorem readOutput_recorded (pp : PublicParam) (layer : Layer) (r : Role) (st : State) {z}
    (hz : z ∈ support ((simulateQ (graph pp layer).eagerImpl (readOutput r)).run st)) :
    Recorded r z.1 z.2 := by
  simp only [readOutput, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    CanonicalGraph.eagerImpl_readCell_run, CanonicalGraph.eagerImpl_touchCell_run, bind_map_left,
    mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hb).1.2
    (by simpa [Recorded] using (RelabelState.le_and_cell_eq_of_mem_support_drawCell ha).2)

/-- Any ready role can use its carried ordered values directly in the actual tweakable hash. -/
theorem th_of_ready (pp : PublicParam) (layer : Layer) (r : Role) (vs : List Word)
    (addr : Address) (data : ByteArray) (st : State)
    (cells : List.Forall₂ (fun c v => st.2 c = some v) (children r) vs)
    (raw : input pp layer r vs = (thInput pp addr data).data.toList) :
    (simulateQ (graph pp layer).eagerImpl (th hash pp addr data)).run st =
      (simulateQ (graph pp layer).eagerImpl (readOutput r)).run st := by
  let G := graph pp layer
  have both := G.eagerImpl_siblings_run_of_childVals (.inl r) (.inr r) vs st
    (G.childVals_eq_some_iff.mpr cells) (G.childVals_eq_some_iff.mpr cells)
  let bytes := input pp layer r vs
  let askLow : OracleComp Spec Word := query (spec := Spec) (.inl (.inl (.inr (.inl bytes))))
  let askHigh : OracleComp Spec Word := query (spec := Spec) (.inl (.inl (.inr (.inr bytes))))
  change (simulateQ G.eagerImpl (do let m ← askLow; let n ← askHigh; pure (m, n))).run st = _ at both
  have physical : th hash pp addr data =
      (do let lo ← askLow; let _ ← askHigh; pure (digestEquiv.symm lo)) := by
    dsimp only [askLow, askHigh, bytes]
    rw [raw]
    simp only [th, hash_eq, bind_assoc, pure_bind, PairedHashWord.first_half_bytes,
      Equiv.apply_symm_apply]
    rfl
  have eqn := congrArg (fun body => (fun p : (Word × Word) × State => (digestEquiv.symm p.1.1, p.2)) <$> body) both
  rw [physical, readOutput]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
    CanonicalGraph.simulateQ_eagerImpl_touchCell, bind_map_left] at eqn ⊢
  exact eqn

/-- The actual binary hash uses the child values carried from the two preceding returns. -/
theorem nodeHash_of_recorded (pp : PublicParam) (layer : Layer) (l j : Nat) (h : l < LAYER_HEIGHT)
    (a b : Digest) (st : State) (left : Recorded (treeRole l (2 * j)) a st)
    (right : Recorded (treeRole l (2 * j + 1)) b st) :
    (simulateQ (graph pp layer).eagerImpl (nodeHash hash pp layer ⟨l + 1, j⟩ a b)).run st =
    (simulateQ (graph pp layer).eagerImpl (readOutput (treeRole (l + 1) j))).run st := by
  let r := treeRole (l + 1) j
  let vs := [digestEquiv a, digestEquiv b]
  have cells : List.Forall₂ (fun c v => st.2 c = some v) (children r) vs := by
    rw [treeRole_children _ _ h]
    exact .cons left (.cons right .nil)
  exact th_of_ready pp layer r vs _ _ st cells (node_input pp layer l j h a b)

/-- All supported results record their returned digest at the designated low row. -/
def Settles (pp : PublicParam) (layer : Layer) (r : Role) (op : OracleComp Spec Digest) : Prop :=
  ∀ (st : State) z, z ∈ support ((simulateQ (graph pp layer).eagerImpl op).run st) →
    Recorded r z.1 z.2

/-- Running any continuation in the eager graph preserves all recorded words. -/
theorem state_extends (pp : PublicParam) (layer : Layer) {α : Type} (op : OracleComp Spec α)
    (st : State) {z} (run : z ∈ support ((simulateQ (graph pp layer).eagerImpl op).run st)) : st ≤ z.2 :=
  simulateQ_run_preservesInv _ (st ≤ ·)
    (fun _ _ prev _ hz => prev.trans ((graph pp layer).le_of_mem_support_eagerImpl hz))
    op st le_rfl z run

/-- The normalized recursion evaluates each subtree in library order before reading its parent. -/
noncomputable def normalizedNode (base : Nat → OracleComp Spec Digest) (l j : Nat) : OracleComp Spec Digest :=
  Merkle.node (fun p _ _ => readOutput (treeRole p.level p.index)) base ⟨l, j⟩

/-- After the leaves have recorded their low outputs, every subtree can replace its internal
physical hashes by reads of their parent roles. The complete final caches and root digest agree. -/
theorem subtree (pp : PublicParam) (layer : Layer) (base : Nat → OracleComp Spec Digest)
    (baseRecords : ∀ j, Settles pp layer (treeRole 0 j) (base j)) :
    ∀ (l j : Nat), l ≤ LAYER_HEIGHT →
      simulateQ (graph pp layer).eagerImpl (Merkle.node (nodeHash hash pp layer) base ⟨l, j⟩) =
        simulateQ (graph pp layer).eagerImpl (normalizedNode base l j) ∧
      Settles pp layer (treeRole l j) (Merkle.node (nodeHash hash pp layer) base ⟨l, j⟩)
  | 0, j, _ => ⟨rfl, baseRecords j⟩
  | l + 1, j, valid => by
    let G := graph pp layer
    let walk := Merkle.node.go (nodeHash hash pp layer) base
    obtain ⟨leftEq, leftAt⟩ := subtree pp layer base baseRecords l (2 * j) (by omega)
    obtain ⟨rightEq, rightAt⟩ := subtree pp layer base baseRecords l (2 * j + 1) (by omega)
    have last (st : State) {a b : Digest × State}
        (hl : a ∈ support ((simulateQ G.eagerImpl (walk l (2 * j))).run st))
        (hr : b ∈ support ((simulateQ G.eagerImpl (walk l (2 * j + 1))).run a.2)) :
        (simulateQ G.eagerImpl (nodeHash hash pp layer ⟨l + 1, j⟩ a.1 b.1)).run b.2 =
          (simulateQ G.eagerImpl (readOutput (treeRole (l + 1) j))).run b.2 := by
      -- The right subtree can query old rows, but keeps the left digest already stored there.
      have ext := state_extends pp layer _ a.2 hr
      exact nodeHash_of_recorded pp layer l j (by omega) a.1 b.1 b.2
        (ext.2 (leftAt st a hl)) (rightAt a.2 b hr)
    constructor
    · ext st : 1
      unfold normalizedNode at leftEq rightEq ⊢
      simp only [Merkle.node] at leftEq rightEq
      simp only [Merkle.node, Merkle.node.go, simulateQ_bind, StateT.run_bind]
      rw [← leftEq, ← rightEq]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro a hl
      apply OracleComp.bind_congr_of_forall_mem_support
      intro b hr
      exact last st hl hr
    · intro st z hz
      simp only [Merkle.node, Merkle.node.go, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨a, ha, b, hb, parent⟩ := hz
      rw [last st ha hb] at parent
      exact readOutput_recorded pp layer (treeRole (l + 1) j) b.2 parent

/-- The actual leanXMSS tree computation uses the same recursion, including height 16 and every
32-bit index chosen by the library. The leaf premise concerns only its honest leaf computation. -/
theorem node_of_settled_leaves (pp : PublicParam) (layer : Layer) (prf : SeedPrf (OracleComp Spec))
    (leafRecords : ∀ j, Settles pp layer (treeRole 0 j) (leaves hash pp prf layer j))
    (l j : Nat) (valid : l ≤ LAYER_HEIGHT) :
    simulateQ (graph pp layer).eagerImpl (Xmss.node hash pp prf layer l j) =
      simulateQ (graph pp layer).eagerImpl (normalizedNode (leaves hash pp prf layer) l j) ∧
    Settles pp layer (treeRole l j) (Xmss.node hash pp prf layer l j) :=
  subtree pp layer _ leafRecords l j valid

/-- All heights also admit a closed boundary computation which reads the actual low leaf rows. -/
theorem subtree_from_read_leaves (pp : PublicParam) (layer : Layer) (l j : Nat) (valid : l ≤ LAYER_HEIGHT) :
    let base := fun index => readOutput (treeRole 0 index)
    simulateQ (graph pp layer).eagerImpl (Merkle.node (nodeHash hash pp layer) base ⟨l, j⟩) =
      simulateQ (graph pp layer).eagerImpl (normalizedNode base l j) ∧
    Settles pp layer (treeRole l j) (Merkle.node (nodeHash hash pp layer) base ⟨l, j⟩) :=
  subtree pp layer _ (fun index st _ => readOutput_recorded pp layer (treeRole 0 index) st) l j valid

end EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

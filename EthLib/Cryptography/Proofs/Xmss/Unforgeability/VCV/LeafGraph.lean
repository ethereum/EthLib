module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ChainGraphWalk
public import EthLib.Cryptography.Xmss.Tree
public import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead.Children

/-!
# Hashing an ordered vector of leanXMSS digests

The leanXMSS draft, section "WOTS+C", hashes 58 ordered chain ends into a leaf.

Sections "Hashing and parameters" and "Trees" use the same full-word hash for a pair of children.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.LeafGraph

open Constants HashSig OracleSpec OracleComp
open ChainGraph (Word Public)

/-- The endpoint cells are read from index zero upward. -/
def children (n : Nat) : List (Fin n ⊕ Bool) := (List.finRange n).map Sum.inl

/-- The graph asks for exactly `n` 16-byte digests at each of its two output rows. -/
@[expose] def digests (n : Nat) (vs : List Word) : Vector Digest n :=
  Vector.ofFn fun i => ofBV 16 (vs[i.val]?.getD 0)

private theorem digests_injective {n : Nat} {vs ws : List Word} (hv : vs.length = n)
    (hw : ws.length = n) (same : digests n vs = digests n ws) : vs = ws := by
  apply List.ext_getElem (hv.trans hw.symm)
  intro i hi hj
  have bound : i < n := by omega
  have slot (xs : List Word) :
      (digests n xs)[i] = ofBV 16 (xs[i]?.getD 0) :=
    Vector.getElem_ofFn (f := fun j : Fin n => ofBV 16 (xs[j.val]?.getD 0)) bound
  have cell := (slot vs).symm.trans
    ((congrArg (fun ds : Vector Digest n => ds[i]) same).trans (slot ws))
  apply ofBV_inj (n := 16) (by decide)
  simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] at cell
  exact cell

/-- Physical bytes passed to the hash at the fixed address. -/
@[expose] def input (pp : PublicParam) (address : Address) (n : Nat) (vs : List Word) : HashInput :=
  (thInput pp address (packDigests (digests n vs))).data.toList

/-- At its proper arity, the full hash input determines every digest in order. -/
theorem input_injective {pp : PublicParam} {address : Address} {n : Nat} {vs ws : List Word}
    (hv : vs.length = n) (hw : ws.length = n)
    (same : input pp address n vs = input pp address n ws) :
    vs = ws := by
  have raw := ByteArray.ext (Array.toList_inj.mp same)
  have packed := (thInput_inj raw).2.2
  exact digests_injective hv hw
    (Vector.eq_iff_flatten_eq.mpr (EthLib.Base.packBytes_injective packed))

/-- The low and high row are the two outputs at exactly the same ordered digest vector. -/
def graph (pp : PublicParam) (address : Address) (n : Nat) :
    CanonicalGraph Public (Fin n) Bool Word where
  ch _ := children n
  pt row vs := if row then .inr (input pp address n vs) else .inl (input pp address n vs)
  range_eq _ _ := rfl
  pt_inj := by
    intro k k' vs ws hv hw same
    simp [children] at hv hw
    cases k <;> cases k' <;> simp at same
    all_goals exact ⟨rfl, input_injective hv hw same⟩

private def liftPublic (n : Nat) :
    QueryImpl (unifSpec + Public) (OracleComp (Public.withLabels (Fin n) Bool Word)) :=
  Sum.rec (fun j => query (spec := Public.withLabels (Fin n) Bool Word) (.inl (.inl (.inl j))))
    (fun b => query (spec := Public.withLabels (Fin n) Bool Word) (.inl (.inl (.inr b))))

/-- The full physical query under the same two-row translation used for chain steps. -/
def hash (n : Nat) (bytes : ByteArray) :
    OracleComp (Public.withLabels (Fin n) Bool Word) (Vector UInt8 32) :=
  simulateQ (liftPublic n)
    (simulateQ PairedHashWord.readHalves (queryH (m := OracleComp OracleWorld) bytes))

private theorem hash_eq (n : Nat) (bytes : ByteArray) : hash n bytes = (do
    let lo ← query (spec := Public.withLabels (Fin n) Bool Word)
      (.inl (.inl (.inr (.inl bytes.data.toList))))
    let hi ← query (spec := Public.withLabels (Fin n) Bool Word)
      (.inl (.inl (.inr (.inr bytes.data.toList))))
    pure (ofOutput (PairedHashWord.halves.symm (lo, hi)))) := by
  change simulateQ (liftPublic n) (simulateQ PairedHashWord.readHalves (ofOutput <$>
    (liftM (OracleWorld.query (.inr bytes.data.toList)) : OracleComp OracleWorld HashOutput))) = _
  simp [PairedHashWord.readHalves, RandomOraclePairedValue.readHalves, liftPublic, ← bind_pure_comp]

/-- Hashing the children reads the low output and touches the high output.

Both computations preserve the same reply and final caches. -/
theorem th_from_children (pp : PublicParam) (address : Address) (n : Nat) :
    simulateQ (graph pp address n).eagerImpl (do
      let vs ← (children n).mapM fun c => readCell (some c)
      th (hash n) pp address (packDigests (digests n vs))) =
    simulateQ (graph pp address n).eagerImpl (do
      forM (children n) fun c => touchCell (some c)
      let lo ← readCell (some (.inr false))
      touchCell (some (.inr true))
      pure (ofBV 16 lo)) := by
  let G := graph pp address n
  have eqn := congrArg (fun body => (fun p : Word × Word => ofBV 16 p.1) <$> body)
    (G.simulateQ_eagerImpl_siblings false true (children n) rfl rfl)
  simp only [th, hash_eq, bind_assoc, pure_bind, PairedHashWord.first_half_bytes,
    Equiv.apply_symm_apply]
  simp only [simulateQ_bind, simulateQ_pure, map_bind, map_pure,
    CanonicalGraph.simulateQ_eagerImpl_touchCell, bind_map_left] at eqn ⊢
  exact eqn

/-- In a leanXMSS leaf, `otsLeafHash` consumes all 58 chain ends in order. -/
theorem otsLeafHash_from_children (pp : PublicParam) (layer : Layer) (epoch : UInt32) :
    simulateQ (graph pp (addrLeaf layer epoch) V).eagerImpl (do
      let vs ← (children V).mapM fun c => readCell (some c)
      otsLeafHash (hash V) pp layer epoch (digests V vs)) =
    simulateQ (graph pp (addrLeaf layer epoch) V).eagerImpl (do
      forM (children V) fun c => touchCell (some c)
      let lo ← readCell (some (.inr false))
      touchCell (some (.inr true))
      pure (ofBV 16 lo)) :=
  th_from_children pp (addrLeaf layer epoch) V

/-- The leaf hash consumes the ordered digests returned by the previous reads.

The final cache records each digest at its child. -/
theorem otsLeafHash_after_endpoints (pp : PublicParam) (layer : Layer) (epoch : UInt32)
    (initial : RelabelState Public (Fin V) Bool Word)
    {z : List Word × RelabelState Public (Fin V) Bool Word}
    (run : z ∈ support ((simulateQ (graph pp (addrLeaf layer epoch) V).eagerImpl
      ((children V).mapM fun c => readCell (some c))).run initial)) :
    (simulateQ (graph pp (addrLeaf layer epoch) V).eagerImpl
      (otsLeafHash (hash V) pp layer epoch (digests V z.1))).run z.2 =
    (simulateQ (graph pp (addrLeaf layer epoch) V).eagerImpl (do
      let lo ← readCell (some (.inr false))
      touchCell (some (.inr true))
      pure (ofBV 16 lo))).run z.2 := by
  let G := graph pp (addrLeaf layer epoch) V
  have recorded := (G.readCells_recorded (children V) initial run).2
  have ready (row : Bool) : G.childVals z.2 row = some z.1 := G.childVals_eq_some_iff.mpr recorded
  have eqn := congrArg
    (fun body => (fun p : (Word × Word) × RelabelState Public (Fin V) Bool Word =>
      (ofBV 16 p.1.1, p.2)) <$> body)
    (G.eagerImpl_siblings_run_of_childVals false true z.1 z.2 (ready false) (ready true))
  simp only [otsLeafHash, th, hash_eq, bind_assoc, pure_bind, PairedHashWord.first_half_bytes,
    Equiv.apply_symm_apply]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
    CanonicalGraph.simulateQ_eagerImpl_touchCell, bind_map_left] at eqn ⊢
  exact eqn

private theorem pack_pair (ds : Vector Digest 2) :
    packDigests ds = packBytes ds[0] ++ packBytes ds[1] := by
  have pair : ds = #v[ds[0]].push ds[1] := by
    apply Vector.ext
    intro i hi
    have choices : i = 0 ∨ i = 1 := by omega
    rcases choices with rfl | rfl <;> simp
  calc
    packDigests ds = packDigests (#v[ds[0]].push ds[1]) := congrArg packDigests pair
    _ = _ := by
      rw [packDigests, Vector.flatten_push, Vector.flatten_singleton]
      apply ByteArray.ext
      simp [EthLib.Base.packBytes, ByteArray.data_append]

/-- The same ordered-child rule at arity two reads the Merkle payload left before right. -/
theorem nodeHash_from_children (pp : PublicParam) (layer : Layer) (p : Merkle.Position) :
    let a := addrNode layer (Fin.ofNat _ p.level) (UInt32.ofNat p.index)
    simulateQ (graph pp a 2).eagerImpl (do
      let vs ← (children 2).mapM fun c => readCell (some c)
      let ds := digests 2 vs
      nodeHash (hash 2) pp layer p ds[0] ds[1]) =
    simulateQ (graph pp a 2).eagerImpl (do
      forM (children 2) fun c => touchCell (some c)
      let lo ← readCell (some (.inr false))
      touchCell (some (.inr true))
      pure (ofBV 16 lo)) := by
  simpa only [nodeHash, ← pack_pair] using
    th_from_children pp (addrNode layer (Fin.ofNat _ p.level) (UInt32.ofNat p.index)) 2

end EthLib.Cryptography.Xmss.Unforgeability.VCV.LeafGraph

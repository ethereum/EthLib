module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CanonicalOpening
public import EthLib.Cryptography.Proofs.Merkle.Position

/-!
# Recovering the authentication path

The leanXMSS draft, section "Trees", assigns each sibling a level and a global index.

An accepting climb to a recorded root fixes the leaf and each submitted sibling at those positions.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe

open EthLib.Cryptography OracleSpec OracleComp Constants HashSig TwoLayerGraph
open ChainGraph (Word digestEquiv)

/-- The low label at this layer, level and index contains the given digest. -/
def AtPosition (st : Honest.SharedState) (l : Layer) (p : Merkle.Position) (d : Digest) : Prop :=
  st.2 (.inr (.inl (l, LayerGraph.treeRole p.level p.index))) = some (digestEquiv d)

/-- A successful binary hash whose result matches its stored parent fixes both children. -/
theorem node_children (pp : PublicParam) (st : Honest.SharedState) (l : Layer)
    (h j : Nat) (within : h < LAYER_HEIGHT) (a b d : Digest)
    (safe : ¬(keys pp).TCHazard ((subgraph pp).project st))
    (label : AtPosition st l ⟨h + 1, j⟩ d)
    (read : nodeHash (hashAt pp st) pp l ⟨h + 1, j⟩ a b = some d) :
    AtPosition st l ⟨h, 2 * j⟩ a ∧ AtPosition st l ⟨h, 2 * j + 1⟩ b := by
  let r := LayerGraph.treeRole (h + 1) j
  let vs := [digestEquiv a, digestEquiv b]
  have raw := LayerGraph.node_input pp l h j within a b
  have width : vs.length = LayerGraph.arity r := by
    rw [show r = _ from LayerGraph.treeRole_succ h j within]
    rfl
  -- The node's ordered digest pair is exactly the payload read by the native verifier.
  rw [nodeHash, th] at read
  obtain ⟨w, readWord, eqn⟩ := Option.bind_eq_some_iff.mp read
  have same : halfOf 0 w = d := Option.some.inj eqn
  have physical := low_of_hashAt _ _ _ _ readWord
  rw [same] at physical
  have stored := matched_children pp st (l, r) vs (digestEquiv d) safe width label
    (by
      change (graph pp).merge st (.inl (LayerGraph.input pp l r vs)) = _
      rw [raw]
      exact physical)
  have values := (graph pp).childVals_eq_some_iff.mp stored
  change List.Forall₂ _ ((LayerGraph.children r).map (inLayer l)) vs at values
  rw [show LayerGraph.children r = _ from LayerGraph.treeRole_children h j within] at values
  exact ⟨values.get (i := 0) (by change 0 < 2; decide) (by change 0 < 2; decide),
    values.get (i := 1) (by change 1 < 2; decide) (by change 1 < 2; decide)⟩

/-- A successful climb fixes the starting digest and each submitted sibling. -/
theorem climb_opening (pp : PublicParam) (st : Honest.SharedState) (l : Layer)
    (safe : ¬(keys pp).TCHazard ((subgraph pp).project st)) (siblings : List Digest)
    (p : Merkle.Position) (current root : Digest)
    (within : p.level + siblings.length ≤ LAYER_HEIGHT)
    (run : Merkle.climb (nodeHash (hashAt pp st) pp l) p current siblings = some root)
    (anchor : AtPosition st l (p.ancestor siblings.length) root) :
    AtPosition st l p current ∧ ∀ i : Fin siblings.length,
      AtPosition st l (p.ancestor i.val).sibling siblings[i.val] := by
  induction siblings generalizing p current with
  | nil =>
    have eqn : current = root := Option.some.inj run
    exact ⟨by simpa [eqn] using anchor, fun i => Fin.elim0 i⟩
  | cons sibling rest ih =>
    rw [Merkle.climb] at run
    obtain ⟨parent, hashParent, up⟩ := Option.bind_eq_some_iff.mp run
    have bound : p.level < LAYER_HEIGHT := by simp only [List.length_cons] at within; omega
    obtain ⟨known, higher⟩ := ih p.parent parent
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using within)
      up (by simpa using anchor)
    -- Undo the verifier's choice of left and right before recovering the named sibling.
    have pair := node_children pp st l p.level p.parent.index bound _ _ parent safe known hashParent
    have both : AtPosition st l p current ∧ AtPosition st l p.sibling sibling := by
      cases side : p.isLeft with
      | true =>
        have even := (Merkle.Position.isLeft_iff p).mp side
        have here : 2 * p.parent.index = p.index := by
          simp only [Merkle.Position.parent_index]
          omega
        have other : 2 * p.parent.index + 1 = p.sibling.index := by
          rw [here, Merkle.Position.sibling_index, Merkle.xor_one_of_even even]
        have curPos : (⟨p.level, 2 * p.parent.index⟩ : Merkle.Position) = p :=
          Merkle.Position.ext rfl here
        have sibPos : (⟨p.level, 2 * p.parent.index + 1⟩ : Merkle.Position) = p.sibling :=
          Merkle.Position.ext rfl other
        rwa [curPos, sibPos, Merkle.ordered, side, ite_eq_left rfl] at pair
      | false =>
        have odd := (Merkle.Position.isLeft_eq_false_iff p).mp side
        have here : 2 * p.parent.index + 1 = p.index := by
          simp only [Merkle.Position.parent_index]
          omega
        have other : 2 * p.parent.index = p.sibling.index := by
          rw [Merkle.Position.sibling_index, Merkle.xor_one_of_odd odd]; omega
        have curPos : (⟨p.level, 2 * p.parent.index + 1⟩ : Merkle.Position) = p :=
          Merkle.Position.ext rfl here
        have sibPos : (⟨p.level, 2 * p.parent.index⟩ : Merkle.Position) = p.sibling :=
          Merkle.Position.ext rfl other
        rw [curPos, sibPos, Merkle.ordered, side, ite_eq_right (by decide)] at pair
        exact pair.symm
    refine ⟨both.1, fun i => ?_⟩
    refine Fin.cases (by simpa using both.2) (fun k => ?_) i
    simpa using higher k

end EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe

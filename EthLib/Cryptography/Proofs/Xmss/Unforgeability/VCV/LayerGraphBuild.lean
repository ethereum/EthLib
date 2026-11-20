module

public import EthLib.Cryptography.Proofs.Merkle.Build
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphLeaf

/-!
# Authentication paths from the tree stored by the signer

The leanXMSS draft, section "The scheme", returns the bottom tree path and its signed root.
EthLib builds that tree once and reads its paths without further oracle calls.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

open Constants OracleComp Merkle

/-- The stored tree gives the recorded root and every sibling of each leaf in its subtree. -/
@[expose] def BuildRecorded (level index : Nat) (tree : Built Digest) (st : State) : Prop :=
  Recorded (treeRole level index) tree.value st ∧
  ∀ e, e / 2 ^ level = index → ∀ k : Fin level,
    Recorded (treeRole k.val ((e / 2 ^ k.val) ^^^ 1)) ((tree.path level e)[k.val]'k.isLt) st

theorem BuildRecorded.mono {l j : Nat} {t : Built Digest} {s u : State}
    (old : BuildRecorded l j t s) (ext : s ≤ u) : BuildRecorded l j t u :=
  ⟨ext.2 old.1, fun e eq k => ext.2 (old.2 e eq k)⟩

private theorem parent_recorded {l j : Nat} {a b : Built Digest} {d : Digest} {s : State}
    (left : BuildRecorded l (2 * j) a s) (right : BuildRecorded l (2 * j + 1) b s)
    (root : Recorded (treeRole (l + 1) j) d s) :
    BuildRecorded (l + 1) j (.node d a b) s := by
  refine ⟨root, ?_⟩
  intro e tree k
  have half : e / 2 ^ l / 2 = j := (div_pow_div_two e l).trans tree
  rw [Built.path]
  by_cases even : e / 2 ^ l % 2 = 0
  · have side : e / 2 ^ l = 2 * j := by omega
    rw [ite_eq_left even, Vector.getElem_push]
    split
    · exact left.2 e side ⟨k.val, by omega⟩
    · have atTop : k.val = l := by omega
      rw [atTop, xor_one_of_even even, side]
      exact right.1
  · have side : e / 2 ^ l = 2 * j + 1 := by omega
    rw [ite_eq_right even, Vector.getElem_push]
    split
    · exact right.2 e side ⟨k.val, by omega⟩
    · have atTop : k.val = l := by omega
      rw [atTop, xor_one_of_odd (by omega : e / 2 ^ l % 2 = 1), side, Nat.add_sub_cancel]
      exact left.1

/-- Every supported return of the given computation has a tree recorded in its final cache. -/
@[expose] def ProducesBuild (pp : PublicParam) (layer : Layer) (l j : Nat) (op : OracleComp Spec (Built Digest)) : Prop :=
  ∀ (st : State) (z : Built Digest × State),
    z ∈ support ((simulateQ (graph pp layer).eagerImpl op).run st) → BuildRecorded l j z.1 z.2

private theorem build_leaf (pp : PublicParam) (layer : Layer) (j : Nat)
    (op : OracleComp Spec Digest) (ready : Settles pp layer (treeRole 0 j) op) :
    ProducesBuild pp layer 0 j (do let d ← op; pure (Built.leaf d)) := by
  intro st z run
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨d, hd, rfl⟩ := run
  exact ⟨ready st d hd, fun _ _ i => Fin.elim0 i⟩

private theorem build_parent (pp : PublicParam) (layer : Layer) (l j : Nat) (bound : l < LAYER_HEIGHT)
    (left right : OracleComp Spec (Built Digest))
    (hl : ProducesBuild pp layer l (2*j) left) (hr : ProducesBuild pp layer l (2*j+1) right) :
    ProducesBuild pp layer (l+1) j (do
      let a ← left
      let b ← right
      let d ← nodeHash hash pp layer ⟨l+1,j⟩ a.value b.value
      return .node d a b) := by
  intro st z hz
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨a, ha, b, hb, d, hd, rfl⟩ := hz
  have leftDone := (hl st a ha).mono (state_extends pp layer right a.2 hb)
  have rightDone := hr a.2 b hb
  have afterHash := state_extends pp layer _ b.2 hd
  rw [nodeHash_of_recorded pp layer l j bound a.1.value b.1.value b.2
    leftDone.1 rightDone.1] at hd
  exact parent_recorded (leftDone.mono afterHash) (rightDone.mono afterHash)
    (readOutput_recorded pp layer _ b.2 hd)

/-- Every supported execution of the signer's actual tree build records all of its paths.
Later updates to the graph preserve the root and every one of these path coordinates. -/
theorem build_recorded (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec)) :
    ∀ l j, l ≤ LAYER_HEIGHT → ProducesBuild pp layer l j
      (Xmss.build hash pp (startPrf pp layer other) layer l j) := by
  intro l
  induction l with
  | zero =>
    intro j _
    rw [Xmss.build, build_zero]
    exact build_leaf pp layer j _ (otsPublicLeaf_settles pp layer other (UInt32.ofNat j))
  | succ l ih =>
    intro j h
    rw [Xmss.build, build_succ]
    exact build_parent pp layer l j (by omega) _ _
      (ih (2*j) (by omega)) (ih (2*j+1) (by omega))

end EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

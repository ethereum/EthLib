module

public import EthLib.Cryptography.Proofs.Vrf.Unpredictability
public import EthLib.Cryptography.Proofs.EvalDistEq
public import EthLib.Cryptography.Proofs.LogKeys

/-!
# Proofs: a mixed selection cannot be ground

A protocol selects a holder when the mixed value of an output falls in a target set.

The mix hashes the output with randomness that becomes known after the holder registers its root.

Here the holder chooses every secret of its tree, so it chooses every output.

It may query the mix before the randomness is drawn, then open any index of a set fixed in advance.

The mix is a random oracle, and the tree hash is Keccak-256 itself.

A mixed value of the registered tree lands in the target set with a probability bounded by a sum.

- The number of allowed indices times the size of the target set, over `2^256`.
- The number of mix queries before the randomness, over `2^256`.
- The chance that the opening and the honest opening at its index expose a Keccak-256 collision.

The collision is the one the search of the uniqueness theorem returns.

The theorem covers a holder that registers a tree whose secrets it chose.

It does not cover a holder that registers a root without knowing a tree under it.

The randomness is uniform and independent of the holder.

So the theorem does not cover randomness that the holder knows at registration, or can bias.

The game is EthLib's own: it bounds what a selection needs, for a holder that chose its key.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open OracleSpec OracleComp ENNReal

/-! ## The mix as an oracle -/

/-- The mix as an oracle: an output and a randomness in, a 32-byte value out. -/
abbrev MixSpec := Digest × Digest →ₒ Digest

/-- What a holder may query: private uniform sampling, and the mix. -/
abbrev HolderSpec := unifSpec + MixSpec

/-- A query of a holder to the mix. -/
def IsMixQuery : HolderSpec.Domain → Prop
  | .inr _ => True
  | .inl _ => False

instance : DecidablePred IsMixQuery := fun t => by
  rcases t with _ | _ <;> simp only [IsMixQuery] <;> infer_instance

/-- The mix of the specification as a table: the value at a randomness and an output. -/
def mixTable (randomness output : Digest) : Digest :=
  mixOutput output randomness

/-- Answer the mix from a table, read at the randomness, then at the output.

Sampling passes through. -/
def tableImpl (table : Digest → Digest → Digest) : QueryImpl HolderSpec ProbComp
  | .inl n => unifSpec.query n
  | .inr x => pure (table x.2 x.1)

/-- With the table of the specification, a mix query is answered with the specified mixed value. -/
theorem tableImpl_mixTable (y r : Digest) :
    tableImpl mixTable (.inr (y, r)) = pure (mixOutput y r) :=
  rfl

/-! ## The game -/

/-- A holder that registers a tree, then opens it once the randomness is known. -/
structure SelectionAdversary (σ : Type) where
  /-- Choose every secret of the tree, and keep a state. -/
  commit : OracleComp HolderSpec ((UInt32 → Digest) × σ)
  /-- From the state and the randomness, return an index and an opening there. -/
  reveal : σ → Digest → OracleComp HolderSpec (UInt32 × Opening)

/-- What a run of the game produces. -/
structure Selection where
  /-- The table of the mix. -/
  table : Digest → Digest → Digest
  /-- The secrets of the registered tree. -/
  secrets : UInt32 → Digest
  /-- The randomness, drawn after the tree is registered. -/
  randomness : Digest
  /-- The index the holder opens. -/
  index : UInt32
  /-- The opening it returns there. -/
  revealed : Opening

/-- One run: a uniform mix table, the registered tree, the randomness, then the opening. -/
noncomputable def selectionRun {σ : Type} (adversary : SelectionAdversary σ) :
    ProbComp Selection := do
  let table ← $ᵗ (Digest → Digest → Digest)
  let c ← simulateQ (tableImpl table) adversary.commit
  let randomness ← $ᵗ Digest
  let x ← simulateQ (tableImpl table) (adversary.reveal c.2 randomness)
  return ⟨table, c.1, randomness, x.1, x.2⟩

/-- A run is selected when its opening verifies under the root of the registered tree.

The index must be in `I`, and the mixed value of the output must be in `S`.

The mixed value of an output `y` under a randomness `r` is read in the table at `r`, then `y`. -/
def Selection.Selected (I : Finset UInt32) (S : Finset Digest) (z : Selection) : Prop :=
  z.index ∈ I ∧ ∃ y, verify (root z.secrets) z.index z.revealed = some y ∧
    z.table z.randomness y ∈ S

/-- With the table of the specification, a run is selected exactly when the protocol selects it.

That is, the opening verifies at an index of `I`, and the specified mixed value is in `S`. -/
theorem Selection.selected_iff_mixOutput {I : Finset UInt32} {S : Finset Digest} {z : Selection}
    (h : z.table = mixTable) :
    z.Selected I S ↔ z.index ∈ I ∧ ∃ y, verify (root z.secrets) z.index z.revealed = some y ∧
      mixOutput y z.randomness ∈ S := by
  rw [Selection.Selected, h]
  rfl

/-- The opening and the honest opening of the registered tree expose a Keccak-256 collision.

The opening need not verify: every pair the search returns is a collision. -/
def Selection.Collides (z : Selection) : Prop :=
  (findHashCollision z.index z.revealed (opening z.secrets z.index)).isSome

/-! ## The bound -/

/-- A uniform 32-byte value lands in a set with its share of the `2^256` values. -/
theorem prEvent_uniformSample_mem_digest (T : Finset Digest) :
    Pr{let r ← $ᵗ Digest}[r ∈ T] = T.card * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  classical
  rw [SampleableType.prEvent_uniformSample, Finset.filter_mem_eq_inter, Finset.univ_inter,
    ← Nat.card_eq_fintype_card, natCard_digest, div_eq_mul_inv]
  norm_num

/-- A uniform function, read at one point, lands in a set with its share of the values. -/
theorem prEvent_uniformFun_apply_mem (a : Digest) (T : Finset Digest) :
    Pr{let G ← $ᵗ (Digest → Digest)}[G a ∈ T] = T.card * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hu := evalDistEq_uniformSample_bind_update a
    (fun G : Digest → Digest => (pure (G a ∈ T) : ProbComp Prop))
  simp only [Function.update_self] at hu
  have h := ((EvalDistEq.bind_right ($ᵗ Digest) fun u =>
    (EvalDistEq.bind_const ($ᵗ (Digest → Digest)) (pure (u ∈ T) : ProbComp Prop)).symm).trans
    hu).prEvent_eq id
  rw [← prEvent_uniformSample_mem_digest]
  rw [bind_pure_comp, bind_pure_comp, prEvent_map, prEvent_map] at h
  exact h.symm

/-- A selected run mixes an honest output at an allowed index, or exposes a collision. -/
theorem Selection.Selected.honest_or_collides {I : Finset UInt32} {S : Finset Digest}
    {z : Selection}
    (h : z.Selected I S) :
    (∃ i ∈ I, z.table z.randomness (outputHash i (z.secrets i)) ∈ S) ∨ z.Collides := by
  obtain ⟨hI, y, hy, hS⟩ := h
  rcases verify_root_unique hy with rfl | ⟨p, hp, -⟩
  · exact .inl ⟨z.index, hI, hS⟩
  · exact .inr (by rw [Selection.Collides, hp]; rfl)

/-- An honest output mixed into the target set is bounded before the reveal phase. -/
theorem prEvent_commit_mix_le {σ : Type} (commit : OracleComp HolderSpec ((UInt32 → Digest) × σ))
    (I : Finset UInt32) (S : Finset Digest) {q : ℕ} (hq : IsQueryBoundP commit IsMixQuery q) :
    Pr{let table ← $ᵗ (Digest → Digest → Digest)
       let c ← simulateQ (tableImpl table) commit
       let r ← $ᵗ Digest}[∃ i ∈ I, table r (outputHash i (c.1 i)) ∈ S] ≤
      (I.card * S.card : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  classical
  let key : HolderSpec.Domain → Option Digest := fun t =>
    Sum.elim (fun _ => none) (fun x => some x.2) t
  have hkey : ∀ t, ¬ IsMixQuery t → key t = none := by
    rintro (n | x) h
    · rfl
    · exact absurd trivial h
  have hrun : ∀ table, simulateQ (tableImpl table) commit =
      Prod.fst <$> (simulateQ (logKeys (tableImpl table) key) commit).run ∅ :=
    fun table => (fst_map_run_simulateQ_logKeys _ key commit ∅).symm
  obtain ⟨M, hM⟩ : ∃ M : ProbComp ((Digest → Digest → Digest) ×
      (((UInt32 → Digest) × σ) × Finset Digest) × Digest),
      M = $ᵗ (Digest → Digest → Digest) >>= fun table =>
        (simulateQ (logKeys (tableImpl table) key) commit).run ∅ >>= fun z =>
          $ᵗ Digest >>= fun r => pure (table, z, r) := ⟨_, rfl⟩
  have hgoal : Pr{let table ← $ᵗ (Digest → Digest → Digest)
                  let c ← simulateQ (tableImpl table) commit
                  let r ← $ᵗ Digest}[∃ i ∈ I, table r (outputHash i (c.1 i)) ∈ S] =
      Pr{let w ← M}[∃ i ∈ I, w.1 w.2.2 (outputHash i (w.2.1.1.1 i)) ∈ S] := by
    simp only [hM, hrun, bind_map_left, map_bind, bind_pure_comp, Functor.map_map]
  rw [hgoal]
  have hbad : Pr{let w ← M}[w.2.2 ∈ w.2.1.2] ≤ (q : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    rw [hM]
    refine prEvent_bind_le_of_forall_le_of_support (m := ProbComp) _ _ _ fun table _ => ?_
    refine prEvent_bind_le_of_forall_le_of_support (m := ProbComp) _ _ _ fun z hz => ?_
    rw [bind_pure_comp, prEvent_map]
    have hcard := card_le_of_mem_support_run_logKeys _ hkey hq ∅ hz
    rw [Finset.card_empty, zero_add] at hcard
    refine (prEvent_uniformSample_mem_digest z.2).trans_le ?_
    gcongr
  have hgood : Pr{let w ← M}[(∃ i ∈ I, w.1 w.2.2 (outputHash i (w.2.1.1.1 i)) ∈ S) ∧
      w.2.2 ∉ w.2.1.2] ≤ (I.card * S.card : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    have hswap : M =ᵈ ($ᵗ Digest >>= fun r => $ᵗ (Digest → Digest → Digest) >>= fun table =>
        (simulateQ (logKeys (tableImpl table) key) commit).run ∅ >>= fun z =>
          (pure (table, z, r) : ProbComp _)) := by
      rw [hM]
      exact (EvalDistEq.bind_right _ fun table => EvalDistEq.bind_bind_swap _ _ _).trans
        (EvalDistEq.bind_bind_swap _ _ _)
    rw [hswap.prEvent_eq]
    refine prEvent_bind_le_of_forall_le_of_support (m := ProbComp) _ _ _ fun r _ => ?_
    rw [← (evalDistEq_uniformSample_bind_update r fun table =>
      (simulateQ (logKeys (tableImpl table) key) commit).run ∅ >>= fun z =>
        (pure (table, z, r) : ProbComp _)).prEvent_eq]
    calc _ ≤ Pr{let w ← $ᵗ (Digest → Digest) >>= fun G =>
          ($ᵗ (Digest → Digest → Digest) >>= fun table => simulateQ (tableImpl table) commit) >>=
            fun c => (pure (G, c) : ProbComp _)}[
          ∃ i ∈ I, w.1 (outputHash i (w.2.1 i)) ∈ S] := by
          refine prEvent_bind_mono_of_forall_le (m := ProbComp) _ _ _ _ _ fun G => ?_
          rw [bind_assoc]
          refine prEvent_bind_mono_of_forall_le (m := ProbComp) _ _ _ _ _ fun table => ?_
          rw [bind_pure_comp, bind_pure_comp, prEvent_map, prEvent_map]
          simp only [Function.update_self]
          refine prEvent_run_logKeys_le (impl₂ := tableImpl table) ?_ commit ∅
            fun c => ∃ i ∈ I, G (outputHash i (c.1 i)) ∈ S
          rintro (n | x) hx
          · rfl
          · have hx2 : x.2 ≠ r := fun h => hx (by simp [key, h])
            simp only [tableImpl, Function.update_of_ne hx2]
      _ ≤ _ := by
          rw [(EvalDistEq.bind_bind_swap ($ᵗ (Digest → Digest)) _
            fun G c => (pure (G, c) : ProbComp _)).prEvent_eq]
          refine prEvent_bind_le_of_forall_le_of_support (m := ProbComp) _ _ _ fun c _ => ?_
          rw [bind_pure_comp, prEvent_map, mul_assoc]
          refine prEvent_exists_finset_le_card_mul I _ _ fun i _ => ?_
          exact (prEvent_uniformFun_apply_mem (outputHash i (c.1 i)) S).le
  calc _ ≤ Pr{let w ← M}[((∃ i ∈ I, w.1 w.2.2 (outputHash i (w.2.1.1.1 i)) ∈ S) ∧
        w.2.2 ∉ w.2.1.2) ∨ w.2.2 ∈ w.2.1.2] :=
        prEvent_mono _ _ _ fun w h => by
          by_cases hw : w.2.2 ∈ w.2.1.2
          · exact .inr hw
          · exact .inl ⟨h, hw⟩
    _ ≤ _ := (prEvent_or_le _ _ _).trans (add_le_add hgood hbad)

/-- The reveal phase does not change an event of the table, the secrets and the randomness. -/
theorem prEvent_selectionRun_honest_le {σ : Type} (adversary : SelectionAdversary σ)
    (I : Finset UInt32) (S : Finset Digest) :
    Pr{let z ← selectionRun adversary}[
        ∃ i ∈ I, z.table z.randomness (outputHash i (z.secrets i)) ∈ S] ≤
      Pr{let table ← $ᵗ (Digest → Digest → Digest)
         let c ← simulateQ (tableImpl table) adversary.commit
         let r ← $ᵗ Digest}[∃ i ∈ I, table r (outputHash i (c.1 i)) ∈ S] := by
  unfold selectionRun
  simp only [map_bind, map_pure]
  refine prEvent_bind_mono_of_support _ _ _ fun table _ => ?_
  refine prEvent_bind_mono_of_support _ _ _ fun c _ => ?_
  rw [map_eq_bind_pure_comp]
  refine prEvent_bind_mono_of_support _ _ _ fun r _ => ?_
  exact (OracleComp.prEvent_bind_const _ _).le

/-- **A mixed selection cannot be ground.**

The mix is a uniformly random table, and the tree hash is Keccak-256.

The holder chooses all its secrets, and makes at most `q` mix queries before the randomness.

The randomness is uniform, and the holder then opens one index of `I`.

The mixed value of its output lands in `S` with probability at most the sum of three terms.

- `|I| |S| / 2^256`: one fresh uniform value per allowed index.
- `q / 2^256`: a mix query that already used the randomness.
- The chance that the search returns a collision, with the opening and the honest opening.

With one index, `|S| = 2^200` and `q = 2^64`, the first two terms are below `2^-55`. -/
theorem prEvent_selected_le {σ : Type} (adversary : SelectionAdversary σ) (I : Finset UInt32)
    (S : Finset Digest) {q : ℕ} (hq : IsQueryBoundP adversary.commit IsMixQuery q) :
    Pr{let z ← selectionRun adversary}[z.Selected I S] ≤
      (I.card * S.card : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
        Pr{let z ← selectionRun adversary}[z.Collides] := by
  calc _ ≤ Pr{let z ← selectionRun adversary}[
          (∃ i ∈ I, z.table z.randomness (outputHash i (z.secrets i)) ∈ S) ∨ z.Collides] :=
        prEvent_mono _ _ _ fun _ h => Selection.Selected.honest_or_collides h
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := add_le_add ((prEvent_selectionRun_honest_le adversary I S).trans
        (prEvent_commit_mix_le adversary.commit I S hq)) le_rfl

end EthLib.Cryptography.Vrf

module

public import EthLib.Cryptography.Xmss.Sign
public import EthLib.Cryptography.Xmss.Verify
public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import EthLib.Cryptography.Proofs.Merkle.QueryBound
public import EthLib.Cryptography.Proofs.Xmss.Ots
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Proofs: how many calls the leanXMSS algorithms make

Each call of `H` and of the seed function counts at most 1.

Then each algorithm makes at most a fixed number of counted calls.

- A tree at level 16 takes at most `205 * 2^16 - 1` calls.
- A one-time signature takes at most `2^32 + 204` calls.
- Verification takes at most `384` calls.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open OracleSpec OracleComp
open EthLib.Cryptography.Xmss.Constants

/-! ## Loops -/

section Loops

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]

/-- Computing `k` entries in order costs `k` times the cost of one. -/
theorem isQueryBoundP_ofFnInOrder {α : Type} {n : Nat} :
    ∀ (k : Nat) (f : Fin k → OracleComp spec α), (∀ i, IsQueryBoundP (f i) p n) →
      IsQueryBoundP (HashSig.ofFnInOrder k f) p (k * n)
  | 0, _, _ => isQueryBoundP_pure _ _ _
  | k + 1, f, h => by
    rw [HashSig.ofFnInOrder_succ]
    refine (isQueryBoundP_bind (h 0) fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_ofFnInOrder k _ fun i => h i.succ)
        fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
    rw [Nat.succ_mul]
    omega

/-- A walk of `steps` steps costs at most `steps`, when each step costs at most 1. -/
theorem isQueryBoundP_chain {α : Type} {k : Nat} (step : Fin k → α → OracleComp spec α)
    (hstep : ∀ i v, IsQueryBoundP (step i v) p 1) (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ k) (value : α),
      IsQueryBoundP (Wots.chain step start steps h value) p steps
  | 0, _, _ => isQueryBoundP_pure _ _ _
  | s + 1, h, value => by
    rw [Wots.chain_succ]
    exact isQueryBoundP_bind (isQueryBoundP_chain step hstep start s _ value) fun _ _ =>
      hstep _ _

/-- A search of `fuel` trials costs at most `fuel`, when each test costs at most 1. -/
theorem isQueryBoundP_findFirst {κ β : Type} (trial : Nat → κ)
    (test : κ → OracleComp spec (Option β)) (htest : ∀ k, IsQueryBoundP (test k) p 1) :
    ∀ (c fuel : Nat), IsQueryBoundP (Wots.findFirst trial test c fuel) p fuel
  | _, 0 => isQueryBoundP_pure _ _ _
  | c, fuel + 1 => by
    rw [Wots.findFirst]
    refine (isQueryBoundP_bind (htest _) fun r _ => ?_).mono (by omega : 1 + fuel ≤ fuel + 1)
    cases r with
    | none => exact isQueryBoundP_findFirst trial test htest (c + 1) fuel
    | some x => exact isQueryBoundP_pure _ _ _

/-! ## Merkle trees -/

section Merkle

variable {α : Type} {hash : Merkle.Position → α → α → OracleComp spec α}
  {leaves : Nat → OracleComp spec α} {c : Nat}

/-- A node at `level` costs its `2^level` leaves of cost `c` and its `2^level - 1` hashes. -/
theorem isQueryBoundP_merkleNode (hleaves : ∀ j, IsQueryBoundP (leaves j) p c)
    (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) :
    ∀ q : Merkle.Position,
      IsQueryBoundP (Merkle.node hash leaves q) p (2 ^ q.level * (c + 1) - 1) := by
  rintro ⟨level, j⟩
  induction level generalizing j with
  | zero => exact (hleaves j).mono (by simp)
  | succ level ih =>
    rw [Merkle.node_succ]
    have h1 : 1 ≤ 2 ^ level * (c + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : 2 ^ (level + 1) * (c + 1) = 2 * (2 ^ level * (c + 1)) := by ring
    refine (isQueryBoundP_bind (ih _) fun _ _ =>
      isQueryBoundP_bind (ih _) fun _ _ => hhash _ _ _).mono ?_
    simp only at h1 h2 ⊢
    omega

/-- A build at `level` costs as the node at its position. -/
theorem isQueryBoundP_merkleBuild (hleaves : ∀ j, IsQueryBoundP (leaves j) p c)
    (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) (q : Merkle.Position) :
    IsQueryBoundP (Merkle.build hash leaves q) p (2 ^ q.level * (c + 1) - 1) :=
  isQueryBoundP_merkleNode
    (fun j => (isQueryBoundP_bind (m := 0) (hleaves j) fun _ _ => isQueryBoundP_pure _ _ 0).mono
      (le_of_eq (Nat.add_zero _)))
    (fun _ _ _ => (isQueryBoundP_bind (m := 0) (hhash _ _ _) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (le_of_eq (Nat.add_zero _))) q

/-- The `n` siblings above a node at `level` cost the nodes they are. -/
theorem isQueryBoundP_merkleSiblings (hleaves : ∀ j, IsQueryBoundP (leaves j) p c)
    (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) :
    ∀ (q : Merkle.Position) (n : Nat), IsQueryBoundP (Merkle.siblings hash leaves q n) p
      (2 ^ (q.level + n) * (c + 1) - 2 ^ q.level * (c + 1))
  | q, 0 => by simp [Merkle.siblings]
  | q, n + 1 => by
    simp only [Merkle.siblings]
    have h1 : 1 ≤ 2 ^ q.level * (c + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : 2 ^ (q.level + 1) * (c + 1) = 2 * (2 ^ q.level * (c + 1)) := by ring
    have h3 : 2 ^ (q.level + 1) * (c + 1) ≤ 2 ^ (q.level + 1 + n) * (c + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4 : q.level + (n + 1) = q.level + 1 + n := by omega
    rw [h4]
    refine (isQueryBoundP_bind (isQueryBoundP_merkleNode hleaves hhash q.sibling) fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_merkleSiblings hleaves hhash q.parent n)
        fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
    simp only [Merkle.Position.sibling_level, Merkle.Position.parent_level]
    omega

end Merkle

end Loops

/-! ## The algorithms -/

attribute [local irreducible] LAYER_HEIGHT MAX_RANDOMIZER_TRIALS

section Algorithms

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
  {H : Array UInt64 → OracleComp spec Lanes4} {prf : SeedPrf (OracleComp spec)}

/-- A tweakable hash call is one call of `H`. -/
theorem isQueryBoundP_th (hH : ∀ x, IsQueryBoundP (H x) p 1) (publicParam : PublicParam)
    (address : Address) (payload : Array UInt64) :
    IsQueryBoundP (th H publicParam address payload) p 1 :=
  isQueryBoundP_bind (m := 0) (hH _) fun _ _ => isQueryBoundP_pure _ _ 0

/-- The starts of a key's chains are `29` derivations. -/
theorem isQueryBoundP_chainStarts (hprf : ∀ publicParam a suffix, IsQueryBoundP
    (prf publicParam a suffix) p 1)
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) :
    IsQueryBoundP (chainStarts publicParam prf layer e) p 29 :=
  isQueryBoundP_bind (m := 0) (isQueryBoundP_ofFnInOrder (V / 2) _ fun _ => hprf _ _ _)
    fun _ _ => isQueryBoundP_pure _ _ 0

/-- A walk of `steps` steps on a chain is `steps` calls of `H`. -/
theorem isQueryBoundP_xmssChain (hH : ∀ x, IsQueryBoundP (H x) p 1) (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    IsQueryBoundP (chain H publicParam layer e i start steps h value) p steps :=
  isQueryBoundP_chain _ (fun _ _ => isQueryBoundP_th hH _ _ _) _ _ _ _

/-- A key's leaf is `29` derivations, `174` chain steps and one hash. -/
theorem isQueryBoundP_otsPublicLeaf (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) :
    IsQueryBoundP (otsPublicLeaf H publicParam prf layer e) p 204 :=
  isQueryBoundP_bind (isQueryBoundP_chainStarts hprf publicParam layer e) fun _ _ =>
    isQueryBoundP_bind (isQueryBoundP_ofFnInOrder V _ fun _ =>
      isQueryBoundP_xmssChain hH _ _ _ _ _ _ _ _) fun _ _ => isQueryBoundP_th hH _ _ _

/-- A node at `level` is `2^level` leaves and `2^level - 1` hashes. -/
theorem isQueryBoundP_node (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (level j : Nat) :
    IsQueryBoundP (node H publicParam prf layer level j) p (2 ^ level * 205 - 1) :=
  isQueryBoundP_merkleNode (c := 204) (fun _ => isQueryBoundP_otsPublicLeaf hH hprf _ _ _)
    (fun _ _ _ => isQueryBoundP_th hH _ _ _) ⟨level, j⟩

/-- A build at `level` is `2^level` leaves and `2^level - 1` hashes. -/
theorem isQueryBoundP_build (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (level j : Nat) :
    IsQueryBoundP (build H publicParam prf layer level j) p (2 ^ level * 205 - 1) :=
  isQueryBoundP_merkleBuild (c := 204) (fun _ => isQueryBoundP_otsPublicLeaf hH hprf _ _ _)
    (fun _ _ _ => isQueryBoundP_th hH _ _ _) ⟨level, j⟩

/-- A key's path is the `16` nodes beside it, one per level. -/
theorem isQueryBoundP_path (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (e : Nat) :
    IsQueryBoundP (path H publicParam prf layer e) p (2 ^ 16 * 205 - 205) := by
  have h := isQueryBoundP_merkleSiblings (c := 204) (hash := nodeHash H publicParam layer)
    (leaves := leaves H publicParam prf layer)
      (fun _ => isQueryBoundP_otsPublicLeaf hH hprf publicParam layer _)
    (fun _ _ _ => isQueryBoundP_th hH publicParam _ _) ⟨0, e⟩ LAYER_HEIGHT
  unfold path Merkle.path
  exact h.mono (by simp [LAYER_HEIGHT])

/-- The public parameter is one derivation. -/
theorem isQueryBoundP_publicParamOf
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1) :
    IsQueryBoundP (publicParamOf prf) p 1 :=
  isQueryBoundP_bind (m := 0) (hprf _ _ _) fun _ _ => isQueryBoundP_pure _ _ 0

/-- The base of the randomizer trials is one derivation. -/
theorem isQueryBoundP_randomizerBase
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) (msg : Array UInt64) :
    IsQueryBoundP (randomizerBase publicParam prf layer e msg) p 1 :=
  isQueryBoundP_bind (m := 0) (hprf _ _ _) fun _ _ => isQueryBoundP_pure _ _ 0

/-- The codeword search is one digest per trial. -/
theorem isQueryBoundP_findCodeword (hH : ∀ x, IsQueryBoundP (H x) p 1) (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) (msg : Array UInt64) (base : Randomizer) (c fuel : Nat) :
    IsQueryBoundP (Internal.findCodeword H publicParam layer e msg base c fuel) p fuel := by
  rw [Internal.findCodeword_eq]
  exact isQueryBoundP_findFirst _ _ (fun _ => (isQueryBoundP_map_iff _ _ _).2
    (isQueryBoundP_th hH _ _ _)) c fuel

/-- A one-time signature is the base, at most `2^32` trials, the starts and `174` steps. -/
theorem isQueryBoundP_otsSign (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) (msg : Array UInt64) :
    IsQueryBoundP (otsSign H publicParam prf layer e msg) p (2 ^ 32 + 204) := by
  unfold otsSign Internal.otsSignTrials
  refine (isQueryBoundP_bind
    (isQueryBoundP_randomizerBase hprf publicParam layer e msg) fun base _ =>
    isQueryBoundP_bind (isQueryBoundP_findCodeword hH publicParam layer e msg base 0
      MAX_RANDOMIZER_TRIALS) fun r _ => ?_).mono (n := 1 + (MAX_RANDOMIZER_TRIALS + (29 + V * 3)))
    (by simp [MAX_RANDOMIZER_TRIALS, V])
  rcases r with _ | ⟨rho, x⟩
  · exact isQueryBoundP_pure _ _ _
  · refine (isQueryBoundP_bind (isQueryBoundP_chainStarts hprf publicParam layer e) fun starts _ =>
      isQueryBoundP_bind (isQueryBoundP_ofFnInOrder (n := 3) V _ fun i =>
        (isQueryBoundP_xmssChain hH publicParam layer e i 0 x[i] _ starts[i]).mono (m := 3) ?_)
        fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)
    have := x[i].isLt
    simp only [CHAIN_LENGTH] at this
    omega

/-- The leaf of a one-time signature is a digest, at most `174` steps and one hash. -/
theorem isQueryBoundP_otsLeaf (hH : ∀ x, IsQueryBoundP (H x) p 1) (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) (msg : Array UInt64) (rho : Randomizer) (y : Vector Digest V) :
    IsQueryBoundP (otsLeaf H publicParam layer e msg rho y) p 176 := by
  unfold otsLeaf
  refine isQueryBoundP_bind (m := 175) (isQueryBoundP_th hH publicParam _ _) fun d _ => ?_
  rcases codeword? d with _ | x
  · exact isQueryBoundP_pure _ _ _
  · refine (isQueryBoundP_bind (isQueryBoundP_ofFnInOrder (n := 3) V _ fun i =>
      (isQueryBoundP_xmssChain hH publicParam layer e i _ _ _ y[i]).mono (m := 3)
        (by simp only [CHAIN_LENGTH]; omega))
      fun _ _ => isQueryBoundP_bind (m := 0) (isQueryBoundP_th hH publicParam _ _) fun _ _ =>
        isQueryBoundP_pure _ _ 0).mono (by simp [V])

/-- The root one layer's signature leads to is a leaf and a climb of `16` levels. -/
theorem isQueryBoundP_layerRoot (hH : ∀ x, IsQueryBoundP (H x) p 1) (publicParam : PublicParam)
    (layer : Layer) (e : Nat) (msg : Array UInt64) (sig : LayerSignature) :
    IsQueryBoundP (layerRoot H publicParam layer e msg sig) p 192 := by
  unfold layerRoot
  refine (isQueryBoundP_bind
    (isQueryBoundP_otsLeaf hH publicParam layer _ msg _ _) fun r _ => ?_).mono
    (n := 176 + (LAYER_HEIGHT + 0)) (by simp [LAYER_HEIGHT])
  rcases r with _ | leaf
  · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind ((Merkle.isQueryBoundP_climb
    (fun _ _ _ => isQueryBoundP_th hH publicParam _ _)
      sig.path.toList ⟨0, e⟩ leaf).mono (by simp)) fun _ _ => isQueryBoundP_pure _ _ 0

/-- Verification is the roots of both layers. -/
theorem isQueryBoundP_verifyWith (hH : ∀ x, IsQueryBoundP (H x) p 1) (pk : PublicKey)
    (msg : Message) (sig : Signature) :
    IsQueryBoundP (verifyWith H pk msg sig) p 384 := by
  unfold verifyWith
  refine isQueryBoundP_bind (n := 192) (m := 192) (isQueryBoundP_layerRoot hH _ _ _ _ _)
    fun r _ => ?_
  rcases r with _ | bottomRoot
  · exact isQueryBoundP_pure _ _ _
  · refine (isQueryBoundP_bind (m := 0) (isQueryBoundP_layerRoot hH _ _ _ _ _) fun r _ => ?_).mono
      le_rfl
    rcases r with _ | root <;> exact isQueryBoundP_pure _ _ _

end Algorithms

end EthLib.Cryptography.Xmss

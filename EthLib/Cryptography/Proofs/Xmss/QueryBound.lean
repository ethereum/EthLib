module

public import EthLib.Cryptography.Xmss.Sign
public import EthLib.Cryptography.Xmss.Verify
public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Proofs: how many calls the leanXMSS algorithms make

Each call of `H` and of the seed function counts at most 1.

Then each algorithm makes at most a fixed number of counted calls.

- The public key takes at most `205 * 2^16` calls.
- A signature from the derivations takes at most `2^33 + 615 * 2^16 - 3` calls.
- Verification takes at most `384` calls.

A key's leaf takes `29` derivations, `174` chain steps and one hash, `204` calls in all.

A node at level `l` takes `2^l` leaves and `2^l - 1` hashes.
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
    rw [HashSig.ofFnInOrder]
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

variable {α : Type} {hash : Nat → Nat → α → α → OracleComp spec α}
  {leaves : Nat → OracleComp spec α} {c : Nat}

/-- A node at `level` costs its `2^level` leaves of cost `c` and its `2^level - 1` hashes. -/
theorem isQueryBoundP_merkleNode (hleaves : ∀ j, IsQueryBoundP (leaves j) p c)
    (hhash : ∀ l j a b, IsQueryBoundP (hash l j a b) p 1) :
    ∀ level j, IsQueryBoundP (Merkle.node hash leaves level j) p (2 ^ level * (c + 1) - 1)
  | 0, j => (hleaves j).mono (by simp)
  | level + 1, j => by
    rw [Merkle.node_succ]
    have h1 : 1 ≤ 2 ^ level * (c + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : 2 ^ (level + 1) * (c + 1) = 2 * (2 ^ level * (c + 1)) := by ring
    refine (isQueryBoundP_bind (isQueryBoundP_merkleNode hleaves hhash level _) fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_merkleNode hleaves hhash level _) fun _ _ =>
        hhash _ _ _ _).mono ?_
    omega

/-- The `n` siblings above a node at `level` cost the nodes they are. -/
theorem isQueryBoundP_merkleSiblings (hleaves : ∀ j, IsQueryBoundP (leaves j) p c)
    (hhash : ∀ l j a b, IsQueryBoundP (hash l j a b) p 1) :
    ∀ level j n, IsQueryBoundP (Merkle.siblings hash leaves level j n) p
      (2 ^ (level + n) * (c + 1) - 2 ^ level * (c + 1))
  | level, j, 0 => by simp [Merkle.siblings]
  | level, j, n + 1 => by
    simp only [Merkle.siblings]
    have h1 : 1 ≤ 2 ^ level * (c + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : 2 ^ (level + 1) * (c + 1) = 2 * (2 ^ level * (c + 1)) := by ring
    have h3 : 2 ^ (level + 1) * (c + 1) ≤ 2 ^ (level + 1 + n) * (c + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4 : level + (n + 1) = level + 1 + n := by omega
    rw [h4]
    refine (isQueryBoundP_bind (isQueryBoundP_merkleNode hleaves hhash level _) fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_merkleSiblings hleaves hhash (level + 1) (j / 2) n)
        fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
    omega

/-- A climb costs one hash per sibling. -/
theorem isQueryBoundP_climb (hhash : ∀ l j a b, IsQueryBoundP (hash l j a b) p 1) :
    ∀ (siblings : List α) (level j : Nat) (current : α),
      IsQueryBoundP (Merkle.climb hash level j current siblings) p siblings.length
  | [], _, _, _ => isQueryBoundP_pure _ _ _
  | _ :: rest, level, j, current => by
    rw [Merkle.climb]
    refine (isQueryBoundP_bind (hhash _ _ _ _) fun _ _ =>
      isQueryBoundP_climb hhash rest _ _ _).mono ?_
    simp only [List.length_cons]
    omega

end Merkle

end Loops

/-! ## The algorithms -/

attribute [local irreducible] LAYER_HEIGHT MAX_RANDOMIZER_TRIALS

section Algorithms

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
  {H : ByteArray → OracleComp spec (Vector UInt8 32)} {prf : SeedPrf (OracleComp spec)}

/-- A tweakable hash call is one call of `H`. -/
theorem isQueryBoundP_th (hH : ∀ x, IsQueryBoundP (H x) p 1) (pp : PublicParam)
    (address : Address) (payload : ByteArray) :
    IsQueryBoundP (th H pp address payload) p 1 :=
  isQueryBoundP_bind (m := 0) (hH _) fun _ _ => isQueryBoundP_pure _ _ 0

/-- The starts of a key's chains are `29` derivations. -/
theorem isQueryBoundP_chainStarts (hprf : ∀ pp a suffix, IsQueryBoundP (prf pp a suffix) p 1)
    (pp : PublicParam) (layer : Layer) (e : UInt32) :
    IsQueryBoundP (chainStarts pp prf layer e) p 29 :=
  isQueryBoundP_bind (m := 0) (isQueryBoundP_ofFnInOrder (V / 2) _ fun _ => hprf _ _ _)
    fun _ _ => isQueryBoundP_pure _ _ 0

/-- A walk of `steps` steps on a chain is `steps` calls of `H`. -/
theorem isQueryBoundP_xmssChain (hH : ∀ x, IsQueryBoundP (H x) p 1) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    IsQueryBoundP (chain H pp layer e i start steps h value) p steps :=
  isQueryBoundP_chain _ (fun _ _ => isQueryBoundP_th hH _ _ _) _ _ _ _

/-- A key's leaf is `29` derivations, `174` chain steps and one hash. -/
theorem isQueryBoundP_otsPublicLeaf (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ pp a suffix, IsQueryBoundP (prf pp a suffix) p 1) (pp : PublicParam)
    (layer : Layer) (e : UInt32) :
    IsQueryBoundP (otsPublicLeaf H pp prf layer e) p 204 :=
  isQueryBoundP_bind (isQueryBoundP_chainStarts hprf pp layer e) fun _ _ =>
    isQueryBoundP_bind (isQueryBoundP_ofFnInOrder V _ fun _ =>
      isQueryBoundP_xmssChain hH _ _ _ _ _ _ _ _) fun _ _ => isQueryBoundP_th hH _ _ _

/-- A node at `level` is `2^level` leaves and `2^level - 1` hashes. -/
theorem isQueryBoundP_node (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ pp a suffix, IsQueryBoundP (prf pp a suffix) p 1) (pp : PublicParam)
    (layer : Layer) (level j : Nat) :
    IsQueryBoundP (node H pp prf layer level j) p (2 ^ level * 205 - 1) :=
  isQueryBoundP_merkleNode (c := 204) (fun _ => isQueryBoundP_otsPublicLeaf hH hprf _ _ _)
    (fun _ _ _ _ => isQueryBoundP_th hH _ _ _) level j

/-- A key's path is the `16` nodes beside it, one per level. -/
theorem isQueryBoundP_path (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ pp a suffix, IsQueryBoundP (prf pp a suffix) p 1) (pp : PublicParam)
    (layer : Layer) (e : Nat) :
    IsQueryBoundP (path H pp prf layer e) p (2 ^ 16 * 205 - 205) := by
  have h := isQueryBoundP_merkleSiblings (c := 204) (hash := nodeHash H pp layer)
    (leaves := leaves H pp prf layer) (fun _ => isQueryBoundP_otsPublicLeaf hH hprf pp layer _)
    (fun _ _ _ _ => isQueryBoundP_th hH pp _ _) 0 e LAYER_HEIGHT
  unfold path Merkle.path
  exact h.mono (by simp [LAYER_HEIGHT])

/-- The public parameter is one derivation. -/
theorem isQueryBoundP_publicParamOf
    (hprf : ∀ pp a suffix, IsQueryBoundP (prf pp a suffix) p 1) :
    IsQueryBoundP (publicParamOf prf) p 1 :=
  isQueryBoundP_bind (m := 0) (hprf _ _ _) fun _ _ => isQueryBoundP_pure _ _ 0

/-- The public key is the parameter and the top tree's root. -/
theorem isQueryBoundP_publicKeyOf (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ pp a suffix, IsQueryBoundP (prf pp a suffix) p 1) :
    IsQueryBoundP (publicKeyOf H prf) p (205 * 2 ^ 16) := by
  refine (isQueryBoundP_bind (isQueryBoundP_publicParamOf hprf) fun pp _ =>
    isQueryBoundP_bind (m := 0) (isQueryBoundP_node hH hprf pp .top LAYER_HEIGHT 0) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono ?_
  simp [LAYER_HEIGHT]

/-- The base of the randomizer trials is one derivation. -/
theorem isQueryBoundP_randomizerBase
    (hprf : ∀ pp a suffix, IsQueryBoundP (prf pp a suffix) p 1) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) :
    IsQueryBoundP (randomizerBase pp prf layer e msg) p 1 :=
  isQueryBoundP_bind (m := 0) (hprf _ _ _) fun _ _ => isQueryBoundP_pure _ _ 0

/-- The codeword search is one digest per trial. -/
theorem isQueryBoundP_findCodeword (hH : ∀ x, IsQueryBoundP (H x) p 1) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    IsQueryBoundP (Internal.findCodeword H pp layer e msg base c fuel) p fuel :=
  isQueryBoundP_findFirst _ _ (fun _ => (isQueryBoundP_map_iff _ _ _).2
    (isQueryBoundP_th hH _ _ _)) c fuel

/-- A one-time signature is the base, at most `2^32` trials, the starts and `174` steps. -/
theorem isQueryBoundP_otsSign (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ pp a suffix, IsQueryBoundP (prf pp a suffix) p 1) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) :
    IsQueryBoundP (otsSign H pp prf layer e msg) p (2 ^ 32 + 204) := by
  unfold otsSign
  refine (isQueryBoundP_bind (isQueryBoundP_randomizerBase hprf pp layer e msg) fun base _ =>
    isQueryBoundP_bind (isQueryBoundP_findCodeword hH pp layer e msg base 0
      MAX_RANDOMIZER_TRIALS) fun r _ => ?_).mono (n := 1 + (MAX_RANDOMIZER_TRIALS + (29 + V * 3)))
    (by simp [MAX_RANDOMIZER_TRIALS, V])
  rcases r with _ | ⟨rho, x⟩
  · exact isQueryBoundP_pure _ _ _
  · refine (isQueryBoundP_bind (isQueryBoundP_chainStarts hprf pp layer e) fun starts _ =>
      isQueryBoundP_bind (isQueryBoundP_ofFnInOrder (n := 3) V _ fun i =>
        (isQueryBoundP_xmssChain hH pp layer e i 0 x[i] _ starts[i]).mono (m := 3) ?_)
        fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)
    have := x[i].isLt
    simp only [CHAIN_LENGTH] at this
    omega

/-- One layer's signature is a one-time signature and a path. -/
theorem isQueryBoundP_signLayer (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ pp a suffix, IsQueryBoundP (prf pp a suffix) p 1) (pp : PublicParam)
    (layer : Layer) (e : Nat) (msg : ByteArray) :
    IsQueryBoundP (signLayer H pp prf layer e msg) p (2 ^ 32 + 204 + (2 ^ 16 * 205 - 205)) := by
  unfold signLayer
  refine isQueryBoundP_bind (isQueryBoundP_otsSign hH hprf pp layer _ msg) fun r _ => ?_
  rcases r with _ | ⟨rho, y⟩
  · exact isQueryBoundP_pure _ _ _
  · exact (isQueryBoundP_bind (m := 0) (isQueryBoundP_path hH hprf pp layer e) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono le_rfl

/-- A signature is two layers' signatures and the root of the bottom tree. -/
theorem isQueryBoundP_signDerived (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ pp a suffix, IsQueryBoundP (prf pp a suffix) p 1) (pp : PublicParam)
    (idx : LeafIndex) (msg : Message) :
    IsQueryBoundP (signDerived H prf pp idx msg) p (2 ^ 33 + 615 * 2 ^ 16 - 3) := by
  unfold signDerived
  have hlayer := fun layer e msg => isQueryBoundP_signLayer hH hprf pp layer e msg
  refine (isQueryBoundP_bind (hlayer .bottom _ _) fun r _ => ?_).mono
    (n := 2 ^ 32 + 204 + (2 ^ 16 * 205 - 205) +
      (0 + ((2 ^ LAYER_HEIGHT * 205 - 1) + (2 ^ 32 + 204 + (2 ^ 16 * 205 - 205)))))
    (by simp [LAYER_HEIGHT])
  rcases r with err | bottom
  · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind (isQueryBoundP_pure _ _ 0) fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_node hH hprf pp _ LAYER_HEIGHT _) fun _ _ =>
        (isQueryBoundP_bind (m := 0) (hlayer .top _ _) fun r _ => ?_).mono
          (le_of_eq (Nat.add_zero _))
    rcases r with err | top
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_bind_zero _ _ (isQueryBoundP_pure _ _ _) fun _ =>
        isQueryBoundP_pure _ _ _

/-- The leaf of a one-time signature is a digest, at most `174` steps and one hash. -/
theorem isQueryBoundP_otsLeaf (hH : ∀ x, IsQueryBoundP (H x) p 1) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer) (y : Vector Digest V) :
    IsQueryBoundP (otsLeaf H pp layer e msg rho y) p 176 := by
  unfold otsLeaf
  refine isQueryBoundP_bind (m := 175) (isQueryBoundP_th hH pp _ _) fun d _ => ?_
  rcases codeword? d with _ | x
  · exact isQueryBoundP_pure _ _ _
  · refine (isQueryBoundP_bind (isQueryBoundP_ofFnInOrder (n := 3) V _ fun i =>
      (isQueryBoundP_xmssChain hH pp layer e i _ _ _ y[i]).mono (m := 3)
        (by simp only [CHAIN_LENGTH]; omega))
      fun _ _ => isQueryBoundP_bind (m := 0) (isQueryBoundP_th hH pp _ _) fun _ _ =>
        isQueryBoundP_pure _ _ 0).mono (by simp [V])

/-- The root one layer's signature leads to is a leaf and a climb of `16` levels. -/
theorem isQueryBoundP_layerRoot (hH : ∀ x, IsQueryBoundP (H x) p 1) (pp : PublicParam)
    (layer : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature) :
    IsQueryBoundP (layerRoot H pp layer e msg sig) p 192 := by
  unfold layerRoot
  refine (isQueryBoundP_bind (isQueryBoundP_otsLeaf hH pp layer _ msg _ _) fun r _ => ?_).mono
    (n := 176 + (LAYER_HEIGHT + 0)) (by simp [LAYER_HEIGHT])
  rcases r with _ | leaf
  · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind ((isQueryBoundP_climb (fun _ _ _ _ => isQueryBoundP_th hH pp _ _)
      sig.path.toList 0 e leaf).mono (by simp)) fun _ _ => isQueryBoundP_pure _ _ 0

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

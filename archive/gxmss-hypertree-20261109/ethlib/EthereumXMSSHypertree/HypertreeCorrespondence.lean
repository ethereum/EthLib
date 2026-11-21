/- Authors: Matthias Meijers -/

module

public import EthereumXMSSHypertree.Functional
public import EthereumXMSSHypertree.HypertreeHash
public import EthereumXMSSHypertree.HypertreePRF
public import EthereumXMSSHypertree.HypertreeRepresentation
public import HashSig.GXMSS.Hypertree.Scheme
import all HashSig.GXMSS.Merkle
import Mathlib.Data.Nat.Bitwise
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option

/-!
# Source computation equations for the reviewed generic hypertree

The adapter identifies actual source computations with the reviewed generic operations on their
reachable coordinates. Its equations retain all source failures and all signature fields.
-/

public section

namespace EthereumXMSSHypertree.HypertreeCorrespondence

open EthLib.Cryptography Xmss Xmss.Constants
open ConcreteHypertree HypertreeStrategies HypertreePRF

/-- Reindexing a component's concrete source tree by its global tree number preserves its root. -/
theorem source_component_root (H : Pure.Hash) (pp : PublicParam) (prf : Pure.Derivation)
    (layer : Layer) (tree level index : Nat) (hlevel : level ≤ 16) :
    PerfectMerkleTree.merkleRoot
      (fun i => Pure.publicLeaf H pp prf layer (UInt32.ofNat (tree * 2 ^ 16 + i)))
      (fun z t => Pure.nodeHash H pp layer z (tree * 2 ^ (16 - z) + t)) level index =
      Pure.node H pp prf layer level (tree * 2 ^ (16 - level) + index) := by
  induction level generalizing index with
  | zero => rfl
  | succ level ih =>
    rw [PerfectMerkleTree.merkleRoot_succ, ih _ (by omega), ih _ (by omega), Pure.node]
    have hpow : 2 ^ (16 - level) = 2 ^ (16 - (level + 1)) * 2 := by
      have hexponent : 16 - level = 16 - (level + 1) + 1 := by omega
      rw [hexponent, Nat.pow_succ]
    have hleft : tree * 2 ^ (16 - level) + 2 * index =
        2 * (tree * 2 ^ (16 - (level + 1)) + index) := by rw [hpow]; ring
    have hright : tree * 2 ^ (16 - level) + (2 * index + 1) =
        2 * (tree * 2 ^ (16 - (level + 1)) + index) + 1 := by rw [hpow]; ring
    rw [hleft, hright]

/-- The source's XOR sibling selector is the actual engine's sibling selector. -/
theorem source_sibling_eq (index : Nat) : index ^^^ 1 = PerfectMerkleTree.sibling index := by
  by_cases heven : index % 2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr heven)]
    simp [PerfectMerkleTree.sibling, heven]
  · have hodd : Odd index := Nat.odd_iff.mpr (by omega)
    rw [Nat.xor_one_of_odd hodd]
    simp [PerfectMerkleTree.sibling, heven]

/-- Each source path entry is its actual sibling subtree, in leaf-first order. -/
theorem source_siblings_get (H : Pure.Hash) (pp : PublicParam) (prf : Pure.Derivation)
    (layer : Layer) (level index n : Nat) (i : Fin n) :
    (Pure.siblings H pp prf layer level index n)[i] =
      Pure.node H pp prf layer (level + i.val) ((index / 2 ^ i.val) ^^^ 1) := by
  induction n generalizing level index with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Pure.siblings]
    · have hstep := ih (level + 1) (index / 2) j
      have hlevel : level + 1 + j.val = level + (j.val + 1) := by omega
      have hdiv : (index / 2) / 2 ^ j.val = index / 2 ^ (j.val + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ']
      rw [hlevel, hdiv] at hstep
      simpa [Pure.siblings] using hstep

/-- Every entry of the actual engine path is its leaf-first sibling subtree. -/
private theorem engine_path_get (leaf : Nat → Digest)
    (node : Nat → Nat → Digest → Digest → Digest) (index n : Nat) (i : Fin n) :
    (PerfectMerkleTree.authPath leaf node index n)[i.val]'(by simp) =
      PerfectMerkleTree.merkleRoot leaf node i.val
        (PerfectMerkleTree.sibling (index / 2 ^ i.val)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [PerfectMerkleTree.authPath_succ]
    by_cases hi : i.val < n
    · rw [List.getElem_append_left (by simpa using hi)]
      exact ih ⟨i.val, hi⟩
    · have hi' : i.val = n := by have := i.isLt; omega
      simp [hi']

/-- Adding an even component offset commutes with the source's sibling selector. -/
theorem component_sibling (offset localIndex : Nat) (heven : offset % 2 = 0) :
    (offset + localIndex) ^^^ 1 = offset + (localIndex ^^^ 1) := by
  rw [source_sibling_eq, source_sibling_eq]
  unfold PerfectMerkleTree.sibling
  have hparity : (offset + localIndex) % 2 = localIndex % 2 := by omega
  rw [hparity]
  split_ifs <;> omega

/-- The reviewed component chain equals the actual source chain at every legal span. -/
theorem component_chain_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (pp : PublicParam)
    (tree : GXMSS.Hypertree.TreePosition shape) (epoch : Fin (2 ^ 16)) (i : Fin 58)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    ((hashInstance H seedGen).componentHash tree).chain pp epoch i start steps value =
      Pure.chain H pp (sourceLayer tree) (sourceKey (tree, epoch)) i start steps h value := by
  induction steps with
  | zero => rw [GXMSS.HashInstance.chain_zero]; rfl
  | succ steps ih =>
    simp only [CHAIN_LENGTH] at h
    have hmu : start + steps < 3 := by omega
    have hprev : start + steps < CHAIN_LENGTH := by simp only [CHAIN_LENGTH]; omega
    rw [GXMSS.HashInstance.chain_succ _ pp epoch i start steps value
      (by change start + steps + 1 ≤ 3; omega)]
    change _ = Pure.step H pp (sourceLayer tree) (sourceKey (tree, epoch)) i
      ⟨start + steps, by simp only [CHAIN_LENGTH]; omega⟩
      (Pure.chain H pp (sourceLayer tree) (sourceKey (tree, epoch)) i start steps hprev value)
    rw [ih hprev]
    exact chain_eval H seedGen pp (tree, epoch) i ⟨start + steps, hmu⟩ _

/-- The full source chain-start table in the actual reviewed global coordinate domain. -/
@[expose] def sourceStarts (pp : PublicParam) (prf : Pure.Derivation) :
    GXMSS.Hypertree.OTSPosition shape → Fin 58 → Digest :=
  fun p i => (Pure.starts pp prf (sourceLayer p.1) (sourceKey p))[i]

/-- The full source endpoint table is the reviewed chain-endpoint operation on source starts. -/
theorem endpoints_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (pp : PublicParam)
    (prf : Pure.Derivation) (position : GXMSS.Hypertree.OTSPosition shape) (i : Fin 58) :
    GXMSS.Hypertree.endpoints (hashInstance H seedGen) pp (sourceStarts pp prf) position i =
      Pure.chain H pp (sourceLayer position.1) (sourceKey position) i 0 3 (by decide)
        (Pure.starts pp prf (sourceLayer position.1) (sourceKey position))[i] :=
  component_chain_eq H seedGen pp position.1 position.2 i 0 3 (by decide) _

/-- A component leaf formed from actual source starts is the source public leaf. -/
theorem component_leaf_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (pp : PublicParam)
    (prf : Pure.Derivation) (tree : GXMSS.Hypertree.TreePosition shape) (epoch : Fin (2 ^ 16)) :
    ((hashInstance H seedGen).componentHash tree).leafHash pp epoch
      (fun i => GXMSS.Hypertree.endpoints (hashInstance H seedGen) pp
        (sourceStarts pp prf) (tree, epoch) i) =
      Pure.publicLeaf H pp prf (sourceLayer tree) (sourceKey (tree, epoch)) := by
  have hf : (fun i => GXMSS.Hypertree.endpoints (hashInstance H seedGen) pp
      (sourceStarts pp prf) (tree, epoch) i) =
      (fun i => Pure.chain H pp (sourceLayer tree) (sourceKey (tree, epoch)) i
        0 3 (by decide) (Pure.starts pp prf (sourceLayer tree) (sourceKey (tree, epoch)))[i]) := by
    funext i
    exact endpoints_eq H seedGen pp prf (tree, epoch) i
  have hv := congrArg (fun f : Fin 58 → Digest => Vector.ofFn f) hf
  calc
    _ = Pure.leafHash H pp (sourceLayer tree) (sourceKey (tree, epoch))
        (Vector.ofFn (fun i => GXMSS.Hypertree.endpoints (hashInstance H seedGen) pp
          (sourceStarts pp prf) (tree, epoch) i)) := leaf_eval H seedGen pp tree epoch _
    _ = Pure.leafHash H pp (sourceLayer tree) (sourceKey (tree, epoch))
        (Vector.ofFn (fun i => Pure.chain H pp (sourceLayer tree) (sourceKey (tree, epoch)) i
          0 3 (by decide) (Pure.starts pp prf (sourceLayer tree) (sourceKey (tree, epoch)))[i])) :=
      congrArg (Pure.leafHash H pp (sourceLayer tree) (sourceKey (tree, epoch))) hv
    _ = _ := rfl

/-- A reachable local Merkle node satisfies the concrete reached-node predicate. -/
private theorem reachable_local {level index : Nat} (_hpos : 0 < level) (hl : level ≤ 16)
    (hi : (index + 1) * 2 ^ level ≤ 2 ^ 16) : index < 2 ^ (16 - level) := by
  have hp : 2 ^ 16 = 2 ^ (16 - level) * 2 ^ level := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hl]
  rw [hp] at hi
  exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_right hi (Nat.two_pow_pos level))

/-- The reviewed component root equals the full source root at its global tree number. -/
theorem component_root_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (pp : PublicParam)
    (prf : Pure.Derivation) (tree : GXMSS.Hypertree.TreePosition shape) :
    GXMSS.Hypertree.componentRoot (hashInstance H seedGen) pp
      (GXMSS.Hypertree.endpoints (hashInstance H seedGen) pp (sourceStarts pp prf)) tree =
      Pure.node H pp prf (sourceLayer tree) 16 tree.2.val := by
  let P := (hashInstance H seedGen).componentHash tree
  let ends := fun epoch => GXMSS.Hypertree.endpoints (hashInstance H seedGen) pp
    (sourceStarts pp prf) (tree, epoch)
  have hl : ∀ i < 2 ^ 16, P.leafExtension pp ends i =
      Pure.publicLeaf H pp prf (sourceLayer tree) (UInt32.ofNat (tree.2.val * 2 ^ 16 + i)) := by
    intro i hi
    change (if h : i < 2 ^ 16 then P.leafHash pp ⟨i, h⟩ (ends ⟨i, h⟩)
      else P.leafHash pp 0 (ends 0)) = _
    rw [dite_eq_left hi]
    exact component_leaf_eq H seedGen pp prf tree ⟨i, hi⟩
  have hn : ∀ z, 0 < z → z ≤ 16 → ∀ i, (i + 1) * 2 ^ z ≤ 2 ^ 16 →
      ∀ left right, P.nodeExtension pp z i left right =
        Pure.nodeHash H pp (sourceLayer tree) z (tree.2.val * 2 ^ (16 - z) + i) left right := by
    intro z hzpos hz i hi left right
    have hzrect : z < 17 := by omega
    have hireach := reachable_local hzpos hz hi
    have hirect : i < 2 ^ 16 := (GXMSS.Merkle.subtree_legal hz hi).2
    change (if hz' : z < 17 then
      if hi' : i < 2 ^ 16 then P.nodeHash pp ⟨z, hz'⟩ ⟨i, hi'⟩ left right else left
      else left) = _
    rw [dite_eq_left hzrect, dite_eq_left hirect]
    exact node_eval H seedGen pp tree ⟨z, hzrect⟩ ⟨i, hirect⟩ left right ⟨hzpos, hireach⟩
  change PerfectMerkleTree.merkleRoot (P.leafExtension pp ends) (P.nodeExtension pp) 16 0 = _
  rw [GXMSS.Merkle.root_extension_independent _ _ _ _ 16 16 0 le_rfl (by simp) hl hn]
  simpa only [Nat.sub_self, pow_zero, Nat.mul_one, Nat.add_zero] using
    source_component_root H pp prf (sourceLayer tree) tree.2.val 16 0 le_rfl

/-- The actual reviewed authentication path preserves every source leaf-first sibling. -/
theorem component_path_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (pp : PublicParam)
    (prf : Pure.Derivation) (tree : GXMSS.Hypertree.TreePosition shape) (epoch : Fin (2 ^ 16)) :
    ((hashInstance H seedGen).componentHash tree).authPath pp
      (fun ep => GXMSS.Hypertree.endpoints (hashInstance H seedGen) pp (sourceStarts pp prf)
        (tree, ep)) epoch =
      fun z => (Pure.path H pp prf (sourceLayer tree) (globalIndex (tree, epoch)))[z] := by
  let P := (hashInstance H seedGen).componentHash tree
  let ends := fun ep => GXMSS.Hypertree.endpoints (hashInstance H seedGen) pp
    (sourceStarts pp prf) (tree, ep)
  have hl : ∀ i < 2 ^ 16, P.leafExtension pp ends i =
      Pure.publicLeaf H pp prf (sourceLayer tree) (UInt32.ofNat (tree.2.val * 2 ^ 16 + i)) := by
    intro i hi
    change (if h : i < 2 ^ 16 then P.leafHash pp ⟨i, h⟩ (ends ⟨i, h⟩)
      else P.leafHash pp 0 (ends 0)) = _
    rw [dite_eq_left hi]
    exact component_leaf_eq H seedGen pp prf tree ⟨i, hi⟩
  have hn : ∀ z, 0 < z → z ≤ 16 → ∀ i, (i + 1) * 2 ^ z ≤ 2 ^ 16 →
      ∀ left right, P.nodeExtension pp z i left right =
        Pure.nodeHash H pp (sourceLayer tree) z (tree.2.val * 2 ^ (16 - z) + i) left right := by
    intro z hzpos hz i hi left right
    have hzrect : z < 17 := by omega
    have hireach := reachable_local hzpos hz hi
    have hirect : i < 2 ^ 16 := (GXMSS.Merkle.subtree_legal hz hi).2
    change (if hz' : z < 17 then
      if hi' : i < 2 ^ 16 then P.nodeHash pp ⟨z, hz'⟩ ⟨i, hi'⟩ left right else left
      else left) = _
    rw [dite_eq_left hzrect, dite_eq_left hirect]
    exact node_eval H seedGen pp tree ⟨z, hzrect⟩ ⟨i, hirect⟩ left right ⟨hzpos, hireach⟩
  have hp := GXMSS.Merkle.authPath_extension_independent _ _ _ _ 16 epoch hl hn
  funext z
  have hz : z.val < 16 := z.isLt
  change (PerfectMerkleTree.authPath (P.leafExtension pp ends) (P.nodeExtension pp)
    epoch.val 16)[z.val]'(by simp) = _
  simp only [hp]
  rw [engine_path_get, source_component_root H pp prf (sourceLayer tree)
    tree.2.val z.val _ (by omega)]
  change _ = (Pure.siblings H pp prf (sourceLayer tree) 0
    (globalIndex (tree, epoch)) 16)[z]
  rw [source_siblings_get]
  simp only [Nat.zero_add]
  have heven : (tree.2.val * 2 ^ (16 - z.val)) % 2 = 0 := by
    have he : 16 - z.val = (15 - z.val) + 1 := by omega
    rw [he, Nat.pow_succ, ← Nat.mul_assoc]
    omega
  have hsibling : (globalIndex (tree, epoch) / 2 ^ z.val) ^^^ 1 =
      tree.2.val * 2 ^ (16 - z.val) + PerfectMerkleTree.sibling (epoch.val / 2 ^ z.val) := by
    rw [globalIndex_ancestor tree epoch z.val (by omega), nodeGlobalIndex,
      component_sibling _ _ heven, source_sibling_eq]
  rw [hsibling]

/-- The public monadic engine law gives the pure engine's actual first leaf-level step. -/
private theorem engine_climb_cons (node : Nat → Nat → Digest → Digest → Digest)
    (index : Nat) (current sibling : Digest) (rest : List Digest) :
    PerfectMerkleTree.climb node index current (sibling :: rest) =
      let children := Merkle.ordered index current sibling
      PerfectMerkleTree.climb (fun z t => node (z + 1) t) (index / 2)
        (node 1 (index / 2) children.1 children.2) rest := by
  have h := congrArg Id.run (PerfectMerkleTree.climbM_cons
    (fun z t left right => (pure (node z t left right) : Id Digest)) index current sibling rest)
  by_cases hparity : index % 2 = 0
  · simpa [hparity, Merkle.ordered] using h
  · simpa [hparity, Merkle.ordered] using h

/-- The source global-index frame commutes with the canonical engine's leaf-first climb. -/
theorem source_component_climb (H : Pure.Hash) (pp : PublicParam) (layer : Layer)
    (tree level index : Nat) (current : Digest) (auth : List Digest)
    (hlevel : level + auth.length ≤ 16) :
    PerfectMerkleTree.climb
      (fun z t => Pure.nodeHash H pp layer (z + level) (tree * 2 ^ (16 - (z + level)) + t))
      index current auth =
      Pure.climb H pp layer level (tree * 2 ^ (16 - level) + index) current auth := by
  induction auth generalizing level index current with
  | nil => rfl
  | cons sibling rest ih =>
    have hlt : level < 16 := by simp only [List.length_cons] at hlevel; omega
    have hpow : 2 ^ (16 - level) = 2 ^ (16 - (level + 1)) * 2 := by
      have he : 16 - level = 16 - (level + 1) + 1 := by omega
      rw [he, Nat.pow_succ]
    have heven : (tree * 2 ^ (16 - level)) % 2 = 0 := by
      rw [hpow, ← Nat.mul_assoc]
      omega
    have hparity : (tree * 2 ^ (16 - level) + index) % 2 = index % 2 := by omega
    have hparent : (tree * 2 ^ (16 - level) + index) / 2 =
        tree * 2 ^ (16 - (level + 1)) + index / 2 := by
      rw [hpow, ← Nat.mul_assoc]
      omega
    rw [engine_climb_cons, Pure.climb]
    simp only [Merkle.ordered, hparity]
    rw [hparent]
    have hshift : (fun z t => Pure.nodeHash H pp layer ((z + 1) + level)
        (tree * 2 ^ (16 - ((z + 1) + level)) + t)) =
        (fun z t => Pure.nodeHash H pp layer (z + (level + 1))
          (tree * 2 ^ (16 - (z + (level + 1))) + t)) := by
      funext z t
      rw [Nat.add_assoc, Nat.add_comm 1 level]
    rw [hshift]
    simpa only [Nat.add_comm 1 level] using
      ih (level + 1) (index / 2) _ (by simp only [List.length_cons] at hlevel; omega)

/-- All-input component recovery equals source recovery from the identical leaf and sibling data. -/
theorem component_recover_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (pp : PublicParam)
    (tree : GXMSS.Hypertree.TreePosition shape) (epoch : Fin (2 ^ 16))
    (values : Fin 58 → Digest) (path : Fin 16 → Digest) :
    ((hashInstance H seedGen).componentHash tree).recoverRoot pp epoch values path =
      Pure.climb H pp (sourceLayer tree) 0 (globalIndex (tree, epoch))
        (Pure.leafHash H pp (sourceLayer tree) (sourceKey (tree, epoch)) (Vector.ofFn values))
        (List.ofFn path) := by
  let P := (hashInstance H seedGen).componentHash tree
  have hn : ∀ z, 0 < z → z ≤ 16 → ∀ i, (i + 1) * 2 ^ z ≤ 2 ^ 16 →
      ∀ left right, P.nodeExtension pp z i left right =
        Pure.nodeHash H pp (sourceLayer tree) z (tree.2.val * 2 ^ (16 - z) + i) left right := by
    intro z hzpos hz i hi left right
    have hzrect : z < 17 := by omega
    have hireach := reachable_local hzpos hz hi
    have hirect : i < 2 ^ 16 := (GXMSS.Merkle.subtree_legal hz hi).2
    change (if hz' : z < 17 then
      if hi' : i < 2 ^ 16 then P.nodeHash pp ⟨z, hz'⟩ ⟨i, hi'⟩ left right else left
      else left) = _
    rw [dite_eq_left hzrect, dite_eq_left hirect]
    exact node_eval H seedGen pp tree ⟨z, hzrect⟩ ⟨i, hirect⟩ left right ⟨hzpos, hireach⟩
  have hl : P.leafHash pp epoch values =
      Pure.leafHash H pp (sourceLayer tree) (sourceKey (tree, epoch)) (Vector.ofFn values) :=
    leaf_eval H seedGen pp tree epoch values
  change PerfectMerkleTree.climb (P.nodeExtension pp) epoch.val (P.leafHash pp epoch values)
    (List.ofFn path) = _
  rw [hl, GXMSS.Merkle.climb_extension_independent _ _ 16 epoch _ path hn]
  simpa only [Nat.add_zero, Nat.sub_zero, globalIndex] using
    source_component_climb H pp (sourceLayer tree)
    tree.2.val 0 epoch.val _ (List.ofFn path)
      (by simp only [List.length_ofFn]; omega)

/-- Reconstruct one source layer from the complete actual generic component signature. -/
@[expose] def componentToSource (sig : GXMSS.Signature Randomizer Digest shape.h shape.v) :
    LayerSignature := layerSignatureEquiv.symm (componentSignatureEquiv.symm sig)

/-- Component signature conversion preserves the source layer exactly. -/
@[simp] theorem componentToSource_toGeneric (sig : LayerSignature) :
    componentToSource (componentSignatureEquiv (layerSignatureEquiv sig)) = sig := by
  simp only [componentToSource, Equiv.symm_apply_apply]

/-- The reviewed PRF-derived keys preserve the complete source public key and original raw S0. -/
theorem source_keygen_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (raw : Seed) :
    GXMSS.Hypertree.PRFDerived.keys (hashInstance H seedGen) .pairedCounter
      sourceRetrySampling (sourceEvaluator H) sourceInterpretation sourceRetryInterpretation raw =
      (publicKeyToGeneric (Pure.keys H raw).2, raw) := by
  let prf := Pure.derivedResponse H (Pure.schemeSeed H raw)
  let pp := Pure.publicParam prf
  have hpp : GXMSS.Hypertree.PRFDerived.publicSeed (sourceEvaluator H)
      sourceInterpretation raw = pp := publicSeed_eq_source H raw
  have hstarts : GXMSS.Hypertree.PRFDerived.starts .pairedCounter
      (GXMSS.Hypertree.PRFDerived.retryBudget sourceRetrySampling)
      (sourceEvaluator H) sourceInterpretation raw pp = sourceStarts pp prf := by
    funext position i
    exact starts_eq_source H raw pp position i
  simp only [GXMSS.Hypertree.PRFDerived.keys, GXMSS.Hypertree.PRFDerived.coreSecretKey]
  rw [hpp, hstarts, component_root_eq]
  rfl

end EthereumXMSSHypertree.HypertreeCorrespondence

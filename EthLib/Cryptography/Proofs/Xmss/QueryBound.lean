module

public import EthLib.Cryptography.Xmss.Sign
public import EthLib.Cryptography.Xmss.Verify
public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import EthLib.Cryptography.Proofs.Merkle.QueryBound
public import EthLib.Cryptography.Proofs.Xmss.Ots
public import EthLib.Cryptography.Proofs.Xmss.Encoding
public import EthLib.Cryptography.Proofs.QueryAvoidance
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Proofs: how many calls the leanXMSS algorithms make

A call of `H` on `n` lanes is charged at most `w n`.

Then each algorithm is charged a sum of weights at input lengths fixed by the message length.

With the weight 1, each call of `H` and of the seed function counts at most 1:

- A tree at level 16 takes at most `205 * 2^16 - 1` calls.
- A one-time signature takes at most `2^32 + 204` calls.
- Verification takes at most `384` calls.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open OracleSpec OracleComp
open EthLib.Cryptography.Xmss.Constants

open PFunctor.FreeM (IsChargeBound isChargeBound_pure isChargeBound_map_iff' wpFold)
open PFunctor (OpSpec)

/-! ## Charged algorithms

A call of `H` on `n` lanes is charged at most `w n`.

A derivation from the seed with a suffix of `n` lanes hashes `8 + n` lanes.
-/

attribute [local irreducible] LAYER_HEIGHT MAX_RANDOMIZER_TRIALS

section ChargeAlgorithms

variable {ι : Type} {spec : OracleSpec ι} {c : ι → ℕ} {w : ℕ → ℕ}
  {H : Array UInt64 → OracleComp spec Lanes4} {prf : SeedPrf (OracleComp spec)}

/-- A tweakable hash call is one call of `H` on `4` lanes more than its payload. -/
theorem isChargeBound_th (hH : ∀ x, IsChargeBound (H x) c (w x.size)) (publicParam : PublicParam)
    (address : Address) (payload : Array UInt64) :
    IsChargeBound (th H publicParam address payload) c (w (4 + payload.size)) := by
  have h := hH (thInput publicParam address payload)
  rw [size_thInput] at h
  exact (h.bind fun _ => isChargeBound_pure (B := 0) _).mono le_rfl

/-- A node hash is one call of `H` on `8` lanes. -/
theorem isChargeBound_nodeHash (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (publicParam : PublicParam) (layer : Layer) (q : Merkle.Position) (left right : Digest) :
    IsChargeBound (nodeHash H publicParam layer q left right) c (w 8) :=
  isChargeBound_th hH _ _ _

/-- A chain step is one call of `H` on `8` lanes. -/
theorem isChargeBound_chainStep (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) :
    IsChargeBound (chainStep H publicParam layer e i mu value) c (w 8) :=
  isChargeBound_th hH _ _ _

/-- The starts of a key's chains are `29` derivations on `8` lanes. -/
theorem isChargeBound_chainStarts
    (hprf : ∀ publicParam a suffix, IsChargeBound (prf publicParam a suffix) c
      (w (8 + suffix.size)))
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) :
    IsChargeBound (chainStarts publicParam prf layer e) c (29 * w 8) :=
  ((isChargeBound_ofFnInOrder_const (V / 2) _ fun _ => hprf _ _ _).bind fun _ =>
    isChargeBound_pure (B := 0) _).mono (le_of_eq (by simp [V]))

/-- A walk of `steps` steps on a chain is `steps` calls of `H` on `8` lanes. -/
theorem isChargeBound_xmssChain (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    IsChargeBound (chain H publicParam layer e i start steps h value) c (steps * w 8) :=
  isChargeBound_chain _ (fun _ _ => isChargeBound_chainStep hH _ _ _ _ _ _) _ _ _ _

/-- The leaf hash of a key is one call of `H` on `120` lanes. -/
theorem isChargeBound_otsLeafHash (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) (ends : Vector Digest V) :
    IsChargeBound (otsLeafHash H publicParam layer e ends) c (w 120) := by
  have h := isChargeBound_th hH publicParam (.leaf layer e) (digestLanes ends)
  rwa [size_digestLanes] at h

/-- A key's leaf is `29` derivations and `174` chain steps on `8` lanes, and its leaf hash. -/
theorem isChargeBound_otsPublicLeaf (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (hprf : ∀ publicParam a suffix, IsChargeBound (prf publicParam a suffix) c
      (w (8 + suffix.size)))
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) :
    IsChargeBound (otsPublicLeaf H publicParam prf layer e) c (203 * w 8 + w 120) :=
  ((isChargeBound_chainStarts hprf publicParam layer e).bind fun _ =>
    (isChargeBound_ofFnInOrder_const V _ fun _ => isChargeBound_xmssChain hH _ _ _ _ _ _ _ _).bind
      fun _ => isChargeBound_otsLeafHash hH _ _ _ _).mono
    (le_of_eq (by simp only [V, CHAIN_LENGTH]; ring))

/-- A node at `level` is `2^level` leaves and `2^level - 1` node hashes. -/
theorem isChargeBound_node (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (hprf : ∀ publicParam a suffix, IsChargeBound (prf publicParam a suffix) c
      (w (8 + suffix.size)))
    (publicParam : PublicParam) (layer : Layer) (level j : Nat) :
    IsChargeBound (node H publicParam prf layer level j) c
      (2 ^ level * (203 * w 8 + w 120) + (2 ^ level - 1) * w 8) :=
  Merkle.isChargeBound_node (fun _ => isChargeBound_otsPublicLeaf hH hprf _ _ _)
    (fun _ _ _ => isChargeBound_nodeHash hH _ _ _ _ _) ⟨level, j⟩

/-- A build at `level` is `2^level` leaves and `2^level - 1` node hashes. -/
theorem isChargeBound_build (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (hprf : ∀ publicParam a suffix, IsChargeBound (prf publicParam a suffix) c
      (w (8 + suffix.size)))
    (publicParam : PublicParam) (layer : Layer) (level j : Nat) :
    IsChargeBound (build H publicParam prf layer level j) c
      (2 ^ level * (203 * w 8 + w 120) + (2 ^ level - 1) * w 8) :=
  Merkle.isChargeBound_build (fun _ => isChargeBound_otsPublicLeaf hH hprf _ _ _)
    (fun _ _ _ => isChargeBound_nodeHash hH _ _ _ _ _) ⟨level, j⟩

/-- A key's path is the `16` nodes beside it, one per level. -/
theorem isChargeBound_path (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (hprf : ∀ publicParam a suffix, IsChargeBound (prf publicParam a suffix) c
      (w (8 + suffix.size)))
    (publicParam : PublicParam) (layer : Layer) (e : Nat) :
    IsChargeBound (path H publicParam prf layer e) c ((2 ^ 16 - 1) * (204 * w 8 + w 120)) := by
  have h := Merkle.isChargeBound_siblings (hash := nodeHash H publicParam layer)
    (leaves := leaves H publicParam prf layer)
    (fun _ => isChargeBound_otsPublicLeaf hH hprf publicParam layer _)
    (fun _ _ _ => isChargeBound_nodeHash hH publicParam layer _ _ _) ⟨0, e⟩ LAYER_HEIGHT
  unfold path Merkle.path
  exact h.mono (le_of_eq (by simp only [LAYER_HEIGHT]; ring))

/-- The public parameter is one derivation on `8` lanes. -/
theorem isChargeBound_publicParamOf
    (hprf : ∀ publicParam a suffix, IsChargeBound (prf publicParam a suffix) c
      (w (8 + suffix.size))) :
    IsChargeBound (publicParamOf prf) c (w 8) :=
  ((hprf _ _ _).bind fun _ => isChargeBound_pure (B := 0) _).mono le_rfl

/-- The base of the randomizer trials is one derivation on `8` lanes more than the message. -/
theorem isChargeBound_randomizerBase
    (hprf : ∀ publicParam a suffix, IsChargeBound (prf publicParam a suffix) c
      (w (8 + suffix.size)))
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) (msg : Array UInt64) :
    IsChargeBound (randomizerBase publicParam prf layer e msg) c (w (8 + msg.size)) :=
  ((hprf _ _ _).bind fun _ => isChargeBound_pure (B := 0) _).mono le_rfl

/-- The digest of a message is one call of `H` on `6` lanes more than the message. -/
theorem isChargeBound_messageDigest (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) (msg : Array UInt64)
    (rho : Randomizer) :
    IsChargeBound (messageDigest H publicParam layer e msg rho) c (w (6 + msg.size)) := by
  have h := isChargeBound_th hH publicParam (.msg layer e) (msg ++ rho.toArray)
  rwa [Array.size_append, show rho.toArray.size = 2 from rfl, Nat.add_comm msg.size 2,
    ← Nat.add_assoc] at h

/-- The codeword search is one digest per trial. -/
theorem isChargeBound_findCodeword (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) (msg : Array UInt64)
    (base : Randomizer) (start fuel : Nat) :
    IsChargeBound (Internal.findCodeword H publicParam layer e msg base start fuel) c
      (fuel * w (6 + msg.size)) := by
  rw [Internal.findCodeword_eq]
  exact isChargeBound_findFirst _ _ (fun _ => (isChargeBound_map_iff' _ _).2
    (isChargeBound_messageDigest hH _ _ _ _ _)) start fuel

/-- Every codeword the search returns has the digit sum `106`. -/
theorem wpFold_findCodeword (publicParam : PublicParam) (layer : Layer) (e : UInt32)
    (msg : Array UInt64) (base : Randomizer) (start fuel : Nat) :
    wpFold (OpSpec.demonic _) (Internal.findCodeword H publicParam layer e msg base start fuel)
      fun r => ∀ rho x, r = some (rho, x) → ∑ i : Fin V, (x[i] : Nat) = TARGET_SUM := by
  rw [Internal.findCodeword_eq]
  exact wpFold_findFirst _ _ (fun _ => by
    rw [PFunctor.FreeM.wpFold_map]
    exact (PFunctor.FreeM.wpFold_demonic_iff_allOutputs _ _).2 fun _ _ _ h =>
      sum_of_codeword h) _ _

/-- A one-time signature is the base, at most `2^32` digests, the starts and `106` steps.

The chains walk to the digits of a codeword, which sum to `106`. -/
theorem isChargeBound_otsSign (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (hprf : ∀ publicParam a suffix, IsChargeBound (prf publicParam a suffix) c
      (w (8 + suffix.size)))
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) (msg : Array UInt64) :
    IsChargeBound (otsSign H publicParam prf layer e msg) c
      (w (8 + msg.size) + MAX_RANDOMIZER_TRIALS * w (6 + msg.size) + 135 * w 8) := by
  unfold otsSign Internal.otsSignTrials
  refine ((isChargeBound_randomizerBase hprf publicParam layer e msg).bind fun base =>
    (isChargeBound_findCodeword hH publicParam layer e msg base 0
      MAX_RANDOMIZER_TRIALS).bind_of_wpFold (B₂ := 135 * w 8)
      (wpFold_findCodeword publicParam layer e msg base 0 MAX_RANDOMIZER_TRIALS)
      fun r hr => ?_).mono (le_of_eq (Nat.add_assoc _ _ _).symm)
  rcases r with _ | ⟨rho, x⟩
  · exact isChargeBound_pure _
  · have hsum := hr rho x rfl
    have hchains (starts : Vector Digest V) : IsChargeBound
        (ofFnInOrder V fun i => chain H publicParam layer e i 0 x[i] (by simp) starts[i]) c
        (∑ i : Fin V, (x[i] : Nat) * w 8) :=
      isChargeBound_ofFnInOrder V _ _ fun i =>
        isChargeBound_xmssChain hH publicParam layer e i 0 x[i] _ starts[i]
    refine ((isChargeBound_chainStarts hprf publicParam layer e).bind fun starts =>
      (hchains starts).bind fun _ => isChargeBound_pure (B := 0) _).mono (le_of_eq ?_)
    rw [← Finset.sum_mul, hsum]
    simp only [TARGET_SUM]
    ring

/-- The leaf of a one-time signature is a digest, `68` steps and the leaf hash.

The chains walk from the digits of a codeword to the ends: `3 * 58 - 106 = 68` steps. -/
theorem isChargeBound_otsLeaf (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) (msg : Array UInt64)
    (rho : Randomizer) (y : Vector Digest V) :
    IsChargeBound (otsLeaf H publicParam layer e msg rho y) c
      (w (6 + msg.size) + 68 * w 8 + w 120) := by
  unfold otsLeaf
  refine ((isChargeBound_messageDigest hH publicParam layer e msg rho).bind
    (B₂ := 68 * w 8 + w 120) fun d => ?_).mono (le_of_eq (Nat.add_assoc _ _ _).symm)
  rcases hd : codeword? d with _ | x
  · exact isChargeBound_pure _
  · have hsum := sum_of_codeword hd
    refine ((isChargeBound_ofFnInOrder V _
      (fun i => (CHAIN_LENGTH - 1 - x[i]) * w 8) fun i =>
        isChargeBound_xmssChain hH publicParam layer e i _ _ _ y[i]).bind fun _ =>
      (isChargeBound_otsLeafHash hH publicParam layer e _).bind fun _ =>
        isChargeBound_pure (B := 0) _).mono (le_of_eq ?_)
    -- Each chain walks `3 - x_i` steps, so the walks and the digits add up to `3 * 58`.
    have hsteps : ∑ i : Fin V, (CHAIN_LENGTH - 1 - (x[i] : Nat)) = 68 := by
      have hadd : ∑ i : Fin V, (CHAIN_LENGTH - 1 - (x[i] : Nat)) + ∑ i : Fin V, (x[i] : Nat) =
          ∑ _i : Fin V, 3 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have := x[i].isLt
        simp only [CHAIN_LENGTH] at *
        omega
      rw [Finset.sum_const, Finset.card_fin, smul_eq_mul, hsum] at hadd
      have hV : V * 3 = 174 := rfl
      have hT : TARGET_SUM = 106 := rfl
      omega
    rw [← Finset.sum_mul, hsteps]
    ring

/-- The root one layer's signature leads to is a leaf and a climb of `16` node hashes. -/
theorem isChargeBound_layerRoot (hH : ∀ x, IsChargeBound (H x) c (w x.size))
    (publicParam : PublicParam) (layer : Layer) (e : Nat) (msg : Array UInt64)
    (sig : LayerSignature) :
    IsChargeBound (layerRoot H publicParam layer e msg sig) c
      (w (6 + msg.size) + 84 * w 8 + w 120) := by
  unfold layerRoot
  refine ((isChargeBound_otsLeaf hH publicParam layer _ msg _ _).bind
    (B₂ := LAYER_HEIGHT * w 8) fun r => ?_).mono
    (le_of_eq (by simp only [LAYER_HEIGHT]; ring))
  rcases r with _ | leaf
  · exact isChargeBound_pure _
  · exact (((Merkle.isChargeBound_climb (fun _ _ _ => isChargeBound_nodeHash hH publicParam
      layer _ _ _) sig.path.toList ⟨0, e⟩ leaf).bind fun _ =>
        isChargeBound_pure (B := 0) _).mono (le_of_eq (by simp)))

/-- Verification is the roots of both layers. -/
theorem isChargeBound_verifyWith (hH : ∀ x, IsChargeBound (H x) c (w x.size)) (pk : PublicKey)
    (msg : Message) (sig : Signature) :
    IsChargeBound (verifyWith H pk msg sig) c (w 10 + 169 * w 8 + 2 * w 120) := by
  unfold verifyWith
  refine ((isChargeBound_layerRoot hH _ _ _ _ _).bind (B₂ := 85 * w 8 + w 120)
    fun r => ?_).mono (le_of_eq ?_)
  · rcases r with _ | bottomRoot
    · exact isChargeBound_pure _
    · refine ((isChargeBound_layerRoot hH _ _ _ _ _).bind (B₂ := 0) fun r => ?_).mono
        (le_of_eq (by simp [Hash.Keccak.Lanes2.toArray]; ring))
      rcases r with _ | root <;> exact isChargeBound_pure _
  · simp [Hash.Keccak.Lanes4.toArray]
    ring

end ChargeAlgorithms

/-! ## Counted loops

A count of the calls that `p` accepts charges one per such call.
-/

section Loops

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]

/-- Computing `k` entries in order costs `k` times the cost of one. -/
theorem isQueryBoundP_ofFnInOrder {α : Type} {n : Nat} :
    ∀ (k : Nat) (f : Fin k → OracleComp spec α), (∀ i, IsQueryBoundP (f i) p n) →
      IsQueryBoundP (HashSig.ofFnInOrder k f) p (k * n) := fun k f h =>
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| isChargeBound_ofFnInOrder_const k f fun i =>
    (isQueryBoundP_iff_isChargeBound p _ _).1 (h i)

/-- A walk of `steps` steps costs at most `steps`, when each step costs at most 1. -/
theorem isQueryBoundP_chain {α : Type} {k : Nat} (step : Fin k → α → OracleComp spec α)
    (hstep : ∀ i v, IsQueryBoundP (step i v) p 1) (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ k) (value : α),
      IsQueryBoundP (Wots.chain step start steps h value) p steps := fun steps h value =>
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_chain step
    (fun i v => (isQueryBoundP_iff_isChargeBound p _ _).1 (hstep i v)) start steps h
      value).mono (le_of_eq (Nat.mul_one _))

/-- A search of `fuel` trials costs at most `fuel`, when each test costs at most 1. -/
theorem isQueryBoundP_findFirst {κ β : Type} (trial : Nat → κ)
    (test : κ → OracleComp spec (Option β)) (htest : ∀ k, IsQueryBoundP (test k) p 1) :
    ∀ (c fuel : Nat), IsQueryBoundP (Wots.findFirst trial test c fuel) p fuel := fun c fuel =>
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_findFirst trial test
    (fun k => (isQueryBoundP_iff_isChargeBound p _ _).1 (htest k)) c fuel).mono
      (le_of_eq (Nat.mul_one _))

end Loops

/-! ## Counted algorithms -/

section Algorithms

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
  {H : Array UInt64 → OracleComp spec Lanes4} {prf : SeedPrf (OracleComp spec)}

/-- A tweakable hash call is one call of `H`. -/
theorem isQueryBoundP_th (hH : ∀ x, IsQueryBoundP (H x) p 1) (publicParam : PublicParam)
    (address : Address) (payload : Array UInt64) :
    IsQueryBoundP (th H publicParam address payload) p 1 :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <|
    isChargeBound_th (w := fun _ => 1)
      (fun x => (isQueryBoundP_iff_isChargeBound p _ _).1 (hH x))
      publicParam address payload

/-- The starts of a key's chains are `29` derivations. -/
theorem isQueryBoundP_chainStarts (hprf : ∀ publicParam a suffix, IsQueryBoundP
    (prf publicParam a suffix) p 1)
    (publicParam : PublicParam) (layer : Layer) (e : UInt32) :
    IsQueryBoundP (chainStarts publicParam prf layer e) p 29 :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| isChargeBound_chainStarts (w := fun _ => 1)
    (fun _ _ _ => (isQueryBoundP_iff_isChargeBound p _ _).1 (hprf _ _ _)) publicParam layer e

/-- A walk of `steps` steps on a chain is `steps` calls of `H`. -/
theorem isQueryBoundP_xmssChain (hH : ∀ x, IsQueryBoundP (H x) p 1) (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    IsQueryBoundP (chain H publicParam layer e i start steps h value) p steps :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_xmssChain (w := fun _ => 1)
    (fun x => (isQueryBoundP_iff_isChargeBound p _ _).1 (hH x))
      publicParam layer e i start steps h value).mono
      (le_of_eq (Nat.mul_one _))

/-- A key's leaf is `29` derivations, `174` chain steps and one hash. -/
theorem isQueryBoundP_otsPublicLeaf (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) :
    IsQueryBoundP (otsPublicLeaf H publicParam prf layer e) p 204 :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| isChargeBound_otsPublicLeaf (w := fun _ => 1)
    (fun x => (isQueryBoundP_iff_isChargeBound p _ _).1 (hH x))
      (fun _ _ _ => (isQueryBoundP_iff_isChargeBound p _ _).1 (hprf _ _ _))
      publicParam layer e

/-- A node at `level` is `2^level` leaves and `2^level - 1` hashes. -/
theorem isQueryBoundP_node (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (level j : Nat) :
    IsQueryBoundP (node H publicParam prf layer level j) p (2 ^ level * 205 - 1) := by
  refine (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_node (w := fun _ => 1)
    (fun x => (isQueryBoundP_iff_isChargeBound p _ _).1 (hH x))
      (fun _ _ _ => (isQueryBoundP_iff_isChargeBound p _ _).1 (hprf _ _ _))
      publicParam layer level j).mono ?_
  have := Nat.one_le_two_pow (n := level)
  omega

/-- A build at `level` is `2^level` leaves and `2^level - 1` hashes. -/
theorem isQueryBoundP_build (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (level j : Nat) :
    IsQueryBoundP (build H publicParam prf layer level j) p (2 ^ level * 205 - 1) := by
  refine (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_build (w := fun _ => 1)
    (fun x => (isQueryBoundP_iff_isChargeBound p _ _).1 (hH x))
      (fun _ _ _ => (isQueryBoundP_iff_isChargeBound p _ _).1 (hprf _ _ _))
      publicParam layer level j).mono ?_
  have := Nat.one_le_two_pow (n := level)
  omega

/-- A key's path is the `16` nodes beside it, one per level. -/
theorem isQueryBoundP_path (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (e : Nat) :
    IsQueryBoundP (path H publicParam prf layer e) p (2 ^ 16 * 205 - 205) :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_path (w := fun _ => 1)
    (fun x => (isQueryBoundP_iff_isChargeBound p _ _).1 (hH x))
      (fun _ _ _ => (isQueryBoundP_iff_isChargeBound p _ _).1 (hprf _ _ _))
      publicParam layer e).mono
      (by norm_num)

/-- The public parameter is one derivation. -/
theorem isQueryBoundP_publicParamOf
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1) :
    IsQueryBoundP (publicParamOf prf) p 1 :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <|
    isChargeBound_publicParamOf (w := fun _ => 1) fun _ _ _ =>
      (isQueryBoundP_iff_isChargeBound p _ _).1 (hprf _ _ _)

/-- The base of the randomizer trials is one derivation. -/
theorem isQueryBoundP_randomizerBase
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) (msg : Array UInt64) :
    IsQueryBoundP (randomizerBase publicParam prf layer e msg) p 1 :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| isChargeBound_randomizerBase (w := fun _ => 1)
    (fun _ _ _ => (isQueryBoundP_iff_isChargeBound p _ _).1 (hprf _ _ _)) publicParam layer e msg

/-- The codeword search is one digest per trial. -/
theorem isQueryBoundP_findCodeword (hH : ∀ x, IsQueryBoundP (H x) p 1) (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) (msg : Array UInt64) (base : Randomizer) (c fuel : Nat) :
    IsQueryBoundP (Internal.findCodeword H publicParam layer e msg base c fuel) p fuel :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_findCodeword (w := fun _ => 1)
    (fun x => (isQueryBoundP_iff_isChargeBound p _ _).1 (hH x))
      publicParam layer e msg base c fuel).mono (le_of_eq (Nat.mul_one _))

/-- A one-time signature is the base, at most `2^32` trials, the starts and `174` steps. -/
theorem isQueryBoundP_otsSign (hH : ∀ x, IsQueryBoundP (H x) p 1)
    (hprf : ∀ publicParam a suffix, IsQueryBoundP (prf publicParam a suffix) p 1)
      (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) (msg : Array UInt64) :
    IsQueryBoundP (otsSign H publicParam prf layer e msg) p (2 ^ 32 + 204) :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_otsSign (w := fun _ => 1)
    (fun x => (isQueryBoundP_iff_isChargeBound p _ _).1 (hH x))
      (fun _ _ _ => (isQueryBoundP_iff_isChargeBound p _ _).1 (hprf _ _ _))
      publicParam layer e msg).mono
      (by simp [MAX_RANDOMIZER_TRIALS])

/-- The leaf of a one-time signature is a digest, at most `174` steps and one hash. -/
theorem isQueryBoundP_otsLeaf (hH : ∀ x, IsQueryBoundP (H x) p 1) (publicParam : PublicParam)
    (layer : Layer) (e : UInt32) (msg : Array UInt64) (rho : Randomizer) (y : Vector Digest V) :
    IsQueryBoundP (otsLeaf H publicParam layer e msg rho y) p 176 :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_otsLeaf (w := fun _ => 1)
    (fun x => (isQueryBoundP_iff_isChargeBound p _ _).1 (hH x)) publicParam layer e msg rho
      y).mono (by norm_num)

/-- The root one layer's signature leads to is a leaf and a climb of `16` levels. -/
theorem isQueryBoundP_layerRoot (hH : ∀ x, IsQueryBoundP (H x) p 1) (publicParam : PublicParam)
    (layer : Layer) (e : Nat) (msg : Array UInt64) (sig : LayerSignature) :
    IsQueryBoundP (layerRoot H publicParam layer e msg sig) p 192 :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_layerRoot (w := fun _ => 1)
    (fun x => (isQueryBoundP_iff_isChargeBound p _ _).1 (hH x)) publicParam layer e msg
      sig).mono (by norm_num)

/-- Verification is the roots of both layers. -/
theorem isQueryBoundP_verifyWith (hH : ∀ x, IsQueryBoundP (H x) p 1) (pk : PublicKey)
    (msg : Message) (sig : Signature) :
    IsQueryBoundP (verifyWith H pk msg sig) p 384 :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_verifyWith (w := fun _ => 1)
    (fun x => (isQueryBoundP_iff_isChargeBound p _ _).1 (hH x)) pk msg sig).mono (by norm_num)

end Algorithms

end EthLib.Cryptography.Xmss

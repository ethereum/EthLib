/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.SigningReachability
public import EthereumXMSSHypertree.Representation
public import Mathlib.Data.Fintype.Card

/-!
# Complete source verification invocation counts

The source recovery and climb computations run in the same full-input counting
interpreter as source signing. Hash invocations and Keccak permutations are
different units: verification uses at most 172 full-hash invocations.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography
open Xmss Xmss.Constants
open Reachability SigningReachability

namespace VerificationReachability

/-- Admitted source digits leave exactly 68 chain steps for recovery. -/
theorem remaining_steps {d : Digest} {x : Vector (Fin CHAIN_LENGTH) V}
    (hx : codeword? d = some x) : ∑ i : Fin V, (CHAIN_LENGTH - 1 - (x[i]).val) = 68 := by
  have hterm (i : Fin V) : (x[i]).val + (CHAIN_LENGTH - 1 - (x[i]).val) = 3 := by
    have := (x[i]).isLt
    simp only [CHAIN_LENGTH] at *
    omega
  have hsum : (∑ i : Fin V, (x[i]).val) +
      (∑ i : Fin V, (CHAIN_LENGTH - 1 - (x[i]).val)) = 174 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : Fin V, 3 := Finset.sum_congr rfl (fun i _ => hterm i)
      _ = 174 := by
        rw [Finset.sum_const, Finset.card_fin]
        rfl
  rw [sum_of_codeword hx] at hsum
  simp only [TARGET_SUM] at hsum
  omega

/-- The actual source recovery chains make exactly the 68 remaining invocations. -/
theorem recovery_chains_calls (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (values : Vector Digest V) (d : Digest)
    (x : Vector (Fin CHAIN_LENGTH) V) (hx : codeword? d = some x) :
    (HashSig.ofFnInOrder V (fun i => Xmss.chain (countedHash H) pp layer e i x[i]
      (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega) values[i])).calls = 68 := by
  rw [ofFnInOrder_calls_sum]
  simp only [chain_calls]
  exact remaining_steps hx

/-- The source's deterministic codeword-decoding observation at a claimed OTS signature. -/
@[expose] def decoding (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer) :=
  codeword? ((messageDigest (pureHash H) pp layer e msg rho).run)

/-- Rejected source OTS recovery costs its single message digest and stops before all chains. -/
theorem otsLeaf_calls_none (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer) (values : Vector Digest V)
    (h : decoding H pp layer e msg rho = none) :
    (otsLeaf (countedHash H) pp layer e msg rho values).calls = 1 := by
  simp only [otsLeaf, bind_calls, messageDigest_result]
  rw [show codeword? ((messageDigest (pureHash H) pp layer e msg rho).run) = none from h]
  rfl

/-- Accepted source OTS recovery costs one digest, 68 steps, and one leaf hash. -/
theorem otsLeaf_calls_some (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer) (values : Vector Digest V)
    (x : Vector (Fin CHAIN_LENGTH) V) (h : decoding H pp layer e msg rho = some x) :
    (otsLeaf (countedHash H) pp layer e msg rho values).calls = 70 := by
  simp only [otsLeaf, bind_calls, messageDigest_result]
  rw [show codeword? ((messageDigest (pureHash H) pp layer e msg rho).run) = some x from h]
  simp only [bind_calls]
  rw [recovery_chains_calls H pp layer e values _ x h]
  rfl

/-- The source OTS recovery returns no leaf exactly when its digest is rejected. -/
theorem otsLeaf_isSome (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer) (values : Vector Digest V) :
    (otsLeaf (countedHash H) pp layer e msg rho values).result.isSome =
      (decoding H pp layer e msg rho).isSome := by
  simp only [otsLeaf, bind_result, messageDigest_result, decoding]
  generalize codeword? ((messageDigest (pureHash H) pp layer e msg rho).run) = outcome
  cases outcome with
  | none => rfl
  | some x => simp only [bind_result, pure_result]; rfl

/-- Climbing a source path costs exactly one parent hash for each supplied sibling. -/
theorem climb_calls (H : ByteArray → Vector UInt8 32) (pp : PublicParam) (layer : Layer)
    (level j : Nat) (current : Digest) (siblings : List Digest) :
    (Merkle.climb (nodeHash (countedHash H) pp layer) level j current siblings).calls =
      siblings.length := by
  induction siblings generalizing level j current with
  | nil => rfl
  | cons sibling rest ih =>
    simp only [Merkle.climb, bind_calls]
    rw [ih]
    change 1 + rest.length = rest.length + 1
    omega

/-- Source layer recovery returns a root exactly when its OTS digest decodes. -/
theorem layerRoot_isSome (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature) :
    (layerRoot (countedHash H) pp layer e msg sig).result.isSome =
      (decoding H pp layer (UInt32.ofNat e) msg sig.randomizer).isSome := by
  rw [← otsLeaf_isSome H pp layer (UInt32.ofNat e) msg sig.randomizer sig.chainValues]
  simp only [layerRoot, bind_result]
  generalize (otsLeaf (countedHash H) pp layer (UInt32.ofNat e) msg
    sig.randomizer sig.chainValues).result = outcome
  cases outcome with
  | none => rfl
  | some leaf => simp only [bind_result, pure_result]; rfl

/-- Rejected source layer recovery costs only its initial message digest. -/
theorem layerRoot_calls_none (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature)
    (h : decoding H pp layer (UInt32.ofNat e) msg sig.randomizer = none) :
    (layerRoot (countedHash H) pp layer e msg sig).calls = 1 := by
  have ho : (otsLeaf (countedHash H) pp layer (UInt32.ofNat e) msg
      sig.randomizer sig.chainValues).result = none := by
    apply Option.not_isSome_iff_eq_none.mp
    rw [otsLeaf_isSome, h]
    exact Bool.false_ne_true
  simp only [layerRoot, bind_calls]
  rw [ho, pure_calls, Nat.add_zero, otsLeaf_calls_none H pp layer _ msg _ _ h]

/-- Accepted source layer recovery costs 70 OTS hashes and sixteen climb hashes. -/
theorem layerRoot_calls_some (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature)
    (x : Vector (Fin CHAIN_LENGTH) V)
    (h : decoding H pp layer (UInt32.ofNat e) msg sig.randomizer = some x) :
    (layerRoot (countedHash H) pp layer e msg sig).calls = 86 := by
  have hi : (otsLeaf (countedHash H) pp layer (UInt32.ofNat e) msg
      sig.randomizer sig.chainValues).result.isSome := by
    rw [otsLeaf_isSome, h]
    rfl
  obtain ⟨leaf, ho⟩ := Option.isSome_iff_exists.mp hi
  simp only [layerRoot, bind_calls]
  rw [ho]
  simp only [bind_calls, pure_calls, Nat.add_zero, fold, climb_calls, Vector.length_toList]
  rw [otsLeaf_calls_some H pp layer _ msg _ _ x h]
  rfl

/-- A source layer returning failure made exactly its initial message-digest call. -/
theorem layerRoot_calls_of_none (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature)
    (h : (layerRoot (countedHash H) pp layer e msg sig).result = none) :
    (layerRoot (countedHash H) pp layer e msg sig).calls = 1 := by
  have hi := layerRoot_isSome H pp layer e msg sig
  rw [h] at hi
  have hd : decoding H pp layer (UInt32.ofNat e) msg sig.randomizer = none := by
    apply Option.not_isSome_iff_eq_none.mp
    intro hp
    rw [← hi] at hp
    exact Bool.false_ne_true hp
  exact layerRoot_calls_none H pp layer e msg sig hd

/-- A source layer returning a root made all 86 recovery and climb invocations. -/
theorem layerRoot_calls_of_some (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature) (root : Digest)
    (h : (layerRoot (countedHash H) pp layer e msg sig).result = some root) :
    (layerRoot (countedHash H) pp layer e msg sig).calls = 86 := by
  have hi := layerRoot_isSome H pp layer e msg sig
  rw [h] at hi
  have hd : (decoding H pp layer (UInt32.ofNat e) msg sig.randomizer).isSome := hi.symm
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
  exact layerRoot_calls_some H pp layer e msg sig x hx

/-- Every source layer uses at most 86 full-hash invocations, including rejection. -/
theorem layerRoot_calls_le (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature) :
    (layerRoot (countedHash H) pp layer e msg sig).calls ≤ 86 := by
  cases h : (layerRoot (countedHash H) pp layer e msg sig).result with
  | none => rw [layerRoot_calls_of_none H pp layer e msg sig h]; decide
  | some root => rw [layerRoot_calls_of_some H pp layer e msg sig root h]

/-- The actual first verification phase, retaining the signature's embedded global index. -/
@[expose] def bottomRecovery (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (msg : Message) (sig : Signature) :=
  layerRoot (countedHash H) pk.publicParam .bottom sig.leafIndex.toNat (packBytes msg) sig.bottom

/-- The actual second verification phase, signing the recovered bottom root. -/
@[expose] def topRecovery (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (sig : Signature) (bottomRoot : Digest) :=
  layerRoot (countedHash H) pk.publicParam .top (bottomTree sig.leafIndex)
    (packBytes bottomRoot) sig.top

/-- Bottom decoding failure rejects before any recovery-chain or top-layer invocation. -/
theorem verifyWith_calls_bottom_none (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (msg : Message) (sig : Signature) (hb : (bottomRecovery H pk msg sig).result = none) :
    (verifyWith (countedHash H) pk msg sig).calls = 1 := by
  simp only [verifyWith, bind_calls]
  rw [show (layerRoot (countedHash H) pk.publicParam .bottom sig.leafIndex.toNat
    (packBytes msg) sig.bottom).result = none from hb]
  simp only [pure_calls, Nat.add_zero]
  exact layerRoot_calls_of_none H pk.publicParam .bottom _ _ _ hb

/-- Top decoding failure follows all 86 bottom calls and its own single digest call. -/
theorem verifyWith_calls_top_none (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (msg : Message) (sig : Signature) (bottomRoot : Digest)
    (hb : (bottomRecovery H pk msg sig).result = some bottomRoot)
    (ht : (topRecovery H pk sig bottomRoot).result = none) :
    (verifyWith (countedHash H) pk msg sig).calls = 87 := by
  simp only [verifyWith, bind_calls]
  rw [show (layerRoot (countedHash H) pk.publicParam .bottom sig.leafIndex.toNat
    (packBytes msg) sig.bottom).result = some bottomRoot from hb]
  simp only [bind_calls]
  rw [show (layerRoot (countedHash H) pk.publicParam .top (bottomTree sig.leafIndex)
    (packBytes bottomRoot) sig.top).result = none from ht]
  simp only [pure_calls, Nat.add_zero]
  rw [layerRoot_calls_of_some H pk.publicParam .bottom _ _ _ bottomRoot hb,
    layerRoot_calls_of_none H pk.publicParam .top _ _ _ ht]

/-- Both decoded layers cost 172 full-hash invocations before the final root comparison. -/
theorem verifyWith_calls_both_some (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (msg : Message) (sig : Signature) (bottomRoot root : Digest)
    (hb : (bottomRecovery H pk msg sig).result = some bottomRoot)
    (ht : (topRecovery H pk sig bottomRoot).result = some root) :
    (verifyWith (countedHash H) pk msg sig).calls = 172 := by
  simp only [verifyWith, bind_calls]
  rw [show (layerRoot (countedHash H) pk.publicParam .bottom sig.leafIndex.toNat
    (packBytes msg) sig.bottom).result = some bottomRoot from hb]
  simp only [bind_calls]
  rw [show (layerRoot (countedHash H) pk.publicParam .top (bottomTree sig.leafIndex)
    (packBytes bottomRoot) sig.top).result = some root from ht]
  simp only [pure_calls, Nat.add_zero]
  rw [layerRoot_calls_of_some H pk.publicParam .bottom _ _ _ bottomRoot hb,
    layerRoot_calls_of_some H pk.publicParam .top _ _ _ root ht]

/-- Root mismatch rejects only after all 172 source verification invocations. -/
theorem verifyWith_root_mismatch (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (msg : Message) (sig : Signature) (bottomRoot root : Digest)
    (hb : (bottomRecovery H pk msg sig).result = some bottomRoot)
    (ht : (topRecovery H pk sig bottomRoot).result = some root) (hne : root ≠ pk.root) :
    (verifyWith (countedHash H) pk msg sig).result = false ∧
      (verifyWith (countedHash H) pk msg sig).calls = 172 := by
  constructor
  · simp only [verifyWith, bind_result]
    rw [show (layerRoot (countedHash H) pk.publicParam .bottom sig.leafIndex.toNat
      (packBytes msg) sig.bottom).result = some bottomRoot from hb]
    simp only [bind_result]
    rw [show (layerRoot (countedHash H) pk.publicParam .top (bottomTree sig.leafIndex)
      (packBytes bottomRoot) sig.top).result = some root from ht]
    simp [pure_result, hne]
  · exact verifyWith_calls_both_some H pk msg sig bottomRoot root hb ht

/-- Every claimed source signature uses at most 172 verification hash invocations. -/
theorem verifyWith_calls_le (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (msg : Message) (sig : Signature) :
    (verifyWith (countedHash H) pk msg sig).calls ≤ 172 := by
  cases hb : (bottomRecovery H pk msg sig).result with
  | none => rw [verifyWith_calls_bottom_none H pk msg sig hb]; decide
  | some bottomRoot =>
    cases ht : (topRecovery H pk sig bottomRoot).result with
    | none => rw [verifyWith_calls_top_none H pk msg sig bottomRoot hb ht]; decide
    | some root => rw [verifyWith_calls_both_some H pk msg sig bottomRoot root hb ht]

/-- Every recovery-chain invocation is retained in the full input log. -/
theorem sound_chain_true (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    Sound (fun _ => True)
      (Xmss.chain (countedHash H) pp layer e i start steps h value) := by
  induction steps with
  | zero => exact sound_pure _ _
  | succ steps ih =>
    apply sound_bind _ _ (ih (by omega))
    intro previous
    exact sound_th H pp _ _ trivial

/-- Count/log agreement holds for source OTS recovery, including rejected decoding. -/
theorem sound_otsLeaf_true (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer) (values : Vector Digest V) :
    Sound (fun _ => True) (otsLeaf (countedHash H) pp layer e msg rho values) := by
  apply sound_bind _ _ (sound_th H pp _ _ trivial)
  intro digest
  cases h : codeword? digest with
  | none => exact sound_pure _ _
  | some x =>
    apply sound_bind
    · apply sound_ofFnInOrder
      intro i
      exact sound_chain_true H pp layer e i _ _ _ values[i]
    · intro ends
      apply sound_bind _ _ (sound_th H pp _ _ trivial)
      intro leaf
      exact sound_pure _ _

/-- Source path climbing retains every parent-hash input, including repetitions. -/
theorem sound_climb_true (H : ByteArray → Vector UInt8 32) (pp : PublicParam) (layer : Layer)
    (level j : Nat) (current : Digest) (siblings : List Digest) :
    Sound (fun _ => True)
      (Merkle.climb (nodeHash (countedHash H) pp layer) level j current siblings) := by
  induction siblings generalizing level j current with
  | nil => exact sound_pure _ _
  | cons sibling rest ih =>
    apply sound_bind _ _ (sound_th H pp _ _ trivial)
    intro parent
    exact ih (level + 1) (j / 2) parent

/-- Source layer recovery retains every input before either rejection or its recovered root. -/
theorem sound_layerRoot_true (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature) :
    Sound (fun _ => True) (layerRoot (countedHash H) pp layer e msg sig) := by
  apply sound_bind _ _ (sound_otsLeaf_true H pp layer _ msg sig.randomizer sig.chainValues)
  intro outcome
  cases outcome with
  | none => exact sound_pure _ _
  | some leaf =>
    apply sound_bind _ _ (sound_climb_true H pp layer 0 e leaf sig.path.toList)
    intro root
    exact sound_pure _ _

/-- Complete source verification retains every full-byte hash invocation in order. -/
theorem sound_verifyWith_true (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (msg : Message) (sig : Signature) :
    Sound (fun _ => True) (verifyWith (countedHash H) pk msg sig) := by
  apply sound_bind _ _ (sound_layerRoot_true H pk.publicParam .bottom _ (packBytes msg) sig.bottom)
  intro bottomOutcome
  cases bottomOutcome with
  | none => exact sound_pure _ _
  | some bottomRoot =>
    apply sound_bind _ _
      (sound_layerRoot_true H pk.publicParam .top _ (packBytes bottomRoot) sig.top)
    intro topOutcome
    cases topOutcome with
    | none => exact sound_pure _ _
    | some root => exact sound_pure _ _

/-- The complete actual verification input log has at most 172 entries, retaining duplicates. -/
theorem verifyWith_inputs_length_le (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (msg : Message) (sig : Signature) :
    (verifyWith (countedHash H) pk msg sig).inputs.length ≤ 172 := by
  rw [← (sound_verifyWith_true H pk msg sig).1]
  exact verifyWith_calls_le H pk msg sig

/-- Bottom decoding failure returns false before any top recovery runs. -/
theorem verifyWith_result_bottom_none (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (msg : Message) (sig : Signature) (hb : (bottomRecovery H pk msg sig).result = none) :
    (verifyWith (countedHash H) pk msg sig).result = false := by
  simp only [verifyWith, bind_result]
  rw [show (layerRoot (countedHash H) pk.publicParam .bottom sig.leafIndex.toNat
    (packBytes msg) sig.bottom).result = none from hb]
  rfl

/-- Top decoding failure returns false without making a final root comparison. -/
theorem verifyWith_result_top_none (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (msg : Message) (sig : Signature) (bottomRoot : Digest)
    (hb : (bottomRecovery H pk msg sig).result = some bottomRoot)
    (ht : (topRecovery H pk sig bottomRoot).result = none) :
    (verifyWith (countedHash H) pk msg sig).result = false := by
  simp only [verifyWith, bind_result]
  rw [show (layerRoot (countedHash H) pk.publicParam .bottom sig.leafIndex.toNat
    (packBytes msg) sig.bottom).result = some bottomRoot from hb]
  simp only [bind_result]
  rw [show (layerRoot (countedHash H) pk.publicParam .top (bottomTree sig.leafIndex)
    (packBytes bottomRoot) sig.top).result = none from ht]
  rfl

/-- An outer-epoch mismatch is rejected with no full-hash invocation. -/
theorem verifyAtEpochWith_calls_mismatch (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (epoch : Epoch) (msg : Message) (sig : Signature)
    (h : leafIndexEquiv sig.leafIndex ≠ epoch) :
    (verifyAtEpochWith (countedHash H) pk epoch msg sig).calls = 0 := by
  rw [verifyAtEpochWith_mismatch (countedHash H) pk epoch msg sig h]
  rfl

/-- The explicit outer-epoch source adapter also has the unconditional 172-call bound. -/
theorem verifyAtEpochWith_calls_le (H : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (epoch : Epoch) (msg : Message) (sig : Signature) :
    (verifyAtEpochWith (countedHash H) pk epoch msg sig).calls ≤ 172 := by
  by_cases h : leafIndexEquiv sig.leafIndex = epoch
  · rw [verifyAtEpochWith_eq (countedHash H) pk epoch msg sig h]
    exact verifyWith_calls_le H pk msg sig
  · rw [verifyAtEpochWith_calls_mismatch H pk epoch msg sig h]
    decide

end VerificationReachability

end EthereumXMSSHypertree

module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Translate
public import EthLib.Cryptography.Proofs.Sphincs.Encoding

/-!
# Proofs: EthLib's codewords and one-time keys are the model's

A digest is a codeword in EthLib exactly when it is one in the model, with the same digits.

So EthLib's encoding with the query is the model's, and so is the leaf that a verifier recovers.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open SphincsSecurity.Concrete (tweakableHash)

/-! ## Codewords -/

/-- The model's digits of a word, as EthLib's codeword. -/
def ofEncoding (e : SphincsSecurity.Encoding) : Codeword :=
  Vector.ofFn fun i : Fin V => ⟨(e ⟨i.val, i.isLt⟩).val, (e ⟨i.val, i.isLt⟩).isLt⟩

/-- A digest's bytes read back as a number are the digest's number. -/
theorem bytesToUint_ofDigest (d : SphincsSecurity.Digest) : bytesToUint (ofDigest d) = d.toNat := by
  rw [ofDigest, ofBV_eq_uintToBytes, Base.bytesToUint_uintToBytes]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le d.isLt (by decide))

/-- EthLib's digits of a digest are the model's. -/
theorem digits_ofDigest (d : SphincsSecurity.Digest) :
    Internal.digits (ofDigest d) = ofEncoding (SphincsSecurity.TargetSum.digestEncoding d) := by
  apply Vector.ext
  intro i hi
  apply Fin.ext
  rw [digits_getElem_val, bytesToUint_ofDigest]
  simp only [ofEncoding, Vector.getElem_ofFn, SphincsSecurity.TargetSum.digestEncoding,
    SphincsSecurity.TargetSum.digitOffset, SphincsSecurity.winternitzBits]
  rw [show (4 : Nat) ^ i = 2 ^ (2 * i) by rw [pow_mul]; norm_num, BitVec.val_toFin,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- EthLib's digit sum of a model word is the model's. -/
theorem digitSum_ofEncoding (e : SphincsSecurity.Encoding) :
    Internal.digitSum (ofEncoding e) = SphincsSecurity.TargetSum.sum e := by
  rw [digitSum_eq_sum, SphincsSecurity.TargetSum.sum]
  simp only [ofEncoding, Fin.getElem_fin, Vector.getElem_ofFn]
  rfl

/-- A digest is a codeword in EthLib exactly when the model decodes it, with the same digits. -/
theorem codeword?_ofDigest (d : SphincsSecurity.Digest) :
    codeword? (ofDigest d) = (SphincsSecurity.TargetSum.decodeDigest d).map ofEncoding := by
  unfold codeword? SphincsSecurity.TargetSum.decodeDigest
  have ht : SphincsSecurity.targetSum = TARGET_SUM := rfl
  simp only [digits_ofDigest, digitSum_ofEncoding, SphincsSecurity.TargetSum.Valid, ht]
  by_cases h : SphincsSecurity.TargetSum.sum (SphincsSecurity.TargetSum.digestEncoding d)
      = TARGET_SUM <;> simp [h]

/-! ## The encoding and the recovered leaf -/

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSig.HashSpec m]

/-- EthLib's encoding of a message under a counter is the model's, with the same codeword. -/
theorem encode_queryH (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (leaf : SphincsSecurity.LeafIndex) (msg : ByteArray)
    (counter : UInt32) :
    encode (queryH (m := m)) (ofParam P) (keyOf lay tree leaf) msg counter
      = Option.map ofEncoding <$> SphincsSecurity.Concrete.encode (m := m) P lay tree leaf
          msg.data.toList (BitVec.ofNat 32 counter.toNat) := by
  rw [encode, th_queryH P _ _ (.encoding lay tree leaf)
    (msg.data.toList ++ SphincsSecurity.bytesLE 4 (BitVec.ofNat 32 counter.toNat))
    (toList_addrEncoding lay tree leaf)
    (by simp only [toList_data_append, toList_data_packBytes, toList_uintToBytes]; rfl)]
  simp only [SphincsSecurity.Concrete.encode, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, codeword?_ofDigest]

omit [HasQuery HashSig.HashSpec m] in
/-- EthLib's vector computed in order is the model's function computed in order. -/
theorem ofFnInOrder_eq_sequenceFin {α β : Type} :
    ∀ (n : Nat) (c : Fin n → m α) (g : α → β),
      ofFnInOrder n (fun i => g <$> c i)
        = (fun f => Vector.ofFn fun i => g (f i)) <$> SphincsSecurity.Concrete.sequenceFin c
  | 0, c, g => by
    simp only [ofFnInOrder, SphincsSecurity.Concrete.sequenceFin, map_pure]
    congr 1
  | n + 1, c, g => by
    simp only [ofFnInOrder, SphincsSecurity.Concrete.sequenceFin, map_bind, bind_map_left,
      map_pure]
    refine bind_congr fun head => ?_
    rw [ofFnInOrder_eq_sequenceFin n (fun i => c i.succ) g]
    simp only [bind_map_left]
    refine bind_congr fun tail => ?_
    congr 1
    apply Vector.ext
    intro i hi
    -- Entry 0 is the head, entry `i + 1` is entry `i` of the tail.
    cases i with
    | zero => simp
    | succ i => simp

/-- The model's chain values as EthLib's vector. -/
def ofChains (f : SphincsSecurity.ChainIndex → SphincsSecurity.Digest) : Vector Digest V :=
  Vector.ofFn fun i : Fin V => ofDigest (f ⟨i.val, i.isLt⟩)

/-- The leaf a verifier recovers from a one-time signature is the model's. -/
theorem otsLeaf_queryH (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (leaf : SphincsSecurity.LeafIndex) (msg : ByteArray)
    (counter : UInt32) (values : SphincsSecurity.ChainIndex → SphincsSecurity.Digest) :
    otsLeaf (queryH (m := m)) (ofParam P) (keyOf lay tree leaf) msg counter (ofChains values)
      = Option.map ofDigest <$> SphincsSecurity.Concrete.otsLeaf (m := m) P lay tree leaf
          msg.data.toList (BitVec.ofNat 32 counter.toNat) values := by
  unfold otsLeaf SphincsSecurity.Concrete.otsLeaf
  rw [encode_queryH, bind_map_left, map_bind]
  refine bind_congr fun r => ?_
  cases r with
  | none => simp
  | some enc =>
    simp only [Option.map_some]
    -- Each chain is the model's recovery, from the revealed value.
    have hchains : (ofFnInOrder V fun i =>
        chain (queryH (m := m)) (ofParam P) (keyOf lay tree leaf) i (ofEncoding enc)[i]
          (CHAIN_LENGTH - 1 - (ofEncoding enc)[i]) (by have := (ofEncoding enc)[i].isLt; omega)
          (ofChains values)[i])
        = ofFnInOrder V fun i => ofDigest <$> SphincsSecurity.Concrete.recoverChain (m := m) P
            lay tree leaf ⟨i.val, i.isLt⟩ (enc ⟨i.val, i.isLt⟩) (values ⟨i.val, i.isLt⟩) := by
      refine congrArg (ofFnInOrder V) (funext fun i => ?_)
      simp only [ofChains, ofEncoding, Fin.getElem_fin, Vector.getElem_ofFn]
      exact chain_queryH P lay tree leaf i _ _ _ _
    rw [hchains, ofFnInOrder_eq_sequenceFin V (fun i : Fin V =>
      SphincsSecurity.Concrete.recoverChain (m := m) P lay tree leaf ⟨i.val, i.isLt⟩
        (enc ⟨i.val, i.isLt⟩) (values ⟨i.val, i.isLt⟩)) ofDigest, bind_map_left, map_bind]
    refine bind_congr fun ends => ?_
    have h := otsLeafHash_queryH (m := m) P lay tree leaf ends
    simp only [map_bind, map_pure, Option.map_some]
    exact (congrArg (fun z => z >>= fun x => pure (some x)) h).trans (bind_map_left _ _ _)

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge

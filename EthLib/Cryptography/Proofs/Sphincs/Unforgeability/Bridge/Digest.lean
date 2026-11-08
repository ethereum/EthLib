module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Fors
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.DigestView
public import EthLib.Cryptography.Proofs.Sphincs.TweakableHash

/-!
# Proofs: EthLib's message digest is the model's

EthLib's message digest makes the model's two digest calls, in the same order.

Both read the first 34 bytes of the calls as FIPS 205's Algorithm 19 does.

```text
    [ md: 30 | tree: 3 | leaf: 1 ]
```

EthLib keeps those bytes, and the model packs the fields they hold into one bit vector.

The index sits in its low 26 bits, and the leaf of tree `κ` in bits `26 + 10 κ` to `35 + 10 κ`.

So EthLib's index and leaves are the model's, read from the same calls.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open SphincsSecurity.Concrete (sequenceFin)

/-- The model's digest calls as EthLib's digest: the first 34 of their bytes, call 0 first. -/
def ofOutputs (outs : SphincsSecurity.DigestCall → HashSig.HashOutput) : MessageDigest :=
  trunc DIGEST_BYTES
    (Vector.ofFn fun call : Fin DIGEST_CALLS => ofOutput (outs ⟨call.val, call.isLt⟩)).flatten

/-- The vectors of a function, joined in order, as a list. -/
theorem toList_flatten_ofFn {α : Type} {n k : Nat} (g : Fin n → Vector α k) :
    (Vector.ofFn g).flatten.toList = (List.ofFn fun i => (g i).toList).flatten := by
  simp [Vector.flatten, Vector.toList, Array.toList_flatten, Array.toList_ofFn, List.map_ofFn,
    Function.comp_def]

/-- EthLib's digest lists the first 34 bytes of the model's bytes of the calls. -/
theorem toList_ofOutputs (outs : SphincsSecurity.DigestCall → HashSig.HashOutput) :
    (ofOutputs outs).toList = (SphincsSecurity.digestOutputBytes outs).take DIGEST_BYTES := by
  rw [ofOutputs, toList_trunc, toList_flatten_ofFn]
  simp only [toList_ofOutput]
  rfl

/-! ## The model's fields -/

/-- The model's index of the calls is the index value of their bytes. -/
theorem val_digestIndex_truncate (outs : SphincsSecurity.DigestCall → HashSig.HashOutput) :
    (SphincsSecurity.Concrete.digestIndex (SphincsSecurity.truncateMessageDigest outs)).val
      = SphincsSecurity.digestIndexValue (SphincsSecurity.digestOutputBytes outs) := by
  simp only [SphincsSecurity.Concrete.digestIndex, SphincsSecurity.truncateMessageDigest,
    BitVec.val_toFin, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  generalize SphincsSecurity.digestOutputBytes outs = bytes
  apply Nat.eq_of_testBit_eq
  intro q
  have hlt := SphincsSecurity.Concrete.digestIndexValue_lt bytes
  simp only [Nat.testBit_mod_two_pow]
  by_cases hq : q < SphincsSecurity.totalHeight
  · have hq' : q < SphincsSecurity.messageDigestBits := lt_of_lt_of_le hq (by decide)
    simp only [hq, hq', decide_true, Bool.true_and,
      SphincsSecurity.Concrete.testBit_digestFieldsValue, ↓reduceIte]
  · -- The index is below `2^26`, so its bits from 26 on are zero.
    have hzero := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hq)))
    simp only [hq, decide_false, Bool.false_and, hzero]

/-- The model's leaf of tree `κ` is the 10 bits from bit `10 κ` of the bytes, the first on top. -/
theorem val_digestLeaves_truncate (outs : SphincsSecurity.DigestCall → HashSig.HashOutput)
    (κ : SphincsSecurity.FTree) :
    (SphincsSecurity.Concrete.digestLeaves (SphincsSecurity.truncateMessageDigest outs) κ).val
      = SphincsSecurity.msbField (SphincsSecurity.digestOutputBytes outs)
          (SphincsSecurity.forsHeight * κ.val) SphincsSecurity.forsHeight := by
  simp only [SphincsSecurity.Concrete.digestLeaves, SphincsSecurity.truncateMessageDigest,
    SphincsSecurity.Concrete.leafOffset, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    BitVec.toNat_ofNat]
  generalize SphincsSecurity.digestOutputBytes outs = bytes
  apply Nat.eq_of_testBit_eq
  intro i
  have hκ : κ.val < 24 := κ.isLt
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < SphincsSecurity.forsHeight
  · have hi' : i < 10 := hi
    -- Bit `i` of the field is bit `26 + 10 κ + i` of the packed fields.
    have hbits : SphincsSecurity.totalHeight + SphincsSecurity.forsHeight * κ.val + i
        < SphincsSecurity.messageDigestBits := by
      change 26 + 10 * κ.val + i < 266
      omega
    have hdiv : (SphincsSecurity.totalHeight + SphincsSecurity.forsHeight * κ.val + i
        - SphincsSecurity.totalHeight) / SphincsSecurity.forsHeight = κ.val := by
      change (26 + 10 * κ.val + i - 26) / 10 = κ.val
      omega
    have hmod : (SphincsSecurity.totalHeight + SphincsSecurity.forsHeight * κ.val + i
        - SphincsSecurity.totalHeight) % SphincsSecurity.forsHeight = i := by
      change (26 + 10 * κ.val + i - 26) % 10 = i
      omega
    have hlow : ¬ SphincsSecurity.totalHeight + SphincsSecurity.forsHeight * κ.val + i
        < SphincsSecurity.totalHeight := by omega
    have hκt : κ.val < SphincsSecurity.forsTrees := κ.isLt
    simp only [hi, hbits, decide_true, Bool.true_and,
      SphincsSecurity.Concrete.testBit_digestFieldsValue, hlow, ↓reduceIte, hdiv, hmod, hκt,
      ↓reduceDIte]
  · have hzero := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le
      (SphincsSecurity.Concrete.msbField_lt bytes (SphincsSecurity.forsHeight * κ.val)
        SphincsSecurity.forsHeight)
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)))
    simp only [hi, decide_false, Bool.false_and, hzero]

/-! ## EthLib's fields -/

/-- Two bit readers that agree on a field read the same field. -/
theorem foldl_bits_congr (b b' : Nat → Nat) (offset : Nat) :
    ∀ width, (∀ j < width, b (offset + j) = b' (offset + j)) →
      (List.range width).foldl (fun value j => 2 * value + b (offset + j)) 0
        = (List.range width).foldl (fun value j => 2 * value + b' (offset + j)) 0
  | 0, _ => rfl
  | width + 1, h => by
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [foldl_bits_congr b b' offset width (fun j hj => h j (by omega)), h width (by omega)]

/-- EthLib's bit `p < 272` of its digest is the model's bit `p` of the bytes of the calls. -/
theorem msbBit_ofOutputs (outs : SphincsSecurity.DigestCall → HashSig.HashOutput) (p : Nat)
    (hp : p < 8 * DIGEST_BYTES) :
    msbBit (ofOutputs outs) p
      = SphincsSecurity.msbBit (SphincsSecurity.digestOutputBytes outs) p := by
  have hbyte : p / 8 < DIGEST_BYTES := by omega
  have hget : (ofOutputs outs)[p / 8]? = (SphincsSecurity.digestOutputBytes outs)[p / 8]? := by
    rw [← Vector.getElem?_toList, toList_ofOutputs, List.getElem?_take_of_lt hbyte]
  simp only [msbBit, SphincsSecurity.msbBit, hget, List.getD_eq_getElem?_getD,
    Nat.shiftRight_eq_div_pow]

/-- EthLib's index is the model's index of the same calls. -/
theorem digestIndex_ofOutputs (outs : SphincsSecurity.DigestCall → HashSig.HashOutput) :
    digestIndex (ofOutputs outs)
      = (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest outs)).val := by
  rw [val_digestIndex_truncate]
  -- Both read bytes 30 to 32 as the tree and byte 33 as the leaf, inside the first 34 bytes.
  have htree : ((ofOutputs outs).toList.drop MD_BYTES).take TREE_INDEX_BYTES
      = ((SphincsSecurity.digestOutputBytes outs).drop SphincsSecurity.mdBytes).take
          SphincsSecurity.treeIndexBytes := by
    rw [toList_ofOutputs, List.drop_take, List.take_take]
    rfl
  have hleaf : ((ofOutputs outs).toList.drop (MD_BYTES + TREE_INDEX_BYTES)).take LEAF_INDEX_BYTES
      = ((SphincsSecurity.digestOutputBytes outs).drop
          (SphincsSecurity.mdBytes + SphincsSecurity.treeIndexBytes)).take
          SphincsSecurity.leafIndexBytes := by
    rw [toList_ofOutputs, List.drop_take, List.take_take]
    rfl
  simp only [digestIndex, digestTree, digestLeaf, SphincsSecurity.digestIndexValue, htree, hleaf,
    beInt_eq_bytesToNat]
  rfl

/-- EthLib's leaves are the model's leaves of the same calls. -/
theorem digestLeaves_ofOutputs (outs : SphincsSecurity.DigestCall → HashSig.HashOutput) :
    digestLeaves (ofOutputs outs)
      = ofLeaves (SphincsSecurity.Concrete.digestLeaves
          (SphincsSecurity.truncateMessageDigest outs)) := by
  apply Vector.ext
  intro i hi
  simp only [digestLeaves, ofLeaves, Vector.getElem_ofFn]
  apply Fin.ext
  rw [val_digestLeaves_truncate]
  simp only [FORS_TREES] at hi
  -- Every bit of a leaf field sits in the first 30 bytes.
  exact foldl_bits_congr _ _ _ _ fun j hj => msbBit_ofOutputs outs _ (by
    change j < 10 at hj
    simp only [FORS_HEIGHT, DIGEST_BYTES, MD_BYTES, TREE_INDEX_BYTES, LEAF_INDEX_BYTES, HEIGHT,
      TOP_HEIGHT, LOWER_HEIGHT, FORS_TREES]
    omega)

section Query

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSig.HashSpec m]

/-- EthLib's message digest is the model's digest calls, in EthLib's bytes. -/
theorem messageDigest_queryH (P : SphincsSecurity.PublicParameter) (root : SphincsSecurity.Digest)
    (msg : SphincsSecurity.Message) (rho : SphincsSecurity.Randomness) :
    hMsg (queryH (m := m)) (ofRandomizer rho) (ofParam P) (ofDigest root) (ofMessage msg)
      = ofOutputs <$> sequenceFin (m := m)
          (SphincsSecurity.Concrete.messageDigestCall P root msg rho) := by
  have h : DIGEST_CALLS = SphincsSecurity.digestCalls := rfl
  have hcalls : (fun call : Fin DIGEST_CALLS => queryH (m := m) (packBytes (ofRandomizer rho)
      ++ packBytes (ofParam P) ++ packBytes (ofDigest root) ++ packBytes (ofMessage msg)
      ++ packBytes (toByte 4 call.val)))
      = fun call => (ofOutput <$> SphincsSecurity.Concrete.messageDigestCall (m := m) P root msg
          rho (Fin.cast h call) : m (Vector UInt8 32)) :=
    funext fun call => digestCall_queryH P root msg rho (Fin.cast h call)
  rw [hMsg, hcalls, ofFnInOrder_eq_sequenceFin_cast (β := Vector UInt8 32) h
    (SphincsSecurity.Concrete.messageDigestCall (m := m) P root msg rho) ofOutput]
  simp only [bind_pure_comp, Functor.map_map]
  rfl

end Query

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge

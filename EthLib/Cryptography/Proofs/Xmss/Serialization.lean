module

public import EthLib.Cryptography.Xmss.Serialization
public import EthLib.Cryptography.Proofs.Xmss.Types
public import EthLib.Cryptography.Proofs.Xmss.Words
public import EthLib.Cryptography.Proofs.HashSig

/-!
# Proofs: leanXMSS byte encodings

The encodings are bijections between objects and byte strings of the declared length.

- Decoding an encoding returns the object.
- Every string of the declared length is an encoding.
- Every string of another length is rejected.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open Constants

/-! ## Digests and their bytes -/

/-- Digests read from a field whose bytes are the bytes of some digests are those digests. -/
theorem splitDigests_eq {n : Nat} {b : ByteArray} {offset : Nat} {ds : Vector Digest n}
    (h : offset + n * 16 ≤ b.size)
    (hr : readBytes b offset (n * 16) h = (ds.map (·.bytes)).flatten) :
    splitDigests n b offset = ds := by
  apply Vector.ext
  intro i hi
  simp only [splitDigests, Vector.getElem_ofFn]
  apply Hash.Keccak.Lanes2.bytes_injective
  rw [Hash.Keccak.Lanes2.bytes_read _ _ (by omega)]
  apply Vector.ext
  intro j hj
  -- Byte `j` of digest `i` is byte `16 i + j` of the field.
  have := congrArg (fun v => v[i * 16 + j]'(by omega)) hr
  have hq : (i * 16 + j) / 16 = i := by omega
  have hm : (i * 16 + j) % 16 = j := by omega
  simp only [Base.readBytes_eq_ofFn_data, Vector.getElem_ofFn, Vector.getElem_flatten,
    Vector.getElem_map, hq, hm] at this ⊢
  exact (getElem_congr_idx (by omega)).trans this

/-- The bytes of the digests read from a field are the bytes of the field. -/
theorem flatten_splitDigests {n : Nat} {b : ByteArray} {offset : Nat}
    (h : offset + n * 16 ≤ b.size) :
    ((splitDigests n b offset).map (·.bytes)).flatten = readBytes b offset (n * 16) h := by
  apply Vector.ext
  intro k hk
  have hb : offset + 16 * (k / 16) + 16 ≤ b.size := by omega
  simp only [Vector.getElem_flatten, Vector.getElem_map, splitDigests, Vector.getElem_ofFn,
    Hash.Keccak.Lanes2.bytes_read _ _ hb, Base.readBytes_eq_ofFn_data]
  exact getElem_congr_idx (by omega)

/-- A list of `n` digests packs to `16 n` bytes. -/
@[simp] theorem size_packDigests {n : Nat} (ds : Vector Digest n) :
    (packDigests ds).size = n * 16 := by
  simp [packDigests]

/-! ## Sizes -/

/-- A public key encodes to 32 bytes. -/
@[simp] theorem size_encodePublicKey (pk : PublicKey) :
    (encodePublicKey pk).size = PUB_KEY_SIZE := by
  simp [encodePublicKey, PUB_KEY_SIZE, DIGEST_LEN, PUBLIC_PARAM_LEN]

/-- A layer's signature encodes to 1200 bytes. -/
@[simp] theorem size_encodeLayerSignature (sig : LayerSignature) :
    (encodeLayerSignature sig).size = LAYER_SIG_SIZE := by
  simp [encodeLayerSignature, LAYER_SIG_SIZE, RANDOMIZER_LEN, DIGEST_LEN]

/-- A signature encodes to 2404 bytes. -/
@[simp] theorem size_encodeSignature (sig : Signature) :
    (encodeSignature sig).size = SIG_SIZE := by
  simp only [encodeSignature, ByteArray.size_append, size_packBytes,
    size_encodeLayerSignature, SIG_SIZE]
  omega

/-- Two lanes read back from their bytes in the middle of a concatenation. -/
theorem lanes2Read_middle {b a c : ByteArray} {w : Lanes2} {offset : Nat}
    (hb : b = a ++ packBytes w.bytes ++ c) (ho : offset = a.size) :
    Hash.Keccak.Lanes2.read b offset = w := by
  have h : offset + 16 ≤ b.size := by subst hb ho; simp
  apply Hash.Keccak.Lanes2.bytes_injective
  rw [Hash.Keccak.Lanes2.bytes_read _ _ h, HashSig.readBytes_middle hb ho h]

/-- A layer's signature reads back from its place in a concatenation. -/
theorem decodeLayerSignature_middle {b a c : ByteArray} {sig : LayerSignature} {offset : Nat}
    (hb : b = a ++ encodeLayerSignature sig ++ c) (ho : offset = a.size)
    (h : offset + LAYER_SIG_SIZE ≤ b.size) :
    decodeLayerSignature b offset h = sig := by
  -- Regroup so each field is the middle of its own concatenation.
  have hr : b = a ++ packBytes sig.randomizer.bytes
      ++ (packDigests sig.chainValues ++ packDigests sig.path ++ c) := by
    rw [hb, encodeLayerSignature]
    simp only [ByteArray.append_assoc]
  have hc : b = (a ++ packBytes sig.randomizer.bytes)
      ++ packBytes (sig.chainValues.map (·.bytes)).flatten ++ (packDigests sig.path ++ c) := by
    rw [hb, encodeLayerSignature]
    simp only [ByteArray.append_assoc, packDigests]
  have hp : b = (a ++ packBytes sig.randomizer.bytes ++ packDigests sig.chainValues)
      ++ packBytes (sig.path.map (·.bytes)).flatten ++ c := by
    rw [hb, encodeLayerSignature]
    simp only [ByteArray.append_assoc, packDigests]
  -- Each field starts where the previous one ends.
  have r := lanes2Read_middle hr ho
  have c' := HashSig.readBytes_middle hc (offset := offset + RANDOMIZER_LEN)
    (by simp [ho, RANDOMIZER_LEN]) (by simp only [LAYER_SIG_SIZE, DIGEST_LEN] at h ⊢; omega)
  have p := HashSig.readBytes_middle hp (offset := offset + RANDOMIZER_LEN + V * DIGEST_LEN)
    (by simp [ho, RANDOMIZER_LEN, DIGEST_LEN])
    (by simp only [LAYER_SIG_SIZE, DIGEST_LEN] at h ⊢; omega)
  simp only [decodeLayerSignature, r, splitDigests_eq _ c', splitDigests_eq _ p]

/-! ## Round trips -/

/-- Decoding an encoded public key returns it. -/
@[simp] theorem decodePublicKey_encodePublicKey (pk : PublicKey) :
    decodePublicKey (encodePublicKey pk) = .ok pk := by
  rw [decodePublicKey, ite_eq_left (size_encodePublicKey pk)]
  -- The root is the first field, the public parameter the one after it.
  have root := lanes2Read_middle (b := encodePublicKey pk) (a := ByteArray.empty)
    (c := packBytes pk.publicParam.bytes) (w := pk.root) (offset := 0)
    (by simp [encodePublicKey, ByteArray.empty_append]) (by simp)
  have param := lanes2Read_middle (b := encodePublicKey pk) (a := packBytes pk.root.bytes)
    (c := ByteArray.empty) (w := pk.publicParam) (offset := DIGEST_LEN)
    (by simp [encodePublicKey, ByteArray.append_empty]) (by simp [DIGEST_LEN])
  simp only [root, param]

/-- Decoding an encoded signature returns it. -/
@[simp] theorem decodeSignature_encodeSignature (sig : Signature) :
    decodeSignature (encodeSignature sig) = .ok sig := by
  rw [decodeSignature, dite_eq_left (size_encodeSignature sig)]
  -- The leaf index is the first four bytes, as a little-endian word.
  have idx := HashSig.readBytes_middle (b := encodeSignature sig) (a := ByteArray.empty)
    (v := Base.ByteOrder.toLE LEAF_INDEX_SIZE sig.leafIndex.toNat)
    (c := encodeLayerSignature sig.bottom ++ encodeLayerSignature sig.top) (offset := 0)
    (by simp [encodeSignature, ByteArray.append_assoc, ByteArray.empty_append]) (by simp)
    (by simp [SIG_SIZE])
  -- The bottom layer follows the index, and the top layer follows the bottom.
  have bottom := decodeLayerSignature_middle (b := encodeSignature sig) (sig := sig.bottom)
    (a := packBytes (Base.ByteOrder.toLE LEAF_INDEX_SIZE sig.leafIndex.toNat))
    (c := encodeLayerSignature sig.top) (offset := LEAF_INDEX_SIZE) (by simp [encodeSignature])
    (by simp) (by simp [SIG_SIZE]; omega)
  have top := decodeLayerSignature_middle (b := encodeSignature sig) (sig := sig.top)
    (a := packBytes (Base.ByteOrder.toLE LEAF_INDEX_SIZE sig.leafIndex.toNat)
      ++ encodeLayerSignature sig.bottom)
    (c := ByteArray.empty) (offset := LEAF_INDEX_SIZE + LAYER_SIG_SIZE)
    (by simp [encodeSignature, ByteArray.append_empty]) (by simp) (by simp [SIG_SIZE]; omega)
  -- A 32-bit word survives its four bytes.
  have word :
      UInt32.ofNat (Base.ByteOrder.ofLE (Base.ByteOrder.toLE LEAF_INDEX_SIZE sig.leafIndex.toNat))
      = sig.leafIndex := by
    rw [Base.ByteOrder.ofLE_toLE, Nat.mod_eq_of_lt (by
      have := sig.leafIndex.toNat_lt_size
      simpa [LEAF_INDEX_SIZE, UInt32.size] using this), UInt32.ofNat_toNat]
  simp only [decodeLeafIndex, idx, bottom, top, word]

/-! ## Every string of the right length is an encoding -/

/-- Two adjacent slices of a buffer join into one. -/
private theorem slice_append (b : ByteArray) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    (⟨b.data.extract i j⟩ : ByteArray) ++ ⟨b.data.extract j k⟩ = ⟨b.data.extract i k⟩ := by
  apply ByteArray.ext
  simp only [ByteArray.data_append, Array.extract_append_extract, Nat.min_eq_left hij,
    Nat.max_eq_right hjk]

/-- A layer's signature re-encodes to the 1200 bytes it was read from. -/
theorem encodeLayerSignature_decodeLayerSignature (b : ByteArray) (offset : Nat)
    (h : offset + LAYER_SIG_SIZE ≤ b.size) :
    encodeLayerSignature (decodeLayerSignature b offset h)
      = ⟨b.data.extract offset (offset + LAYER_SIG_SIZE)⟩ := by
  have h1 : offset + 16 ≤ b.size := by
    simp only [LAYER_SIG_SIZE, RANDOMIZER_LEN] at h; omega
  have h2 : offset + RANDOMIZER_LEN + V * 16 ≤ b.size := by
    simp only [LAYER_SIG_SIZE, DIGEST_LEN] at h; omega
  have h3 : offset + RANDOMIZER_LEN + V * DIGEST_LEN + LAYER_HEIGHT * 16 ≤ b.size := by
    simp only [LAYER_SIG_SIZE, DIGEST_LEN] at h ⊢; omega
  simp only [encodeLayerSignature, decodeLayerSignature, packDigests,
    Hash.Keccak.Lanes2.bytes_read _ _ h1, flatten_splitDigests h2, flatten_splitDigests h3,
    HashSig.packBytes_readBytes]
  simp only [LAYER_SIG_SIZE, RANDOMIZER_LEN, DIGEST_LEN, V, LAYER_HEIGHT]
  rw [slice_append _ (by omega) (by omega), slice_append _ (by omega) (by omega)]

/-- Every 32-byte string is the encoding of a public key. -/
theorem encodePublicKey_decodePublicKey {bytes : ByteArray} (sized : bytes.size = PUB_KEY_SIZE) :
    (decodePublicKey bytes).map encodePublicKey = .ok bytes := by
  rw [decodePublicKey, ite_eq_left sized]
  simp only [PUB_KEY_SIZE, DIGEST_LEN, PUBLIC_PARAM_LEN] at sized
  simp only [Except.map, encodePublicKey,
    Hash.Keccak.Lanes2.bytes_read _ _ (show 0 + 16 ≤ bytes.size by omega),
    Hash.Keccak.Lanes2.bytes_read _ _
      (show DIGEST_LEN + 16 ≤ bytes.size by simp only [DIGEST_LEN]; omega),
    HashSig.packBytes_readBytes, Nat.zero_add]
  simp only [DIGEST_LEN]
  rw [slice_append _ (by omega) (by omega)]
  -- The slice from 0 to the end is the whole buffer.
  congr 1
  apply ByteArray.ext
  simp only [ByteArray.size] at sized
  simp [sized]

/-- Every 2404-byte string is the encoding of a signature. -/
theorem encodeSignature_decodeSignature {bytes : ByteArray} (sized : bytes.size = SIG_SIZE) :
    (decodeSignature bytes).map encodeSignature = .ok bytes := by
  rw [decodeSignature, dite_eq_left sized]
  simp only [Except.map, encodeSignature,
    encodeLayerSignature_decodeLayerSignature bytes LEAF_INDEX_SIZE
      (by simp only [sized, SIG_SIZE]; omega),
    encodeLayerSignature_decodeLayerSignature bytes (LEAF_INDEX_SIZE + LAYER_SIG_SIZE)
      (by simp only [sized, SIG_SIZE]; omega)]
  -- Four bytes read as a word, and written back, are the same four bytes.
  have hword : Base.ByteOrder.ofLE (readBytes bytes 0 LEAF_INDEX_SIZE
      (by simp only [sized, SIG_SIZE]; omega)) < 2 ^ 32 := by
    have := Base.ByteOrder.ofLE_lt (readBytes bytes 0 LEAF_INDEX_SIZE
      (by simp only [sized, SIG_SIZE]; omega))
    simpa [LEAF_INDEX_SIZE] using this
  rw [decodeLeafIndex, UInt32.toNat_ofNat_of_lt' hword, Base.ByteOrder.toLE_ofLE,
    HashSig.packBytes_readBytes, Nat.zero_add, slice_append _ (by omega) (by omega),
    slice_append _ (by omega) (by omega)]
  -- The slice from 0 to the end is the whole buffer.
  congr 1
  apply ByteArray.ext
  simp only [ByteArray.size] at sized
  simp [sized, SIG_SIZE, LAYER_SIG_SIZE, LEAF_INDEX_SIZE]
  omega

/-! ## The leaf index alone -/

/-- Reading the leaf index alone gives the index that decoding the whole signature gives.

Both reject the same strings, those not 2404 bytes long. -/
theorem signatureIndex_eq_decodeSignature (bytes : ByteArray) :
    signatureIndex bytes = (decodeSignature bytes).map (·.leafIndex) := by
  -- Both branches test the same length, and both read the index the same way.
  unfold signatureIndex decodeSignature
  split <;> rfl

/-- An encoded signature reads back the leaf index it was built with. -/
@[simp] theorem signatureIndex_encodeSignature (sig : Signature) :
    signatureIndex (encodeSignature sig) = .ok sig.leafIndex := by
  simp [signatureIndex_eq_decodeSignature, Except.map]

/-- The leaf index is the first 4 bytes, read as a little-endian integer.

So any reader that takes `b_0 + 2^8 b_1 + 2^16 b_2 + 2^24 b_3` gets the same index. -/
theorem signatureIndex_eq_bytes {bytes : ByteArray} (sized : bytes.size = SIG_SIZE) :
    signatureIndex bytes = .ok (UInt32.ofNat
      (bytes[0]!.toNat + 2 ^ 8 * bytes[1]!.toNat + 2 ^ 16 * bytes[2]!.toNat
        + 2 ^ 24 * bytes[3]!.toNat)) := by
  -- The 4 bytes exist, so each checked read is a plain read.
  have room : 4 ≤ bytes.size := by rw [sized]; decide
  rw [signatureIndex, dite_eq_left sized, decodeLeafIndex, Base.ByteOrder.ofLE_eq_foldr]
  -- Both sides convert the same integer, so compare the integers.
  congr 2
  -- Unroll Horner's rule over the 4 bytes: b_0 + 256 (b_1 + 256 (b_2 + 256 b_3)).
  simp only [readBytes, LEAF_INDEX_SIZE, Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero,
    List.foldr_cons, List.foldr_nil]
  rw [getElem!_pos bytes 0 (by omega), getElem!_pos bytes 1 (by omega),
    getElem!_pos bytes 2 (by omega), getElem!_pos bytes 3 (by omega)]
  simp only [ByteArray.getElem_eq_getElem_data, Nat.zero_add, Fin.val_zero, Fin.val_succ,
    Nat.reduceAdd]
  -- Expanding the nested form gives the sum of powers.
  omega

/-- Distinct public keys have distinct encodings. -/
theorem encodePublicKey_injective : Function.Injective encodePublicKey := by
  intro left right same
  simpa using congrArg decodePublicKey same

/-- Distinct signatures have distinct encodings. -/
theorem encodeSignature_injective : Function.Injective encodeSignature := by
  intro left right same
  simpa using congrArg decodeSignature same

/-! ## Rejection -/

/-- A public key string of any other length than 32 bytes is rejected. -/
theorem decodePublicKey_badSize {bytes : ByteArray} (wrong : bytes.size ≠ PUB_KEY_SIZE) :
    decodePublicKey bytes = .error (.badPublicKeySize bytes.size) := by
  rw [decodePublicKey, ite_eq_right wrong]

/-- A signature string of any other length than 2404 bytes is rejected. -/
theorem decodeSignature_badSize {bytes : ByteArray} (wrong : bytes.size ≠ SIG_SIZE) :
    decodeSignature bytes = .error (.badSignatureSize bytes.size) := by
  rw [decodeSignature, dite_eq_right wrong]

/-- Public key decoding succeeds exactly on 32-byte strings. -/
theorem decodePublicKey_success_iff (bytes : ByteArray) :
    (∃ pk, decodePublicKey bytes = .ok pk) ↔ bytes.size = PUB_KEY_SIZE := by
  constructor
  · rintro ⟨pk, read⟩
    exact Decidable.byContradiction fun wrong => by simp [decodePublicKey_badSize wrong] at read
  · intro sized
    rw [decodePublicKey, ite_eq_left sized]
    exact ⟨_, rfl⟩

/-- A signature string of any other length than 2404 bytes has no leaf index. -/
theorem signatureIndex_badSize {bytes : ByteArray} (wrong : bytes.size ≠ SIG_SIZE) :
    signatureIndex bytes = .error (.badSignatureSize bytes.size) := by
  rw [signatureIndex, dite_eq_right wrong]

/-- Signature decoding succeeds exactly on 2404-byte strings. -/
theorem decodeSignature_success_iff (bytes : ByteArray) :
    (∃ sig, decodeSignature bytes = .ok sig) ↔ bytes.size = SIG_SIZE := by
  constructor
  · rintro ⟨sig, read⟩
    exact Decidable.byContradiction fun wrong => by simp [decodeSignature_badSize wrong] at read
  · intro sized
    rw [decodeSignature, dite_eq_left sized]
    exact ⟨_, rfl⟩

end EthLib.Cryptography.Xmss

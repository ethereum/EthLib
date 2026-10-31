import EthLib.Cryptography.Xmss.Serialization
import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: `Xmss.Serialization`

The encodings are bijections between objects and byte strings of the declared length.

- Decoding an encoding returns the object.
- Every string of the declared length is an encoding.
- Every string of another length is rejected.
-/

namespace EthLib.Cryptography.Xmss

open Constants

/-! ## Digests and their bytes -/

/-- Cutting a field into digests and joining them back gives the field. -/
@[simp] theorem flatten_splitDigests {n : Nat} (bytes : Vector UInt8 (n * DIGEST_LEN)) :
    (splitDigests bytes).flatten = bytes := by
  apply Vector.ext
  intro i inside
  simp only [Vector.getElem_flatten, splitDigests, Vector.getElem_ofFn]
  -- Position p is byte p mod 16 of digest p / 16.
  congr 1
  simp only [DIGEST_LEN] at *
  omega

/-- Joining digests into a field and cutting it back gives the digests. -/
@[simp] theorem splitDigests_flatten {n : Nat} (digests : Vector Digest n) :
    splitDigests digests.flatten = digests := by
  apply Vector.ext
  intro i inside
  apply Vector.ext
  intro j within
  simp only [splitDigests, Vector.getElem_ofFn, Vector.getElem_flatten]
  -- Position 16 i + j is byte j of digest i.
  have quotient : (i * DIGEST_LEN + j) / DIGEST_LEN = i := by
    simp only [DIGEST_LEN] at *
    omega
  have remainder : (i * DIGEST_LEN + j) % DIGEST_LEN = j := by
    simp only [DIGEST_LEN] at *
    omega
  simp [quotient, remainder]

/-- A list of `n` digests packs to `16 n` bytes. -/
@[simp] theorem size_packDigests {n : Nat} (ds : Vector Digest n) :
    (packDigests ds).size = n * DIGEST_LEN := by
  simp [packDigests]

/-! ## Sizes -/

/-- A public key encodes to 32 bytes. -/
@[simp] theorem size_encodePublicKey (pk : PublicKey) :
    (encodePublicKey pk).size = PUB_KEY_SIZE := by
  simp [encodePublicKey, PUB_KEY_SIZE]

/-- A layer's signature encodes to 1200 bytes. -/
@[simp] theorem size_encodeLayerSignature (sig : LayerSignature) :
    (encodeLayerSignature sig).size = LAYER_SIG_SIZE := by
  simp [encodeLayerSignature, LAYER_SIG_SIZE]

/-- A signature encodes to 2404 bytes. -/
@[simp] theorem size_encodeSignature (sig : Signature) :
    (encodeSignature sig).size = SIG_SIZE := by
  simp only [encodeSignature, ByteArray.size_append, size_packBytes,
    size_encodeLayerSignature, SIG_SIZE]
  omega

/-! ## Reading a field out of a concatenation -/

/-- A read that covers exactly the middle part of a concatenation returns that part. -/
theorem readBytes_middle {b a c : ByteArray} {n : Nat} {v : Vector UInt8 n} {offset : Nat}
    (hb : b = a ++ packBytes v ++ c) (ho : offset = a.size) (h : offset + n ≤ b.size) :
    readBytes b offset n h = v := by
  subst hb ho
  -- Strip the last part, then the first, leaving the object itself.
  rw [readBytes_append_left _ (by simp)]
  have past := readBytes_append_right (a := a) (b := packBytes v) (offset := 0) (n := n)
    (by simp)
  simp only [Nat.add_zero] at past
  rw [past, readBytes_packBytes]

/-- A layer's signature reads back from its place in a concatenation. -/
theorem decodeLayerSignature_middle {b a c : ByteArray} {sig : LayerSignature} {offset : Nat}
    (hb : b = a ++ encodeLayerSignature sig ++ c) (ho : offset = a.size)
    (h : offset + LAYER_SIG_SIZE ≤ b.size) :
    decodeLayerSignature b offset h = sig := by
  -- Regroup so each field is the middle of its own concatenation.
  have hr : b = a ++ packBytes sig.randomizer
      ++ (packDigests sig.chainValues ++ packDigests sig.path ++ c) := by
    rw [hb, encodeLayerSignature]
    simp only [ByteArray.append_assoc]
  have hc : b = (a ++ packBytes sig.randomizer) ++ packBytes sig.chainValues.flatten
      ++ (packDigests sig.path ++ c) := by
    rw [hb, encodeLayerSignature]
    simp only [ByteArray.append_assoc, packDigests]
  have hp : b = (a ++ packBytes sig.randomizer ++ packDigests sig.chainValues)
      ++ packBytes sig.path.flatten ++ c := by
    rw [hb, encodeLayerSignature]
    simp only [ByteArray.append_assoc, packDigests]
  -- Each field starts where the previous one ends.
  have r := readBytes_middle hr ho (by simp only [LAYER_SIG_SIZE] at h; omega)
  have c' := readBytes_middle hc (offset := offset + RANDOMIZER_LEN)
    (by simp [ho]) (by simp only [LAYER_SIG_SIZE] at h; omega)
  have p := readBytes_middle hp (offset := offset + RANDOMIZER_LEN + V * DIGEST_LEN)
    (by simp [ho]) (by simp only [LAYER_SIG_SIZE] at h; omega)
  simp only [decodeLayerSignature, r, c', p, splitDigests_flatten]

/-! ## Round trips -/

/-- Decoding an encoded public key returns it. -/
@[simp] theorem decodePublicKey_encodePublicKey (pk : PublicKey) :
    decodePublicKey (encodePublicKey pk) = .ok pk := by
  rw [decodePublicKey, dite_eq_left (size_encodePublicKey pk)]
  -- The root is the first field, the public parameter the one after it.
  have root := readBytes_middle (b := encodePublicKey pk) (a := ByteArray.empty)
    (c := packBytes pk.publicParam) (v := pk.root) (offset := 0)
    (by simp [encodePublicKey, ByteArray.empty_append]) (by simp)
    (by simp [PUB_KEY_SIZE])
  have param := readBytes_middle (b := encodePublicKey pk) (a := packBytes pk.root)
    (c := ByteArray.empty) (v := pk.publicParam) (offset := DIGEST_LEN)
    (by simp [encodePublicKey, ByteArray.append_empty]) (by simp) (by simp [PUB_KEY_SIZE])
  simp only [root, param]

/-- Decoding an encoded signature returns it. -/
@[simp] theorem decodeSignature_encodeSignature (sig : Signature) :
    decodeSignature (encodeSignature sig) = .ok sig := by
  rw [decodeSignature, dite_eq_left (size_encodeSignature sig)]
  -- The leaf index is the first four bytes, as a little-endian word.
  have idx := readBytes_middle (b := encodeSignature sig) (a := ByteArray.empty)
    (v := littleEndian LEAF_INDEX_SIZE sig.leafIndex.toNat)
    (c := encodeLayerSignature sig.bottom ++ encodeLayerSignature sig.top) (offset := 0)
    (by simp [encodeSignature, ByteArray.append_assoc, ByteArray.empty_append]) (by simp)
    (by simp [SIG_SIZE])
  -- The bottom layer follows the index, and the top layer follows the bottom.
  have bottom := decodeLayerSignature_middle (b := encodeSignature sig) (sig := sig.bottom)
    (a := packBytes (littleEndian LEAF_INDEX_SIZE sig.leafIndex.toNat))
    (c := encodeLayerSignature sig.top) (offset := LEAF_INDEX_SIZE) (by simp [encodeSignature])
    (by simp) (by simp [SIG_SIZE]; omega)
  have top := decodeLayerSignature_middle (b := encodeSignature sig) (sig := sig.top)
    (a := packBytes (littleEndian LEAF_INDEX_SIZE sig.leafIndex.toNat)
      ++ encodeLayerSignature sig.bottom)
    (c := ByteArray.empty) (offset := LEAF_INDEX_SIZE + LAYER_SIG_SIZE)
    (by simp [encodeSignature, ByteArray.append_empty]) (by simp) (by simp [SIG_SIZE]; omega)
  -- A 32-bit word survives its four bytes.
  have word : UInt32.ofNat (fromLittleEndian (littleEndian LEAF_INDEX_SIZE sig.leafIndex.toNat))
      = sig.leafIndex := by
    rw [fromLittleEndian_littleEndian, Nat.mod_eq_of_lt (by
      have := sig.leafIndex.toNat_lt_size
      simpa [LEAF_INDEX_SIZE, UInt32.size] using this), UInt32.ofNat_toNat]
  simp only [decodeLeafIndex, idx, bottom, top, word]

/-! ## Every string of the right length is an encoding -/

/-- The bytes of a read are the slice of the buffer it covers. -/
theorem packBytes_readBytes (b : ByteArray) (offset n : Nat) (h) :
    packBytes (readBytes b offset n h) = ⟨b.data.extract offset (offset + n)⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size] at h
    simp only [packBytes, readBytes, Vector.toArray_ofFn, Array.size_ofFn, Array.size_extract]
    omega
  · intro i h₁ h₂
    simp [packBytes, readBytes]

/-- Two adjacent slices of a buffer join into one. -/
private theorem slice_append (b : ByteArray) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    (⟨b.data.extract i j⟩ : ByteArray) ++ ⟨b.data.extract j k⟩ = ⟨b.data.extract i k⟩ := by
  apply ByteArray.ext
  simp only [ByteArray.data_append, Array.extract_append_extract, Nat.min_eq_left hij,
    Nat.max_eq_right hjk]

/-- A layer's signature re-encodes to the 1200 bytes it was read from. -/
theorem encodeLayerSignature_decodeLayerSignature (b : ByteArray) (offset : Nat) (h) :
    encodeLayerSignature (decodeLayerSignature b offset h)
      = ⟨b.data.extract offset (offset + LAYER_SIG_SIZE)⟩ := by
  simp only [encodeLayerSignature, decodeLayerSignature, packDigests, flatten_splitDigests,
    packBytes_readBytes]
  rw [slice_append _ (by omega) (by omega), slice_append _ (by omega) (by omega)]
  simp only [LAYER_SIG_SIZE, Nat.add_assoc]

/-- Every 32-byte string is the encoding of a public key. -/
theorem encodePublicKey_decodePublicKey {bytes : ByteArray} (sized : bytes.size = PUB_KEY_SIZE) :
    (decodePublicKey bytes).map encodePublicKey = .ok bytes := by
  rw [decodePublicKey, dite_eq_left sized]
  simp only [Except.map, encodePublicKey, packBytes_readBytes, Nat.zero_add]
  rw [slice_append _ (by omega) (by omega)]
  -- The slice from 0 to the end is the whole buffer.
  congr 1
  apply ByteArray.ext
  simp only [ByteArray.size] at sized
  simp [sized, PUB_KEY_SIZE, DIGEST_LEN, PUBLIC_PARAM_LEN]

/-- Every 2404-byte string is the encoding of a signature. -/
theorem encodeSignature_decodeSignature {bytes : ByteArray} (sized : bytes.size = SIG_SIZE) :
    (decodeSignature bytes).map encodeSignature = .ok bytes := by
  rw [decodeSignature, dite_eq_left sized]
  simp only [Except.map, encodeSignature, encodeLayerSignature_decodeLayerSignature]
  -- Four bytes read as a word, and written back, are the same four bytes.
  have hword : fromLittleEndian (readBytes bytes 0 LEAF_INDEX_SIZE
      (by simp only [sized, SIG_SIZE]; omega)) < 2 ^ 32 := by
    have := fromLittleEndian_lt (readBytes bytes 0 LEAF_INDEX_SIZE
      (by simp only [sized, SIG_SIZE]; omega))
    simpa [LEAF_INDEX_SIZE] using this
  rw [decodeLeafIndex, UInt32.toNat_ofNat_of_lt' hword, littleEndian_fromLittleEndian, packBytes_readBytes,
    Nat.zero_add, slice_append _ (by omega) (by omega), slice_append _ (by omega) (by omega)]
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
  rw [signatureIndex, dite_eq_left sized, decodeLeafIndex, fromLittleEndian_eq_foldr]
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
  rw [decodePublicKey, dite_eq_right wrong]

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
    rw [decodePublicKey, dite_eq_left sized]
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

import EthLib.Cryptography.Sphincs.Serialization
import EthLib.Cryptography.Proofs.Xmss.Serialization

/-!
# Proofs: `Sphincs.Serialization`

The encodings are bijections between objects and byte strings of the declared length.

- Decoding an encoding returns the object.
- Every string of the declared length is an encoding.
- Every string of another length is rejected.
-/

namespace EthLib.Cryptography.Sphincs

open Constants

/-! ## Chunks and their bytes -/

/-- Cutting a field into chunks and joining them back gives the field. -/
@[simp] theorem flatten_splitChunks {n m : Nat} (bytes : Vector UInt8 (n * m)) :
    (splitChunks bytes).flatten = bytes := by
  apply Vector.ext
  intro i inside
  simp only [Vector.getElem_flatten, splitChunks, Vector.getElem_ofFn]
  -- Position p is byte `p mod m` of chunk `p / m`.
  congr 1
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp at inside
  · exact Nat.div_add_mod' i m

/-- Joining chunks into a field and cutting it back gives the chunks. -/
@[simp] theorem splitChunks_flatten {n m : Nat} (chunks : Vector (Vector UInt8 m) n) :
    splitChunks chunks.flatten = chunks := by
  apply Vector.ext
  intro i inside
  apply Vector.ext
  intro j within
  simp only [splitChunks, Vector.getElem_ofFn, Vector.getElem_flatten]
  -- Position `m i + j` is byte `j` of chunk `i`.
  have quotient : (i * m + j) / m = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt within, Nat.zero_add]
  have remainder : (i * m + j) % m = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt within]
  simp [quotient, remainder]

/-- A list of `n` digests packs to `16 n` bytes. -/
@[simp] theorem size_packDigests {n : Nat} (ds : Vector Digest n) :
    (packDigests ds).size = n * N := by
  simp [packDigests]

/-! ## One FORS opening -/

/-- Reading back the bytes of an opening returns the opening. -/
@[simp] theorem treeOpeningOfBytes_treeOpeningBytes (opening : TreeOpening) :
    treeOpeningOfBytes (treeOpeningBytes opening) = opening := by
  obtain ⟨secret, path⟩ := opening
  simp only [treeOpeningOfBytes, treeOpeningBytes, TreeOpening.mk.injEq]
  constructor
  -- The first 16 bytes are the secret.
  · apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn, Vector.getElem_append, hj, ↓reduceDIte]
  -- The 144 bytes after them are the path.
  · have hpath : (Vector.ofFn fun j : Fin (FORS_HEIGHT * N) =>
        (secret ++ path.flatten)[N + j.val]'(by have := j.isLt; simp only [N, FORS_HEIGHT] at *; omega))
        = path.flatten := by
      apply Vector.ext
      intro j hj
      simp only [Vector.getElem_ofFn, Vector.getElem_append]
      -- Byte `16 + j` lies past the secret, at byte `j` of the path.
      simp only [show ¬ (N + j < N) from by omega, ↓reduceDIte, Nat.add_sub_cancel_left]
    rw [hpath]
    exact splitChunks_flatten path

/-- Writing back the opening read from 176 bytes returns those bytes. -/
@[simp] theorem treeOpeningBytes_treeOpeningOfBytes (bytes : Vector UInt8 TREE_OPENING_SIZE) :
    treeOpeningBytes (treeOpeningOfBytes bytes) = bytes := by
  apply Vector.ext
  intro j hj
  simp only [treeOpeningBytes, treeOpeningOfBytes, splitDigests, flatten_splitChunks,
    Vector.getElem_append, Vector.getElem_ofFn]
  -- Below 16 the byte is in the secret, from 16 on it is in the path.
  split
  · rfl
  · congr 1
    simp only [N] at *
    omega

/-! ## Sizes -/

/-- A public key encodes to 32 bytes. -/
@[simp] theorem size_encodePublicKey (pk : PublicKey) :
    (encodePublicKey pk).size = PUB_KEY_SIZE := by
  simp [encodePublicKey, PUB_KEY_SIZE]

/-- The FORS openings encode to 4224 bytes. -/
@[simp] theorem size_encodeFors (openings : Vector TreeOpening FORS_TREES) :
    (encodeFors openings).size = FORS_TREES * TREE_OPENING_SIZE := by
  simp [encodeFors]

/-- A layer's signature encodes to `1028 + 16 h` bytes. -/
@[simp] theorem size_encodeLayerSignature {layer : Layer} (sig : LayerSignature layer) :
    (encodeLayerSignature sig).size = layerSigSize layer.height := by
  simp [encodeLayerSignature, layerSigSize]

/-- A signature encodes to 7740 bytes. -/
@[simp] theorem size_encodeSignature (sig : Signature) :
    (encodeSignature sig).size = SIG_SIZE := by
  simp only [encodeSignature, ByteArray.size_append, Xmss.size_packBytes, size_encodeFors,
    size_encodeLayerSignature, Layer.height, SIG_SIZE]
  omega

/-! ## Reading a part out of a concatenation -/

/-- The FORS openings read back from their place in a concatenation. -/
theorem decodeFors_middle {b a c : ByteArray} {openings : Vector TreeOpening FORS_TREES}
    {offset : Nat} (hb : b = a ++ encodeFors openings ++ c) (ho : offset = a.size)
    (h : offset + FORS_TREES * TREE_OPENING_SIZE ≤ b.size) :
    decodeFors b offset h = openings := by
  have hread := Xmss.readBytes_middle (v := (openings.map treeOpeningBytes).flatten) hb ho h
  simp only [decodeFors, hread, splitChunks_flatten, Vector.map_map]
  -- Writing then reading an opening is the identity.
  have : treeOpeningOfBytes ∘ treeOpeningBytes = id := funext treeOpeningOfBytes_treeOpeningBytes
  rw [this, Vector.map_id]

/-- A layer's signature reads back from its place in a concatenation. -/
theorem decodeLayerSignature_middle {layer : Layer} {b a c : ByteArray}
    {sig : LayerSignature layer} {offset : Nat}
    (hb : b = a ++ encodeLayerSignature sig ++ c) (ho : offset = a.size)
    (h : offset + layerSigSize layer.height ≤ b.size) :
    decodeLayerSignature layer b offset h = sig := by
  -- Regroup so each field is the middle of its own concatenation.
  have hr : b = a ++ packBytes (littleEndian COUNTER_LEN sig.counter.toNat)
      ++ (packDigests sig.chainValues ++ packDigests sig.path ++ c) := by
    rw [hb, encodeLayerSignature]
    simp only [ByteArray.append_assoc]
  have hc : b = (a ++ packBytes (littleEndian COUNTER_LEN sig.counter.toNat))
      ++ packBytes sig.chainValues.flatten ++ (packDigests sig.path ++ c) := by
    rw [hb, encodeLayerSignature]
    simp only [ByteArray.append_assoc, packDigests]
  have hp : b = (a ++ packBytes (littleEndian COUNTER_LEN sig.counter.toNat)
      ++ packDigests sig.chainValues) ++ packBytes sig.path.flatten ++ c := by
    rw [hb, encodeLayerSignature]
    simp only [ByteArray.append_assoc, packDigests]
  -- Each field starts where the previous one ends.
  have r := Xmss.readBytes_middle hr ho (by simp only [layerSigSize] at h; omega)
  have c' := Xmss.readBytes_middle hc (offset := offset + COUNTER_LEN)
    (by simp [ho]) (by simp only [layerSigSize] at h; omega)
  have p := Xmss.readBytes_middle hp (offset := offset + COUNTER_LEN + V * N)
    (by simp [ho]) (by simp only [layerSigSize] at h; omega)
  -- A 32-bit word survives its four bytes.
  have word : UInt32.ofNat (fromLittleEndian (littleEndian COUNTER_LEN sig.counter.toNat))
      = sig.counter := by
    rw [Xmss.fromLittleEndian_littleEndian, Nat.mod_eq_of_lt (by
      have := sig.counter.toNat_lt_size
      simpa [COUNTER_LEN, UInt32.size] using this), UInt32.ofNat_toNat]
  obtain ⟨counter, chainValues, path⟩ := sig
  simp only [decodeLayerSignature, r, c', p, word, splitDigests, splitChunks_flatten]

/-! ## Round trips -/

/-- Decoding an encoded public key returns it. -/
@[simp] theorem decodePublicKey_encodePublicKey (pk : PublicKey) :
    decodePublicKey (encodePublicKey pk) = .ok pk := by
  rw [decodePublicKey, dite_eq_left (size_encodePublicKey pk)]
  -- The root is the first field, the public parameter the one after it.
  have root := Xmss.readBytes_middle (b := encodePublicKey pk) (a := ByteArray.empty)
    (c := packBytes pk.publicParam) (v := pk.root) (offset := 0)
    (by simp [encodePublicKey, ByteArray.empty_append]) (by simp)
    (by simp [PUB_KEY_SIZE])
  have param := Xmss.readBytes_middle (b := encodePublicKey pk) (a := packBytes pk.root)
    (c := ByteArray.empty) (v := pk.publicParam) (offset := N)
    (by simp [encodePublicKey, ByteArray.append_empty]) (by simp) (by simp [PUB_KEY_SIZE])
  simp only [root, param]

/-- Decoding an encoded signature returns it. -/
@[simp] theorem decodeSignature_encodeSignature (sig : Signature) :
    decodeSignature (encodeSignature sig) = .ok sig := by
  rw [decodeSignature, dite_eq_left (size_encodeSignature sig)]
  -- The randomizer is the first 16 bytes.
  have rho := Xmss.readBytes_middle (b := encodeSignature sig) (a := ByteArray.empty)
    (v := sig.randomizer)
    (c := encodeFors sig.fors ++ encodeLayerSignature sig.bottom ++ encodeLayerSignature sig.middle
      ++ encodeLayerSignature sig.top) (offset := 0)
    (by simp [encodeSignature, ByteArray.append_assoc, ByteArray.empty_append]) (by simp)
    (by simp [SIG_SIZE]; omega)
  -- The FORS openings follow the randomizer.
  have fors := decodeFors_middle (b := encodeSignature sig) (openings := sig.fors)
    (a := packBytes sig.randomizer)
    (c := encodeLayerSignature sig.bottom ++ encodeLayerSignature sig.middle
      ++ encodeLayerSignature sig.top) (offset := forsOffset)
    (by simp [encodeSignature, ByteArray.append_assoc]) (by simp [forsOffset])
    (by simp [SIG_SIZE, forsOffset]; omega)
  -- Each layer follows the parts before it.
  have bottom := decodeLayerSignature_middle (b := encodeSignature sig) (sig := sig.bottom)
    (a := packBytes sig.randomizer ++ encodeFors sig.fors)
    (c := encodeLayerSignature sig.middle ++ encodeLayerSignature sig.top) (offset := bottomOffset)
    (by simp [encodeSignature, ByteArray.append_assoc]) (by simp [bottomOffset, forsOffset])
    (by simp [SIG_SIZE, bottomOffset, forsOffset, Layer.height]; omega)
  have middle := decodeLayerSignature_middle (b := encodeSignature sig) (sig := sig.middle)
    (a := packBytes sig.randomizer ++ encodeFors sig.fors ++ encodeLayerSignature sig.bottom)
    (c := encodeLayerSignature sig.top) (offset := middleOffset)
    (by simp [encodeSignature, ByteArray.append_assoc])
    (by simp [middleOffset, bottomOffset, forsOffset, Layer.height])
    (by simp [SIG_SIZE, middleOffset, bottomOffset, forsOffset, Layer.height]; omega)
  have top := decodeLayerSignature_middle (b := encodeSignature sig) (sig := sig.top)
    (a := packBytes sig.randomizer ++ encodeFors sig.fors ++ encodeLayerSignature sig.bottom
      ++ encodeLayerSignature sig.middle)
    (c := ByteArray.empty) (offset := topOffset)
    (by simp [encodeSignature, ByteArray.append_empty])
    (by simp [topOffset, middleOffset, bottomOffset, forsOffset, Layer.height])
    (by simp [SIG_SIZE, topOffset, middleOffset, bottomOffset, forsOffset, Layer.height]; omega)
  simp only [rho, fors, bottom, middle, top]

/-! ## Every string of the right length is an encoding -/

/-- Two adjacent slices of a buffer join into one. -/
theorem slice_append (b : ByteArray) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    (⟨b.data.extract i j⟩ : ByteArray) ++ ⟨b.data.extract j k⟩ = ⟨b.data.extract i k⟩ := by
  apply ByteArray.ext
  simp only [ByteArray.data_append, Array.extract_append_extract, Nat.min_eq_left hij,
    Nat.max_eq_right hjk]

/-- The FORS openings re-encode to the 4224 bytes they were read from. -/
theorem encodeFors_decodeFors (b : ByteArray) (offset : Nat) (h) :
    encodeFors (decodeFors b offset h)
      = ⟨b.data.extract offset (offset + FORS_TREES * TREE_OPENING_SIZE)⟩ := by
  simp only [encodeFors, decodeFors, Vector.map_map]
  -- Reading then writing 176 bytes is the identity.
  have : treeOpeningBytes ∘ treeOpeningOfBytes = id := funext treeOpeningBytes_treeOpeningOfBytes
  rw [this, Vector.map_id, flatten_splitChunks, Xmss.packBytes_readBytes]

/-- A layer's signature re-encodes to the bytes it was read from. -/
theorem encodeLayerSignature_decodeLayerSignature (layer : Layer) (b : ByteArray) (offset : Nat) (h) :
    encodeLayerSignature (decodeLayerSignature layer b offset h)
      = ⟨b.data.extract offset (offset + layerSigSize layer.height)⟩ := by
  -- Four bytes read as a word, and written back, are the same four bytes.
  have hword : fromLittleEndian (readBytes b offset COUNTER_LEN
      (by simp only [layerSigSize] at h; omega)) < 2 ^ 32 := by
    have := Xmss.fromLittleEndian_lt (readBytes b offset COUNTER_LEN
      (by simp only [layerSigSize] at h; omega))
    simpa [COUNTER_LEN] using this
  simp only [encodeLayerSignature, decodeLayerSignature, packDigests, splitDigests,
    flatten_splitChunks, Xmss.packBytes_readBytes, UInt32.toNat_ofNat_of_lt' hword,
    Xmss.littleEndian_fromLittleEndian]
  rw [slice_append _ (by omega) (by omega), slice_append _ (by omega) (by omega)]
  simp only [layerSigSize, Nat.add_assoc]

/-- Every 32-byte string is the encoding of a public key. -/
theorem encodePublicKey_decodePublicKey {bytes : ByteArray} (sized : bytes.size = PUB_KEY_SIZE) :
    (decodePublicKey bytes).map encodePublicKey = .ok bytes := by
  rw [decodePublicKey, dite_eq_left sized]
  simp only [Except.map, encodePublicKey, Xmss.packBytes_readBytes, Nat.zero_add]
  rw [slice_append _ (by omega) (by omega)]
  -- The slice from 0 to the end is the whole buffer.
  congr 1
  apply ByteArray.ext
  simp only [ByteArray.size] at sized
  simp [sized, PUB_KEY_SIZE, N, PUBLIC_PARAM_LEN]

/-- Every 7740-byte string is the encoding of a signature. -/
theorem encodeSignature_decodeSignature {bytes : ByteArray} (sized : bytes.size = SIG_SIZE) :
    (decodeSignature bytes).map encodeSignature = .ok bytes := by
  rw [decodeSignature, dite_eq_left sized]
  simp only [Except.map, encodeSignature, encodeLayerSignature_decodeLayerSignature,
    encodeFors_decodeFors, Xmss.packBytes_readBytes, Nat.zero_add]
  simp only [forsOffset, bottomOffset, middleOffset, topOffset, Layer.height]
  rw [slice_append _ (by omega) (by omega), slice_append _ (by omega) (by omega),
    slice_append _ (by omega) (by omega), slice_append _ (by omega) (by omega)]
  -- The slice from 0 to the end is the whole buffer.
  congr 1
  apply ByteArray.ext
  have hsize : RANDOMIZER_LEN + FORS_TREES * TREE_OPENING_SIZE + layerSigSize LOWER_HEIGHT
      + layerSigSize LOWER_HEIGHT + layerSigSize TOP_HEIGHT = bytes.data.size := by
    have : bytes.data.size = SIG_SIZE := sized
    rw [this, SIG_SIZE]
    omega
  simp only [ByteArray.size] at sized
  rw [hsize, Array.extract_size]

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

/-- A signature string of any other length than 7740 bytes is rejected. -/
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

/-- Signature decoding succeeds exactly on 7740-byte strings. -/
theorem decodeSignature_success_iff (bytes : ByteArray) :
    (∃ sig, decodeSignature bytes = .ok sig) ↔ bytes.size = SIG_SIZE := by
  constructor
  · rintro ⟨sig, read⟩
    exact Decidable.byContradiction fun wrong => by simp [decodeSignature_badSize wrong] at read
  · intro sized
    rw [decodeSignature, dite_eq_left sized]
    exact ⟨_, rfl⟩

end EthLib.Cryptography.Sphincs

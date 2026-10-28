import EthLib.Cryptography.Xmss.Serialization
import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: `Xmss.Serialization`

The encodings are bijections between objects and byte strings of the declared length.
-/

namespace EthLib.Cryptography.Xmss

open Constants

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

/-! ## Sizes -/

/-- A public key encodes to 32 bytes. -/
@[simp] theorem size_encodePublicKey (pk : PublicKey) :
    (encodePublicKey pk).size = PUB_KEY_SIZE := by
  simp [encodePublicKey, PUB_KEY_SIZE]

/-- A signature encodes to 1208 bytes. -/
@[simp] theorem size_encodeSignature (sig : Signature) :
    (encodeSignature sig).size = SIG_SIZE := by
  simp [encodeSignature, SIG_SIZE, WOTS_SIG_SIZE]

/-! ## Round trips -/

/-- Decoding an encoded public key returns it. -/
@[simp] theorem decodePublicKey_encodePublicKey (pk : PublicKey) :
    decodePublicKey (encodePublicKey pk) = .ok pk := by
  rw [decodePublicKey, dif_pos (size_encodePublicKey pk)]
  -- The root is the first field, the public parameter the one after it.
  have root := readBytes_append_left (a := packBytes pk.merkleRoot)
    (b := packBytes pk.publicParam) (offset := 0) (n := DIGEST_LEN)
    (by simp [DIGEST_LEN, PUBLIC_PARAM_LEN]) (by simp)
  have param := readBytes_append_right (a := packBytes pk.merkleRoot)
    (b := packBytes pk.publicParam) (offset := 0) (n := PUBLIC_PARAM_LEN)
    (by simp [DIGEST_LEN, PUBLIC_PARAM_LEN])
  simp only [size_packBytes, Nat.add_zero] at param
  simp only [encodePublicKey, root, param, readBytes_packBytes]

/-- Decoding an encoded signature returns it. -/
@[simp] theorem decodeSignature_encodeSignature (sig : Signature) :
    decodeSignature (encodeSignature sig) = .ok sig := by
  rw [decodeSignature, dif_pos (size_encodeSignature sig)]
  -- The encoding is three parts: randomizer, chain values, siblings.
  have hr : (packBytes sig.randomness).size = RANDOMNESS_LEN := size_packBytes _
  have hc : (packBytes sig.chainElements.flatten).size = V * DIGEST_LEN := size_packBytes _
  -- The randomizer is the start of the first two parts, and of the first.
  have randomizer : readBytes (encodeSignature sig) 0 RANDOMNESS_LEN
      (by simp [SIG_SIZE, WOTS_SIG_SIZE]; omega) = sig.randomness := by
    -- The encoding unfolds to the concatenation by definition.
    show readBytes (packBytes _ ++ packBytes _ ++ packBytes _) 0 _ _ = _
    rw [readBytes_append_left _ (by simp [hr, hc]),
      readBytes_append_left _ (by simp [hr]), readBytes_packBytes]
  -- The chain values start where the randomizer ends.
  have chains : readBytes (encodeSignature sig) RANDOMNESS_LEN (V * DIGEST_LEN)
      (by simp [SIG_SIZE, WOTS_SIG_SIZE]) = sig.chainElements.flatten := by
    show readBytes (packBytes _ ++ packBytes _ ++ packBytes _) _ _ _ = _
    rw [readBytes_append_left _ (by simp [hr, hc])]
    have past := readBytes_append_right (a := packBytes sig.randomness)
      (b := packBytes sig.chainElements.flatten) (offset := 0) (n := V * DIGEST_LEN)
      (by simp [hr, hc])
    simp only [hr, Nat.add_zero] at past
    rw [past, readBytes_packBytes]
  -- The siblings start where the first two parts end.
  have siblings : readBytes (encodeSignature sig) WOTS_SIG_SIZE (LOG_LIFETIME * DIGEST_LEN)
      (by simp [SIG_SIZE]) = sig.merklePath.flatten := by
    have past := readBytes_append_right
      (a := packBytes sig.randomness ++ packBytes sig.chainElements.flatten)
      (b := packBytes sig.merklePath.flatten) (offset := 0)
      (n := LOG_LIFETIME * DIGEST_LEN) (by simp [hr, hc])
    simp only [ByteArray.size_append, hr, hc, Nat.add_zero] at past
    exact past.trans (readBytes_packBytes _ _)
  simp only [randomizer, chains, siblings, splitDigests_flatten]

/-- Every 32-byte string is the encoding of a public key. -/
theorem encodePublicKey_surjective {bytes : ByteArray} (sized : bytes.size = PUB_KEY_SIZE) :
    ∃ pk, encodePublicKey pk = bytes := by
  have size : bytes.data.size = 32 := sized.trans pub_key_size_eq
  -- Bytes 0..15 are the root and bytes 16..31 the public parameter.
  refine ⟨⟨⟨bytes.data.extract 0 16, by simp [size, DIGEST_LEN]⟩,
    ⟨bytes.data.extract 16 32, by simp [size, PUBLIC_PARAM_LEN]⟩⟩, ?_⟩
  -- Re-joining the two adjacent slices gives the whole string.
  apply ByteArray.ext
  simp [encodePublicKey, packBytes, Array.extract_append_extract, ← size]
  omega

/-- Every 1208-byte string is the encoding of a signature. -/
theorem encodeSignature_surjective {bytes : ByteArray} (sized : bytes.size = SIG_SIZE) :
    ∃ sig, encodeSignature sig = bytes := by
  have size : bytes.data.size = 1208 := sized.trans sig_size_eq
  -- Cut at the field seams:
  --
  --     [ 0, 24) randomizer
  --     [24, 696) chain values
  --     [696, 1208) siblings
  refine ⟨⟨splitDigests ⟨bytes.data.extract 24 696, by simp [size, V, DIGEST_LEN]⟩,
    ⟨bytes.data.extract 0 24, by simp [size, RANDOMNESS_LEN]⟩,
    splitDigests ⟨bytes.data.extract 696 1208, by simp [size, LOG_LIFETIME, DIGEST_LEN]⟩⟩, ?_⟩
  -- Re-joining the three adjacent slices gives the whole string.
  apply ByteArray.ext
  simp [encodeSignature, packBytes, Array.extract_append_extract, ← size]
  omega

/-- Decoding then re-encoding a 32-byte string returns it. -/
theorem encodePublicKey_decodePublicKey {bytes : ByteArray} (sized : bytes.size = PUB_KEY_SIZE) :
    (decodePublicKey bytes).map encodePublicKey = .ok bytes := by
  obtain ⟨pk, rfl⟩ := encodePublicKey_surjective sized
  simp [Except.map]

/-- Decoding then re-encoding a 1208-byte string returns it. -/
theorem encodeSignature_decodeSignature {bytes : ByteArray} (sized : bytes.size = SIG_SIZE) :
    (decodeSignature bytes).map encodeSignature = .ok bytes := by
  obtain ⟨sig, rfl⟩ := encodeSignature_surjective sized
  simp [Except.map]

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
  rw [decodePublicKey, dif_neg wrong]

/-- A signature string of any other length than 1208 bytes is rejected. -/
theorem decodeSignature_badSize {bytes : ByteArray} (wrong : bytes.size ≠ SIG_SIZE) :
    decodeSignature bytes = .error (.badSignatureSize bytes.size) := by
  rw [decodeSignature, dif_neg wrong]

/-- Public key decoding succeeds exactly on 32-byte strings. -/
theorem decodePublicKey_success_iff (bytes : ByteArray) :
    (∃ pk, decodePublicKey bytes = .ok pk) ↔ bytes.size = PUB_KEY_SIZE := by
  constructor
  · rintro ⟨pk, read⟩
    exact Decidable.byContradiction fun wrong => by simp [decodePublicKey_badSize wrong] at read
  · intro sized
    obtain ⟨pk, rfl⟩ := encodePublicKey_surjective sized
    exact ⟨pk, by simp⟩

/-- Signature decoding succeeds exactly on 1208-byte strings. -/
theorem decodeSignature_success_iff (bytes : ByteArray) :
    (∃ sig, decodeSignature bytes = .ok sig) ↔ bytes.size = SIG_SIZE := by
  constructor
  · rintro ⟨sig, read⟩
    exact Decidable.byContradiction fun wrong => by simp [decodeSignature_badSize wrong] at read
  · intro sized
    obtain ⟨sig, rfl⟩ := encodeSignature_surjective sized
    exact ⟨sig, by simp⟩

end EthLib.Cryptography.Xmss

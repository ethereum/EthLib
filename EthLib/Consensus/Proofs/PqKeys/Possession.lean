module

public import EthLib.Consensus.PqKeys.Possession
public import EthLib.Consensus.Proofs.PqKeys.Containers
public import EthLib.Consensus.Proofs.Signing
public import EthLib.Cryptography.Proofs.Xmss.Correctness
public import EthLib.Cryptography.Proofs.Xmss.Serialization

/-!
# Proofs: the check of a proof of possession

Every 32-byte string decodes to a leanXMSS public key, and every 2404-byte string to a signature.

Every pair of keys has a possession root on every chain.

So the check reduces to two steps: the leaf index is 0, and the proof verifies on the root.

Completeness: a key generated from a seed, signing its root at leaf 0, gives a proof that passes.

A proof at any other leaf index fails, whatever its bytes.
-/

@[expose] public section

namespace EthLib.Consensus.PqKeys

open Base Cryptography Cryptography.Bls Serialization.Ssz

/-- A computation whose result is some value returns that value. -/
theorem eq_ok_toOption_get {ε α : Type} (e : Except ε α) (ok : e.toOption.isSome) :
    e = .ok (e.toOption.get ok) := by
  cases e <;> simp [Except.toOption] at ok ⊢

/-- The 32 bytes of a leanXMSS public key. -/
def xmssPublicKeyBytes (pk : Xmss.PublicKey) : XMSSPublicKey :=
  ⟨(Xmss.encodePublicKey pk).data, by
    simp [Xmss.Constants.pub_key_size_eq]⟩

/-- The 2404 bytes of a leanXMSS signature. -/
def xmssSignatureBytes (σ : Xmss.Signature) : XMSSSignature :=
  ⟨(Xmss.encodeSignature σ).data, by
    simp [Xmss.Constants.sig_size_eq]⟩

theorem decodePublicKey_isOk (key : XMSSPublicKey) :
    ((Xmss.decodePublicKey (Base.packBytes key)).toOption).isSome := by
  simp [Xmss.decodePublicKey, Base.packBytes, ByteArray.size, Xmss.Constants.pub_key_size_eq,
    Except.toOption]

theorem decodeSignature_isOk (proof : XMSSSignature) :
    ((Xmss.decodeSignature (Base.packBytes proof)).toOption).isSome := by
  simp [Xmss.decodeSignature, Base.packBytes, ByteArray.size, Xmss.Constants.sig_size_eq,
    Except.toOption]

/-- The leanXMSS public key that 32 bytes encode. -/
def publicKeyOfBytes (key : XMSSPublicKey) : Xmss.PublicKey :=
  (Xmss.decodePublicKey (Base.packBytes key)).toOption.get (decodePublicKey_isOk key)

/-- The leanXMSS signature that 2404 bytes encode. -/
def signatureOfBytes (proof : XMSSSignature) : Xmss.Signature :=
  (Xmss.decodeSignature (Base.packBytes proof)).toOption.get (decodeSignature_isOk proof)

/-- Every 32-byte string decodes to a leanXMSS public key. -/
theorem decodePublicKey_packBytes (key : XMSSPublicKey) :
    Xmss.decodePublicKey (Base.packBytes key) = .ok (publicKeyOfBytes key) :=
  eq_ok_toOption_get _ _

/-- Every 2404-byte string decodes to a leanXMSS signature. -/
theorem decodeSignature_packBytes (proof : XMSSSignature) :
    Xmss.decodeSignature (Base.packBytes proof) = .ok (signatureOfBytes proof) :=
  eq_ok_toOption_get _ _

/-- The leaf index of the decoded signature is the index that the bytes carry. -/
theorem signatureOfBytes_leafIndex (proof : XMSSSignature) :
    (signatureOfBytes proof).leafIndex = xmssSignatureIndex proof := by
  have decoded := decodeSignature_packBytes proof
  rw [Xmss.decodeSignature, dite_eq_left (by simp [Base.packBytes, ByteArray.size,
    Xmss.Constants.sig_size_eq])] at decoded
  rw [← Except.ok.inj decoded]
  rfl

/-- Decoding the bytes of a public key gives the key back. -/
@[simp] theorem publicKeyOfBytes_xmssPublicKeyBytes (pk : Xmss.PublicKey) :
    publicKeyOfBytes (xmssPublicKeyBytes pk) = pk := by
  have decoded := decodePublicKey_packBytes (xmssPublicKeyBytes pk)
  have packed : Base.packBytes (xmssPublicKeyBytes pk) = Xmss.encodePublicKey pk := rfl
  rw [packed, Xmss.decodePublicKey_encodePublicKey, Except.ok.injEq] at decoded
  exact decoded.symm

/-- Decoding the bytes of a signature gives the signature back. -/
@[simp] theorem signatureOfBytes_xmssSignatureBytes (σ : Xmss.Signature) :
    signatureOfBytes (xmssSignatureBytes σ) = σ := by
  have decoded := decodeSignature_packBytes (xmssSignatureBytes σ)
  have packed : Base.packBytes (xmssSignatureBytes σ) = Xmss.encodeSignature σ := rfl
  rw [packed, Xmss.decodeSignature_encodeSignature, Except.ok.injEq] at decoded
  exact decoded.symm

theorem possessionSigningRoot_isOk (config : Config) (genesisValidatorsRoot : Root)
    (pubkey : BLSPubkey) (xmssPublicKey : XMSSPublicKey) :
    (possessionSigningRoot config genesisValidatorsRoot pubkey xmssPublicKey).toOption.isSome := by
  obtain ⟨domain, computed⟩ := computeDomain_total config DOMAIN_PQ_KEY_POSSESSION
    config.GENESIS_FORK_VERSION genesisValidatorsRoot
  obtain ⟨root, signed⟩ := computeSigningRoot_total (PQKeyPossession.mk pubkey xmssPublicKey) domain
  simp [possessionSigningRoot, computed, signed, bind, Except.bind, Except.toOption]

/-- The possession root of two keys on a chain. -/
def possessionRoot (config : Config) (genesisValidatorsRoot : Root) (pubkey : BLSPubkey)
    (xmssPublicKey : XMSSPublicKey) : Root :=
  (possessionSigningRoot config genesisValidatorsRoot pubkey xmssPublicKey).toOption.get
    (possessionSigningRoot_isOk config genesisValidatorsRoot pubkey xmssPublicKey)

/-- Every pair of keys has a possession root on every chain. -/
theorem possessionSigningRoot_eq (config : Config) (genesisValidatorsRoot : Root)
    (pubkey : BLSPubkey) (xmssPublicKey : XMSSPublicKey) :
    possessionSigningRoot config genesisValidatorsRoot pubkey xmssPublicKey =
      .ok (possessionRoot config genesisValidatorsRoot pubkey xmssPublicKey) :=
  eq_ok_toOption_get _ _

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))
  (config : Config) (genesisValidatorsRoot : Root) (pubkey : BLSPubkey)
  (xmssPublicKey : XMSSPublicKey) (proof : XMSSSignature)

/-- The check is the leaf index, then leanXMSS verification of the proof on the possession root.

It holds over every hash, in every lawful monad. -/
theorem isValidPqPossessionProofWith_eq :
    isValidPqPossessionProofWith H config genesisValidatorsRoot pubkey xmssPublicKey proof =
      if xmssSignatureIndex proof = PQ_POSSESSION_XMSS_INDEX then
        Xmss.verifyWith H (publicKeyOfBytes xmssPublicKey)
          (possessionRoot config genesisValidatorsRoot pubkey xmssPublicKey)
          (signatureOfBytes proof)
      else pure false := by
  unfold isValidPqPossessionProofWith
  rw [possessionSigningRoot_eq, decodePublicKey_packBytes, decodeSignature_packBytes]
  by_cases index : xmssSignatureIndex proof = PQ_POSSESSION_XMSS_INDEX <;> simp [index]

/-- A proof at a leaf index other than 0 fails, whatever its bytes, without hashing. -/
theorem isValidPqPossessionProofWith_of_index_ne
    (other : xmssSignatureIndex proof ≠ PQ_POSSESSION_XMSS_INDEX) :
    isValidPqPossessionProofWith H config genesisValidatorsRoot pubkey xmssPublicKey proof =
      pure false := by
  rw [isValidPqPossessionProofWith_eq, ite_eq_right other]

/-- A valid proof carries leaf index 0, and verifies under the key on the possession root. -/
theorem verify_of_isValidPqPossessionProof
    (valid : isValidPqPossessionProof config genesisValidatorsRoot pubkey xmssPublicKey proof) :
    xmssSignatureIndex proof = PQ_POSSESSION_XMSS_INDEX ∧
      Xmss.verify (publicKeyOfBytes xmssPublicKey)
        (possessionRoot config genesisValidatorsRoot pubkey xmssPublicKey)
        (signatureOfBytes proof) = true := by
  unfold isValidPqPossessionProof at valid
  rw [isValidPqPossessionProofWith_eq] at valid
  by_cases index : xmssSignatureIndex proof = PQ_POSSESSION_XMSS_INDEX
  · rw [ite_eq_left index] at valid
    exact ⟨index, valid⟩
  · rw [ite_eq_right index] at valid
    exact absurd valid (by simp)

/-- Completeness: a generated key that signs its possession root at leaf 0 gives a valid proof.

Signing fails only when a one-time key finds no codeword.

So the hypothesis on signing is the one that leanXMSS correctness makes. -/
theorem isValidPqPossessionProof_sign {seed : Xmss.Seed} {sk : Xmss.SecretKey}
    {pk : Xmss.PublicKey} {σ : Xmss.Signature}
    (generated : Xmss.keyGen seed = (sk, pk))
    (signed : Xmss.sign sk PQ_POSSESSION_XMSS_INDEX
      (possessionRoot config genesisValidatorsRoot pubkey (xmssPublicKeyBytes pk)) = .ok σ) :
    isValidPqPossessionProof config genesisValidatorsRoot pubkey (xmssPublicKeyBytes pk)
      (xmssSignatureBytes σ) = true := by
  have index : xmssSignatureIndex (xmssSignatureBytes σ) = PQ_POSSESSION_XMSS_INDEX := by
    rw [← signatureOfBytes_leafIndex, signatureOfBytes_xmssSignatureBytes]
    exact (Xmss.sign_eq_ok rfl rfl signed).1
  unfold isValidPqPossessionProof
  rw [isValidPqPossessionProofWith_eq, ite_eq_left index,
    publicKeyOfBytes_xmssPublicKeyBytes, signatureOfBytes_xmssSignatureBytes]
  exact Xmss.verify_keyGen_sign generated signed

end EthLib.Consensus.PqKeys

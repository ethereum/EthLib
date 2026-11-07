module

public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Cryptography.Proofs.Bls.HashToCurveValidity

/-!
# Proofs: BLS signing never fails, and the rejected inputs

Source: draft-irtf-cfrg-bls-signature-04, §2.6 to §2.9 and §3.3.

Signing never fails, because the hash to curve never fails.

Each other theorem names an input that an operation rejects.

The decoder of a secret key accepts exactly the 32-byte encodings of the nonzero scalars below `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Signatures

open EthLib.Cryptography.Bls

/-- The core signature never fails. -/
theorem coreSign_ok (sk : SecretKey) (msg dst : ByteArray) :
    ∃ sig, coreSign sk msg dst = .ok sig := by
  obtain ⟨q, hq, -⟩ := HashToCurve.hashToG2_total msg dst
  refine ⟨pointToSignature (G2.mul q sk.val), ?_⟩
  -- Rewrite the hash first, so the kernel never evaluates it on a variable message.
  unfold coreSign
  rw [hq]
  rfl

/-- Signing never fails. -/
theorem sign_ok (sk : SecretKey) (msg : ByteArray) : ∃ sig, sign sk msg = .ok sig :=
  coreSign_ok sk msg DST

/-- The proof of possession never fails. -/
theorem popProve_ok (sk : SecretKey) : ∃ proof, popProve sk = .ok proof :=
  coreSign_ok sk _ POP_DST

/-- Aggregation rejects an empty list (§2.8). -/
theorem aggregate_empty : aggregate #[] = .error .emptySignatureList := rfl

/-- The core aggregate verification rejects an empty key list (§2.9). -/
theorem coreAggregateVerify_empty (msgs : Array ByteArray) (sig dst : ByteArray) :
    coreAggregateVerify #[] msgs sig dst = false := rfl

/-- The core aggregate verification rejects lists of two sizes. -/
theorem coreAggregateVerify_size_ne {pks msgs : Array ByteArray} (h : pks.size ≠ msgs.size)
    (sig dst : ByteArray) : coreAggregateVerify pks msgs sig dst = false := by
  unfold coreAggregateVerify
  rw [ite_eq_left_of_eq_true _ _ (by simp [h])]

/-- Key validation rejects a public key that is not 48 bytes. -/
theorem keyValidatePoint_size_ne {pk : ByteArray} (h : pk.size ≠ 48) :
    G1.keyValidatePoint pk = .error .invalidG1Point := by
  simp [G1.keyValidatePoint, G1.uncompress, h, bind, Except.bind]

/-- The core verification rejects a public key that is not 48 bytes. -/
theorem coreVerify_badPubkeySize {pk : ByteArray} (h : pk.size ≠ 48) (msg sig dst : ByteArray) :
    coreVerify pk msg sig dst = false := by
  unfold coreVerify
  rw [keyValidatePoint_size_ne h]
  split <;> simp

/-- Verification rejects a public key that is not 48 bytes. -/
theorem verify_badPubkeySize {pk : ByteArray} (h : pk.size ≠ 48) (msg sig : ByteArray) :
    verify pk msg sig = false :=
  coreVerify_badPubkeySize h msg sig DST

/-- The secret key decoder gives a key exactly when the decoder of scalars gives its scalar. -/
theorem SecretKey.fromBytes_eq_ok_iff {bytes : ByteArray} {sk : SecretKey} :
    SecretKey.fromBytes bytes = .ok sk ↔ Fr.fromBytesBE bytes = .ok sk.val := by
  obtain ⟨x, hx⟩ := sk
  unfold SecretKey.fromBytes
  cases hd : Fr.fromBytesBE bytes with
  | error e => simp
  | ok y =>
    by_cases hy : y = 0
    · simp [hy, Ne.symm hx]
    · simp [hy, Subtype.ext_iff, eq_comm]

/-- Decoding the 32 bytes of a secret key gives it back. -/
theorem SecretKey.fromBytes_toBytesBE (sk : SecretKey) :
    SecretKey.fromBytes sk.val.toBytesBE = .ok sk :=
  SecretKey.fromBytes_eq_ok_iff.mpr (Fr.fromBytesBE_toBytesBE sk.val)

/-- The secret key decoder rejects the encoding of zero (§2.3). -/
theorem SecretKey.fromBytes_zero :
    SecretKey.fromBytes (0 : Fr).toBytesBE = .error .invalidSecretKey := by
  unfold SecretKey.fromBytes
  rw [Fr.fromBytesBE_toBytesBE]
  simp

end EthLib.Cryptography.Bls.Signatures

module

public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Cryptography.Proofs.Bls.HashToCurveValidity

/-!
# Proofs: BLS signing never fails, and the rejected inputs

Source: draft-irtf-cfrg-bls-signature-04, §2.6 to §2.9 and §3.3.

Signing never fails, because the hash to curve never fails.

Each other theorem names an input that an operation rejects.
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

end EthLib.Cryptography.Bls.Signatures

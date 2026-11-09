module

public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: the order of honest keys in aggregate verification

Fast aggregate verification sums the public keys before verifying the signature.

A permutation of honest keys preserves that sum, including repeated keys.

The operation is the `FastAggregateVerify` of [draft-04][draft-04], §3.3.4.

[draft-04]: https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Signatures

open scoped EthLib.Cryptography.Bls.Fr

/-- Permuting honest public keys leaves fast aggregate verification unchanged. -/
theorem fastAggregateVerify_pkBytes_perm {keys keys' : List SecretKey}
    (perm : keys.Perm keys') (msg sig : ByteArray) :
    fastAggregateVerify (keys.map pkBytes).toArray msg sig =
      fastAggregateVerify (keys'.map pkBytes).toArray msg sig := by
  by_cases nonempty : keys = []
  · subst keys
    have empty : keys' = [] := perm.symm.eq_nil
    subst keys'
    rfl
  · have nonempty' : keys' ≠ [] := by
      intro empty
      subst keys'
      exact nonempty perm.eq_nil
    rw [fastAggregateVerify_eq_verify keys nonempty,
      fastAggregateVerify_eq_verify keys' nonempty', (perm.map (·.val)).sum_eq]

/-- The signatures carried by a list are the outputs of signing with its keys. -/
private theorem mapM_sign_eq {keys : List SecretKey} {signatures : List BLSSignature}
    {message : ByteArray}
    (signed : List.Forall₂ (fun key signature => sign key message = .ok signature)
      keys signatures) :
    keys.mapM (fun key => sign key message) = .ok signatures := by
  induction signed with
  | nil => rfl
  | cons head _ ih =>
    rw [List.mapM_cons, head, ih]
    rfl

/-- An aggregate of signatures on one message verifies under their signing keys.

The keys must be nonempty and have a nonzero scalar sum. -/
theorem fastAggregateVerify_aggregate_of_forall₂ {keys : List SecretKey}
    {signatures : List BLSSignature} {message : ByteArray} {signature : BLSSignature}
    (signed : List.Forall₂ (fun key sig => sign key message = .ok sig) keys signatures)
    (nonempty : keys ≠ []) (sum : (keys.map (·.val)).sum ≠ 0)
    (aggregated : aggregate (signatures.map sigBytes).toArray = .ok signature) :
    fastAggregateVerify (keys.map pkBytes).toArray message (sigBytes signature) = true := by
  obtain ⟨signatures', signs, signature', built, verifies⟩ :=
    fastAggregateVerify_aggregate keys nonempty sum message
  have sameSignatures : signatures' = signatures :=
    Except.ok.inj (signs.symm.trans (mapM_sign_eq signed))
  subst signatures'
  have sameAggregate : signature' = signature :=
    Except.ok.inj (built.symm.trans aggregated)
  simpa only [sameAggregate] using verifies

end EthLib.Cryptography.Bls.Signatures

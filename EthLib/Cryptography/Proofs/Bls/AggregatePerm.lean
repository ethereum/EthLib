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

end EthLib.Cryptography.Bls.Signatures

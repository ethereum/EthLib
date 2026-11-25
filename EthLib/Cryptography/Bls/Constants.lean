module

/-!
# `Constants`

The byte lengths of a public key in `G1` and a signature in `G2`, as in the BLS signature draft, §2.1:
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-2.1>
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Constants

/-- The length of a public key in bytes: one compressed point of `G1`. -/
def BYTES_PER_PUBKEY : Nat :=
  -- One `Fp` coordinate of 381 bits, with the 3 flag bits on top, in the pairing-friendly curves draft:
  -- <https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-11#appendix-C>
  48

/-- The length of a signature in bytes: one compressed point of `G2`. -/
def BYTES_PER_SIGNATURE : Nat :=
  -- One `Fp2` coordinate, two `Fp` elements of 48 bytes each, in the same appendix.
  96

end EthLib.Cryptography.Bls.Constants

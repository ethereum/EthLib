module

/-!
# `Constants`

The two moduli and the parameter of BLS12-381, and the byte lengths of its keys and signatures.

The byte lengths follow the BLS signature draft, §2.1:
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-2.1>

This module imports nothing, so a check that reads only these numbers imports nothing else.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- BLS12-381 base field modulus.

In hexadecimal, `p` is the 96 digits of these two lines, joined:

- `1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624`
- `1eabfffeb153ffffb9feffffffffaaab`
-/
def Fp.modulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- BLS12-381 scalar field modulus (= group order). -/
def Fr.modulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- `|t|` for the BLS parameter `t = -0xd201000000010000`, which the pairing calls `x`. -/
def blsX : Nat := 0xD201000000010000

end EthLib.Cryptography.Bls

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

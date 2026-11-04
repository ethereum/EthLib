module

public import EthLib.Cryptography.Secp256k1.Encoding

/-!
# ECDH over secp256k1

The Diffie-Hellman primitive of SEC 1 v2 §3.3.1: the shared secret is the `x` of `d Q`.

The cofactor is 1, so the primitive and its cofactor variant agree.

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

/--
The shared secret of the private key `sk` and the public key `pk`, as 32 big-endian bytes.

The public key must be on the curve and not `O`, as SEC 1 v2 §3.2.2.1 checks.

Step 2 rejects the point `O`, which a zero key gives.

The key is secret, and this function makes no constant-time claim.
-/
def ecdh (sk : Fn) (pk : Point) : Except Secp256k1Error (Vector UInt8 32) :=
  if pk = .infinity then .error .pointAtInfinity
  else if !pk.isOnCurve then .error .notOnCurve
  else
    -- Step 1: `P = d Q`.
    match Point.mul sk pk with
    | .infinity => .error .pointAtInfinity
    -- Steps 3 and 4: `z = x_P`, as 32 bytes by SEC 1 v2 §2.3.5.
    | .affine x _ => .ok ⟨x.toBytes.toArray, by simp [Fp.length_toBytes]⟩

end EthLib.Cryptography.Secp256k1

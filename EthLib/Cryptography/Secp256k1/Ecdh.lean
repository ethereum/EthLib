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
  -- §3.2.2.1, step 1: check that `Q` is not `O`.
  if pk = .infinity then .error .pointAtInfinity
  -- §3.2.2.1, step 2: check that `y_Q^2 = x_Q^3 + a x_Q + b (mod p)`.
  --
  -- The coordinates are elements of the field, so they already lie in `[0, p - 1]`.
  --
  -- §3.2.2.1, step 4, `n Q = O`, holds for every point of the curve, since the cofactor is 1.
  else if !pk.isOnCurve then .error .notOnCurve
  else
    -- §3.3.1, step 1: `P = (x_P, y_P) = d_U Q_V`.
    match Point.mul sk pk with
    -- §3.3.1, step 2: if `P = O`, output "invalid" and stop.
    | .infinity => .error .pointAtInfinity
    -- §3.3.1, step 3: output `z = x_P`, as 32 bytes by SEC 1 v2 §2.3.5.
    | .affine x _ => .ok ⟨x.toBytes.data, by simp [Sec1.fieldToBytes, sec1]⟩

end EthLib.Cryptography.Secp256k1

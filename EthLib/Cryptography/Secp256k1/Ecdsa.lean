module

public import EthLib.Cryptography.Ecdsa.Curve
public import EthLib.Cryptography.Secp256k1.Encoding
public import EthLib.Cryptography.Secp256k1.MulAdd

/-!
# `Secp256k1.Ecdsa`

ECDSA verification over secp256k1, from SEC 1 v2 §4.1.4, and the low-s rule of EIP-2.

Verification is that of every curve of cofactor 1, with this curve's products and inverse.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

/-- The integer `e` of a hash, by SEC 1 v2 §4.1.4 step 3. -/
def hashToInt (hash : Vector UInt8 32) : Nat :=
  -- Step 3.2: `E = H`, since `ceil(log2 n) = 256 = 8 hashlen` keeps every bit.
  --
  -- Steps 3.1, 3.3 and 3.4: the octets of `H`, read as a big-endian integer by SEC 1 v2 §2.3.8.
  Base.ByteOrder.ofBE hash.toList

/-- secp256k1 as ECDSA uses it: the base point `G`, its products, and the inverse mod `n`. -/
@[inline] def domain : Cryptography.Ecdsa.Curve Fp.modulus Fn.modulus :=
  ⟨Point.generator, Point.mul, Point.mulAdd, Fn.inv⟩

/-- Whether `(r, s)` is a valid signature on `hash` under the public key `q`, by SEC 1 v2 §4.1.4.

`q` must be a valid public key, as SEC 1 v2 §3.2.2.1 checks: on the curve, and not `O`.

A key from the decoder always is, and verification rejects any other. -/
def verify (q : Point) (hash : Vector UInt8 32) (r s : Nat) : Bool :=
  -- Step 3: `e` from the hash `H`; the other steps are those of every curve.
  domain.verify q (hashToInt hash) r s

/-- The low-s rule of EIP-2: `s` is at most `n / 2`, rounded down.

Exactly one of `s` and `n - s` passes it, since `n` is odd.

The rule is not part of ECDSA, and the `ecrecover` precompile does not apply it.

So it is a separate test. -/
def isLowS (s : Nat) : Bool :=
  -- `(r, n - s)` is valid whenever `(r, s)` is, because it rebuilds `-R`, which has the same `x`.
  --
  -- EIP-2 removes that freedom from transactions: their `s` must be at most `n / 2`.
  s ≤ Fn.modulus / 2

end Ecdsa

end EthLib.Cryptography.Secp256k1

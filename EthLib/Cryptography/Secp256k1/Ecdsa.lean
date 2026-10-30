import EthLib.Cryptography.Secp256k1.Encoding

/-!
# `Secp256k1.Ecdsa`

ECDSA verification over secp256k1, from SEC 1 v2 §4.1.4.

A signature on a 32-byte hash is a pair of integers `(r, s)`.

The signer picks a secret nonce `k`, sets `R = k G`, takes `r = x_R mod n`, and sets `s = k^(-1) (e + r d) mod n`.

Here `d` is the private key and `e` the hash read as an integer.

The verifier knows `Q = d G`, not `d`, and rebuilds `R` from public values:

```text
    u1 = e s^(-1),   u2 = r s^(-1)                      mod n
    u1 G + u2 Q = s^(-1) (e + r d) G = k G = R
```

The signature is valid when the `x` of that point is `r` mod `n`.

## The low-s rule

`(r, n - s)` is valid whenever `(r, s)` is, because it rebuilds `-R`, which has the same `x`.

EIP-2 removes that freedom from transactions: their `s` must be at most `n / 2`.

The rule is not part of ECDSA, and the `ecrecover` precompile does not apply it, so it is a separate test, `isLowS`.
-/

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

/-- The integer `e` of a hash, by SEC 1 v2 §4.1.4 step 3.

`n` has 256 bits, as many as the hash, so step 3.2 keeps every bit. -/
def hashToInt (hash : Vector UInt8 32) : Nat := ofBytesBE hash.toList

/-- Whether `(r, s)` is a valid signature on `hash` under the public key `q`, by SEC 1 v2 §4.1.4.

`q` must be a valid public key, as SEC 1 v2 §3.2.2.1 checks: on the curve, and not `O`.

A key from `Point.decode` always is.

The key `O` would accept any `r` that some `u1 G` hits, so it is rejected here too. -/
def verify (q : Point) (hash : Vector UInt8 32) (r s : Nat) : Bool :=
  -- Step 1: `r` and `s` lie in `[1, n - 1]`, and the key is valid.
  if hr : 0 < r ∧ r < Fn.modulus then
    if hs : 0 < s ∧ s < Fn.modulus then
      if q ≠ .infinity ∧ q.isOnCurve then
        -- Steps 3 and 4: `e` acts mod `n`, like every scalar.
        let e : Fn := Fin.ofNat _ (hashToInt hash)
        let sInv := Fn.inv ⟨s, hs.2⟩
        let u1 := e * sInv
        let u2 := (⟨r, hr.2⟩ : Fn) * sInv
        -- Steps 5 to 8: `R = u1 G + u2 Q` must not be `O`, and `x_R mod n` must be `r`.
        match Point.mul u1 .generator + Point.mul u2 q with
        | .infinity => false
        | .affine x _ => x.val % Fn.modulus == r
      else false
    else false
  else false

/-- The low-s rule of EIP-2: `s` is at most `n / 2`, rounded down.

Exactly one of `s` and `n - s` passes it, since `n` is odd. -/
def isLowS (s : Nat) : Bool := s ≤ Fn.modulus / 2

end Ecdsa

end EthLib.Cryptography.Secp256k1

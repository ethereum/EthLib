module

public import EthLib.Cryptography.Secp256k1.Encoding
public import EthLib.Cryptography.Secp256k1.MulAdd

/-!
# `Secp256k1.Ecdsa`

ECDSA verification over secp256k1, from SEC 1 v2 §4.1.4, and the low-s rule of EIP-2.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

/-- The integer `e` of a hash, by SEC 1 v2 §4.1.4 step 3. -/
def hashToInt (hash : Vector UInt8 32) : Nat :=
  -- Step 3.2: `E = H`, since `ceil(log2 n) = 256 = 8 hashlen` keeps every bit.
  --
  -- Steps 3.1, 3.3 and 3.4: the octets of `H`, read as a big-endian integer by SEC 1 v2 §2.3.8.
  Base.bytesToNat hash.toList

/-- Whether `(r, s)` is a valid signature on `hash` under the public key `q`, by SEC 1 v2 §4.1.4.

`q` must be a valid public key, as SEC 1 v2 §3.2.2.1 checks: on the curve, and not `O`.

A key from the decoder always is.

The key `O` would accept any `r` that some `u1 G` hits, so it is rejected here too. -/
def verify (q : Point) (hash : Vector UInt8 32) (r s : Nat) : Bool :=
  -- A signature on a 32-byte hash is a pair of integers `(r, s)`.
  --
  -- Step 1: if `r` and `s` are not both integers in `[1, n-1]`, output "invalid".
  if hr : 0 < r ∧ r < Fn.modulus then
    if hs : 0 < s ∧ s < Fn.modulus then
      -- Not a step of §4.1.4: the key check of SEC 1 v2 §3.2.2.1, on the curve and not `O`.
      if q ≠ .infinity ∧ q.isOnCurve then
        -- Step 2 is done by the caller: the input is the hash `H`, not the message.
        --
        -- Step 3: `e` from `H`, taken mod `n`, which leaves `u1` of step 4 unchanged.
        let e : Fn := Fin.ofNat _ (hashToInt hash)
        let sInv := Fn.inv ⟨s, hs.2⟩
        -- Step 4: `u1 = e s^(-1) mod n` and `u2 = r s^(-1) mod n`.
        let u1 := e * sInv
        let u2 := (⟨r, hr.2⟩ : Fn) * sInv
        -- Step 5: `R = (x_R, y_R) = u1 G + u2 Q_U`, and "invalid" if `R = O`.
        --
        -- For a valid signature, `R = s^(-1) (e + r d_U) G = k G`, the signer's point.
        match Point.mulAdd u1 .generator u2 q with
        | .infinity => false
        -- Steps 6 to 8: `v = x_R mod n`, and "valid" exactly when `v = r`.
        --
        -- The signer's `r` is the `x` of `R = k G` mod `n`, for its secret nonce `k`.
        | .affine x _ => x.val % Fn.modulus == r
      else false
    else false
  else false

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

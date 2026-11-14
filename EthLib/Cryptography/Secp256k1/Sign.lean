module

public import EthLib.Cryptography.Secp256k1.Ecdsa
public import EthLib.Cryptography.Rfc6979

/-!
# ECDSA signing over secp256k1

Signing follows SEC 1 v2 §4.1.3, with the deterministic nonce of RFC 6979 §3.2.

The nonce generator is HMAC-SHA-256, keyed by the private key and the hash.

The signature is in the low-s form of EIP-2, with the parity of `y_R` as its recovery bit.

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

open Point Rfc6979

/--
Steps b to g of RFC 6979 §3.2 with the order `n`: the generator seeded with the key and the hash.

The key is secret, and this function makes no constant-time claim.
-/
def nonceSeed (x : Fn) (hash : Vector UInt8 32) : NonceState :=
  Rfc6979.nonceSeed Fn.modulus x.val hash

/--
Steps 1 to 6 of SEC 1 v2 §4.1.3, over the candidates of the nonce generator.

A candidate is rejected when it is not in `[1, n - 1]`, or when `r = 0`, by RFC 6979 §3.2 step h.3.

It is also rejected when `s = 0`, by step 6 of SEC 1 v2 §4.1.3.

The result is `(r, s, odd)`, where `odd` is the parity of `y_R`.

The key is secret, and this function makes no constant-time claim.
-/
def signWith (d e : Fn) : (fuel : Nat) → NonceState → Except Secp256k1Error (Fn × Fn × Bool)
  | 0, _ => .error .noNonce
  | fuel + 1, state =>
    let (t, state) := nonceNext state
    if ht : 0 < t ∧ t < Fn.modulus then
      let k : Fn := ⟨t, ht.2⟩
      match mul k generator with
      | .infinity => signWith d e fuel (nonceReject state)
      | .affine x y =>
        -- Step 3: `r = x_R mod n`.
        let r : Fn := Fin.ofNat _ x.val
        -- Step 5: `s = k^(-1) (e + r d) mod n`.
        let s := k.inv * (e + r * d)
        if r = 0 ∨ s = 0 then signWith d e fuel (nonceReject state)
        -- Recovery with the ids 0 and 1 needs `x_R = r`.
        else if Fn.modulus ≤ x.val then .error .unrecoverableNonce
        else .ok (r, s, decide (y.val % 2 = 1))
    else signWith d e fuel (nonceReject state)

/--
The signature `(r, s)` of a 32-byte hash, with its recovery bit, by SEC 1 v2 §4.1.3 and RFC 6979.

The low-s rule of EIP-2 replaces `s` by `n - s` when `s > n / 2`.

That signature rebuilds `-R`, so the recovery bit flips with it.

The key is secret, and this function makes no constant-time claim.
-/
def sign (sk : Fn) (hash : Vector UInt8 32) : Except Secp256k1Error (Fn × Fn × Bool) :=
  if sk = 0 then .error .zeroPrivateKey
  else do
    -- Step 4: `e` is the hash read as an integer mod `n`.
    let (r, s, odd) ← signWith sk (Fin.ofNat _ (hashToInt hash)) MAX_NONCES (nonceSeed sk hash)
    if isLowS s.val then .ok (r, s, odd) else .ok (r, -s, !odd)

end Ecdsa

end EthLib.Cryptography.Secp256k1

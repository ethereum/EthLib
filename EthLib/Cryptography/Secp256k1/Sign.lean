module

public import EthLib.Cryptography.Secp256k1.Ecdsa
public import EthLib.Cryptography.Rfc6979

/-!
# ECDSA signing over secp256k1

Signing follows SEC 1 v2 §4.1.3, with the deterministic nonce of RFC 6979 §3.2.

The signature is in the low-s form of EIP-2, with the parity of `y_R` as its recovery bit.

RFC 6979 is read with its verified [erratum 3812][eid3812].

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).

[eid3812]: https://www.rfc-editor.org/errata/eid3812
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
  -- The nonce generator is HMAC-SHA-256, keyed by the private key and the hash.
  Rfc6979.nonceSeed Fn.modulus x.val hash

/--
Steps 1 to 3, 6 and 7 of SEC 1 v2 §4.1.3, over the candidates of the nonce generator.

The result is `(r, s, odd)`, where `odd` is the parity of `y_R`.

The key is secret, and this function makes no constant-time claim.
-/
def signWith (d e : Fn) (fuel : Nat) (state : NonceState) :
    Except Secp256k1Error (Fn × Fn × Bool) :=
  -- The loop is that of every curve.
  match domain.signWith d e fuel state with
  | none => .error .noNonce
  | some (r, s, x, y) =>
    -- Step 3 lets `r` meet a publicly verifiable criterion: here `x_R = r`.
    --
    -- Recovery with the ids 0 and 1 needs it, and signing fails rather than return to step 1.
    if Fn.modulus ≤ x.val then .error .unrecoverableNonce
    -- Step 7: output `S = (r, s)`, with the parity of `y_R` to recover `R` from `r`.
    else .ok (r, s, decide (y.val % 2 = 1))

/--
The signature `(r, s)` of a 32-byte hash, with its recovery bit, by SEC 1 v2 §4.1.3 and RFC 6979.

The low-s rule of EIP-2 replaces `s` by `n - s` when `s > n / 2`.

That signature rebuilds `-R`, so the recovery bit flips with it.

The key is secret, and this function makes no constant-time claim.
-/
def sign (sk : Fn) (hash : Vector UInt8 32) : Except Secp256k1Error (Fn × Fn × Bool) :=
  -- A private key lies in `[1, n-1]`, by SEC 1 v2 §3.2.1 step 1.
  if sk = 0 then .error .zeroPrivateKey
  else do
    -- Step 4 is done by the caller: the input is the hash `H`, not the message.
    --
    -- Step 5: `e` is `H` read as an integer, then taken mod `n`.
    let (r, s, odd) ← signWith sk (Fin.ofNat _ (hashToInt hash)) MAX_NONCES (nonceSeed sk hash)
    -- After step 7, SEC 1 lets the signer replace `(r, s)` by `(r, -s mod n)`, as EIP-2 asks.
    --
    -- The low-s rule of EIP-2 replaces `s` by `n - s` when `s > n / 2`.
    --
    -- That signature rebuilds `-R`, so the recovery bit flips with it.
    if isLowS s.val then .ok (r, s, odd) else .ok (r, -s, !odd)

end Ecdsa

end EthLib.Cryptography.Secp256k1

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
Steps 1 to 3, 6 and 7 of SEC 1 v2 §4.1.3, over the candidates of the nonce generator.

The result is `(r, s, odd)`, where `odd` is the parity of `y_R`.

The key is secret, and this function makes no constant-time claim.
-/
def signWith (d e : Fn) : (fuel : Nat) → NonceState → Except Secp256k1Error (Fn × Fn × Bool)
  -- EthLib's bound on the candidates: RFC 6979 §3.2 step h loops without one.
  | 0, _ => .error .noNonce
  | fuel + 1, state =>
    -- RFC 6979 §3.2 steps h.1 and h.2: `V = HMAC_K(V)`, and `T = V` as it has `qlen` bits.
    --
    -- Step h.3: the candidate `k = bits2int(T)`.
    let (t, state) := nonceNext state
    -- Step h.3 also asks `k` in `[1, q-1]`, or the generator moves on to the next candidate.
    if ht : 0 < t ∧ t < Fn.modulus then
      let k : Fn := ⟨t, ht.2⟩
      -- Step 1: the ephemeral key pair `(k, R)`, with `R = k G` and `k` from RFC 6979.
      match mul k generator with
      -- `G` has order `n`, so `k G` is never `O` for `k` in `[1, n-1]`.
      | .infinity => signWith d e fuel (nonceReject state)
      | .affine x y =>
        -- Steps 2 and 3: `r = x_R mod n`.
        let r : Fn := Fin.ofNat _ x.val
        -- Step 6: `s = k^(-1) (e + r d_U) mod n`.
        let s := k.inv * (e + r * d)
        -- Steps 3 and 6 return to step 1 when `r = 0` or `s = 0`.
        --
        -- Step 1 then takes the next candidate: RFC 6979 §3.2 step h.3 asks it for `r = 0`.
        --
        -- For `s = 0` the next candidate is EthLib's choice.
        if r = 0 ∨ s = 0 then signWith d e fuel (nonceReject state)
        -- Step 3 lets `r` meet a publicly verifiable criterion: here `x_R = r`.
        --
        -- Recovery with the ids 0 and 1 needs it, and signing fails rather than return to step 1.
        else if Fn.modulus ≤ x.val then .error .unrecoverableNonce
        -- Step 7: output `S = (r, s)`, with the parity of `y_R` to recover `R` from `r`.
        else .ok (r, s, decide (y.val % 2 = 1))
    else signWith d e fuel (nonceReject state)

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
    if isLowS s.val then .ok (r, s, odd) else .ok (r, -s, !odd)

end Ecdsa

end EthLib.Cryptography.Secp256k1

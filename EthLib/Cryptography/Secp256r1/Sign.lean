module

public import EthLib.Cryptography.Secp256r1.Curve
public import EthLib.Cryptography.Rfc6979

/-!
# ECDSA signing over secp256r1

Signing follows SEC 1 v2 §4.1.3, with the deterministic nonce of RFC 6979 §3.2.

One key and one hash therefore give one signature, and no caller chooses the nonce.

RFC 6979 is read with its verified [erratum 3812][eid3812].

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).

[eid3812]: https://www.rfc-editor.org/errata/eid3812
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

namespace Ecdsa

open Point Rfc6979

/--
Steps 1 to 3, 6 and 7 of SEC 1 v2 §4.1.3, over the candidates of the nonce generator.

The result is `none` when every candidate allowed by the fuel is rejected.

The key is secret, and this function makes no constant-time claim.
-/
def signWith (d e : Fn) : (fuel : Nat) → NonceState → Option (Fn × Fn)
  -- EthLib's bound on the candidates: RFC 6979 §3.2 step h loops without one.
  | 0, _ => none
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
      | .affine x _ =>
        -- Steps 2 and 3: `r = x_R mod n`.
        let r : Fn := Fin.ofNat _ x.val
        -- Step 6: `s = k^(-1) (e + r d_U) mod n`.
        let s := k.inv * (e + r * d)
        -- Steps 3 and 6 return to step 1 when `r = 0` or `s = 0`.
        --
        -- Step 1 then takes the next candidate: RFC 6979 §3.2 step h.3 asks it for `r = 0`.
        --
        -- For `s = 0`, erratum 3812 of RFC 6979 adds the same rule to §2.4.
        --
        -- It selects a new `k`, then computes `r` and `s` again.
        if r = 0 ∨ s = 0 then signWith d e fuel (nonceReject state)
        -- Step 7: output `S = (r, s)`.
        else some (r, s)
    else signWith d e fuel (nonceReject state)

/--
The signature `(r, s)` of a 32-byte hash, by SEC 1 v2 §4.1.3 with the nonce of RFC 6979.

The result is `none` for the zero key, or when no candidate nonce is usable.

The key is secret, and this function makes no constant-time claim.
-/
def sign (d : Fn) (hash : Vector UInt8 32) : Option (Fn × Fn) :=
  -- A private key lies in `[1, n-1]`, by SEC 1 v2 §3.2.1 step 1.
  if d = 0 then none
  else
    -- Step 4 is done by the caller: the input is the hash `H`, not the message.
    --
    -- Step 5: `e` is `H` read as a big-endian integer; `E = H` keeps every bit.
    --
    -- With SHA-256 no truncation is needed.
    --
    -- `e` is taken mod `n`, which leaves `s` of step 6 unchanged.
    signWith d (Fin.ofNat _ (Base.bytesToNat hash.toList)) MAX_NONCES
      -- The nonce generator is HMAC-SHA-256, keyed by the private key and the 32-byte hash.
      (nonceSeed Fn.modulus d.val hash)

end Ecdsa

end EthLib.Cryptography.Secp256r1

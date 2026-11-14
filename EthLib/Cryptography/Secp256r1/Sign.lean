module

public import EthLib.Cryptography.Secp256r1.Curve
public import EthLib.Cryptography.Rfc6979

/-!
# ECDSA signing over secp256r1

Signing follows SEC 1 v2 §4.1.3, with the deterministic nonce of RFC 6979 §3.2.

The nonce generator is HMAC-SHA-256, keyed by the private key and the 32-byte hash.

One key and one hash therefore give one signature, and no caller chooses the nonce.

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

namespace Ecdsa

open Point Rfc6979

/--
Steps 1 to 6 of SEC 1 v2 §4.1.3, over the candidates of the nonce generator.

A candidate is rejected when it is not in `[1, n - 1]`, or when `r = 0`, by RFC 6979 §3.2 step h.3.

It is also rejected when `s = 0`, by step 6 of SEC 1 v2 §4.1.3.

The result is `none` when every candidate allowed by the fuel is rejected.

The key is secret, and this function makes no constant-time claim.
-/
def signWith (d e : Fn) : (fuel : Nat) → NonceState → Option (Fn × Fn)
  | 0, _ => none
  | fuel + 1, state =>
    let (t, state) := nonceNext state
    if ht : 0 < t ∧ t < Fn.modulus then
      let k : Fn := ⟨t, ht.2⟩
      match mul k generator with
      | .infinity => signWith d e fuel (nonceReject state)
      | .affine x _ =>
        -- Step 3: `r = x_R mod n`.
        let r : Fn := Fin.ofNat _ x.val
        -- Step 6: `s = k^(-1) (e + r d) mod n`.
        let s := k.inv * (e + r * d)
        if r = 0 ∨ s = 0 then signWith d e fuel (nonceReject state)
        else some (r, s)
    else signWith d e fuel (nonceReject state)

/--
The signature `(r, s)` of a 32-byte hash, by SEC 1 v2 §4.1.3 with the nonce of RFC 6979.

The hash is read as a big-endian integer mod `n`; with SHA-256 no truncation is needed.

The result is `none` for the zero key, or when no candidate nonce is usable.

The key is secret, and this function makes no constant-time claim.
-/
def sign (d : Fn) (hash : Vector UInt8 32) : Option (Fn × Fn) :=
  if d = 0 then none
  else
    -- Step 5: `e` is the hash read as an integer mod `n`.
    signWith d (Fin.ofNat _ (Base.bytesToNat hash.toList)) MAX_NONCES
      (nonceSeed Fn.modulus d.val hash)

end Ecdsa

end EthLib.Cryptography.Secp256r1

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
def signWith (d e : Fn) (fuel : Nat) (state : NonceState) : Option (Fn × Fn) :=
  -- The loop is that of every curve, and the point `R` is not needed here.
  (domain.signWith d e fuel state).map fun (r, s, _) => (r, s)

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
    signWith d (Fin.ofNat _ (Base.ByteOrder.ofBE hash.toList)) MAX_NONCES
      -- The nonce generator is HMAC-SHA-256, keyed by the private key and the 32-byte hash.
      (nonceSeed Fn.modulus d.val hash)

end Ecdsa

end EthLib.Cryptography.Secp256r1

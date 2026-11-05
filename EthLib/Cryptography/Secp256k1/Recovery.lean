module

public import EthLib.Cryptography.Secp256k1.Ecdsa

/-!
# `Secp256k1.Recovery`

Public key recovery, from SEC 1 v2 §4.1.6.

An Ethereum transaction carries a signature, not a public key.

The key is rebuilt from the signature and the hash, then hashed into the sender's address.

The verification equation `R = u1 G + u2 Q` can be solved for `Q`:

```text
s R = e G + r Q, so Q = r^(-1) (s R - e G)
```

`R` is not sent, but its `x` is `r`, so `R` is one of the two points with that `x`.

The recovery id picks one: `0` for an even `y`, `1` for an odd `y`.

That is the recovery identifier of Appendix F of the Yellow Paper, Shanghai version.

The source is `Paper.tex` at `efc5f9a`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>

It declares the ids 2 and 3 invalid.

SEC 1 also tries `x = r + j n` for `j` up to the cofactor `h = 1`, for the rare `x_R >= n`.

Ethereum uses only the ids 0 and 1, so it never tries `x = r + n`, and neither does recovery here.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

/-- The public key whose signature on `hash` is `(r, s)`, by SEC 1 v2 §4.1.6.

The recovery id gives the parity of the `y` of `R`. -/
def recover (hash : Vector UInt8 32) (r s : Nat) (recoveryId : Fin 2) : Except Secp256k1Error Point :=
  -- `r` and `s` lie in `[1, n - 1]`, as verification requires.
  if hr : 0 < r ∧ r < Fn.modulus then
    if hs : 0 < s ∧ s < Fn.modulus then do
      -- Steps 1.1 to 1.3, with `j = 0`: `R` is the point with `x = r`, since `r < n < p`.
      let R ← Point.decompress (Fin.ofNat _ r) (recoveryId == 1)
      -- Step 1.4 asks `n R = O`, which holds for every point: the cofactor is 1.
      -- Steps 1.5 and 1.6.1: `Q = r^(-1) (s R - e G) = (r^(-1) s) R + (-(r^(-1) e)) G`.
      let e : Fn := Fin.ofNat _ (hashToInt hash)
      let rInv := Fn.inv ⟨r, hr.2⟩
      let q := Point.mulAdd (rInv * ⟨s, hs.2⟩) R (-(rInv * e)) .generator
      -- A public key is never `O`.
      if q = .infinity then .error .pointAtInfinity else .ok q
    else .error .scalarOutOfRange
  else .error .scalarOutOfRange

end Ecdsa

end EthLib.Cryptography.Secp256k1

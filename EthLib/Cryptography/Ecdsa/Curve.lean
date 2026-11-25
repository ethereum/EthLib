module

public import EthLib.Cryptography.Rfc6979
public import EthLib.Cryptography.ShortWeierstrass

/-!
# ECDSA over a short Weierstrass curve

Verification from SEC 1 v2 §4.1.4, and the signing loop of §4.1.3 with the nonce of RFC 6979 §3.2.

They are written once, and each curve of cofactor 1 with a base point of prime order is an instance.

The private key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

@[expose] public section

namespace EthLib.Cryptography.Ecdsa

open ShortWeierstrass Rfc6979

/-- A curve over the integers mod `p`, with a base point `G` of prime order `n`, as ECDSA uses it.

The curve has cofactor 1, so every point on it has order dividing `n`.

Each curve gives its own scalar products and its own inverse mod `n`. -/
structure Curve (p n : Nat) where
  /-- The base point `G`. -/
  generator : Point (Fin p)
  /-- The product `k P`. -/
  mul : Fin n → Point (Fin p) → Point (Fin p)
  /-- The sum `k P + l Q`. -/
  mulAdd : Fin n → Point (Fin p) → Fin n → Point (Fin p) → Point (Fin p)
  /-- The inverse mod `n`, and `0` for `0`. -/
  inv : Fin n → Fin n

namespace Curve

variable {p n : Nat} [NeZero p] [NeZero n] [Params (Fin p)] (C : Curve p n)

/-- Whether `(r, s)` is a valid signature on the hash integer `e` under the public key `q`.

It is the verifying operation of SEC 1 v2 §4.1.4.

`e` acts mod `n`, like every scalar. -/
@[inline] def verify (q : Point (Fin p)) (e r s : Nat) : Bool :=
  -- Step 1: if `r` and `s` are not both integers in `[1, n-1]`, output "invalid".
  if hr : 0 < r ∧ r < n then
    if hs : 0 < s ∧ s < n then
      -- Not a step of §4.1.4: steps 1 and 2 of SEC 1 v2 §3.2.2.1, not `O` and on the curve.
      --
      -- The range of the coordinates in step 2 holds by the type, and step 3 is for `F_2^m`.
      --
      -- Its step 4, `n Q = O`, holds for every point of a curve of cofactor 1.
      --
      -- The key `O` would accept any `r` that some `u1 G` hits.
      if q ≠ .infinity ∧ q.isOnCurve then
        -- Steps 2 and 3 are done by the caller, which passes the integer `e` of the hash.
        --
        -- `e` is taken mod `n` here, which leaves `u1` of step 4 unchanged.
        --
        -- Step 4: `u1 = e s^(-1) mod n` and `u2 = r s^(-1) mod n`.
        let sInv := C.inv ⟨s, hs.2⟩
        let u1 := (Fin.ofNat _ e : Fin n) * sInv
        let u2 := (⟨r, hr.2⟩ : Fin n) * sInv
        -- Step 5: `R = (x_R, y_R) = u1 G + u2 Q_U`, and "invalid" if `R = O`.
        --
        -- For a valid signature, `R = s^(-1) (e + r d_U) G = k G`, the signer's point.
        match C.mulAdd u1 C.generator u2 q with
        | .infinity => false
        -- Steps 6 to 8: `v = x_R mod n`, and "valid" exactly when `v = r`.
        --
        -- The signer's `r` is the `x` of `R = k G` mod `n`, for its secret nonce `k`.
        | .affine x _ => x.val % n == r
      else false
    else false
  else false

/--
Steps 1 to 3, 6 and 7 of SEC 1 v2 §4.1.3, over the candidates of the nonce generator.

The nonces are those of RFC 6979 for an order `n` of 256 bits, the case its generator implements.

The result is `(r, s, x_R, y_R)`, or `none` when every candidate allowed by the fuel is rejected.

The key is secret, and this function makes no constant-time claim.
-/
@[specialize] def signWith (d e : Fin n) :
    (fuel : Nat) → NonceState → Option (Fin n × Fin n × Fin p × Fin p)
  -- EthLib's bound on the candidates: RFC 6979 §3.2 step h loops without one.
  | 0, _ => none
  | fuel + 1, state =>
    -- RFC 6979 §3.2 steps h.1 and h.2: `V = HMAC_K(V)`, and `T = V` as it has `qlen` bits.
    --
    -- Step h.3: the candidate `k = bits2int(T)`.
    let (t, state) := nonceNext state
    -- Step h.3 also asks `k` in `[1, q-1]`, or the generator moves on to the next candidate.
    if ht : 0 < t ∧ t < n then
      let k : Fin n := ⟨t, ht.2⟩
      -- Step 1: the ephemeral key pair `(k, R)`, with `R = k G` and `k` from RFC 6979.
      match C.mul k C.generator with
      -- `G` has order `n`, so `k G` is never `O` for `k` in `[1, n-1]`.
      | .infinity => signWith d e fuel (nonceReject state)
      | .affine x y =>
        -- Steps 2 and 3: `r = x_R mod n`.
        let r : Fin n := Fin.ofNat _ x.val
        -- Step 6: `s = k^(-1) (e + r d_U) mod n`.
        let s := C.inv k * (e + r * d)
        -- Steps 3 and 6 return to step 1 when `r = 0` or `s = 0`.
        --
        -- Step 1 then takes the next candidate: RFC 6979 §3.2 step h.3 asks it for `r = 0`.
        --
        -- For `s = 0`, erratum 3812 of RFC 6979 adds the same rule to §2.4.
        --
        -- It selects a new `k`, then computes `r` and `s` again.
        if r = 0 ∨ s = 0 then signWith d e fuel (nonceReject state)
        -- Step 7: output `S = (r, s)`, with the point `R` that a caller may need.
        else some (r, s, x, y)
    else signWith d e fuel (nonceReject state)

end Curve

end EthLib.Cryptography.Ecdsa

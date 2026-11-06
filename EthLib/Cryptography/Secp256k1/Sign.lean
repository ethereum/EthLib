module

public import EthLib.Cryptography.Secp256k1.Ecdsa
public import EthLib.Cryptography.Hash.Hmac

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

open Point Hash.Hmac

/-- An integer as 32 big-endian bytes, `int2octets` of RFC 6979 §2.3.3 with `rlen = 256`. -/
def int2octets (x : Nat) : ByteArray := ⟨(toBytesBE 32 x).toArray⟩

/-- The state `(K, V)` of the nonce generator of RFC 6979 §3.2. -/
structure NonceState where
  /-- The HMAC key `K`. -/
  key : ByteArray
  /-- The value `V`. -/
  value : ByteArray

/--
Steps b to g of RFC 6979 §3.2: the generator seeded with the key `x` and the hash `h1`.

With `qlen = hlen = 256`, `bits2octets(h1)` is `h1 mod n` as 32 bytes.

The key is secret, and this function makes no constant-time claim.
-/
def nonceSeed (x : Fn) (hash : Vector UInt8 32) : NonceState :=
  let material := int2octets x.val ++ int2octets (hashToInt hash % Fn.modulus)
  let v : ByteArray := ⟨Array.replicate 32 0x01⟩
  let k : ByteArray := ⟨Array.replicate 32 0x00⟩
  let k := hmac k (v ++ ⟨#[0x00]⟩ ++ material)
  let v := hmac k v
  let k := hmac k (v ++ ⟨#[0x01]⟩ ++ material)
  let v := hmac k v
  ⟨k, v⟩

/--
Step h.2 of RFC 6979 §3.2: the next `V`, which is the candidate `T`, since `hlen = qlen`.

The candidate is `bits2int(T)`, and the state keeps the new `V`.
-/
def nonceNext (state : NonceState) : Nat × NonceState :=
  let v := hmac state.key state.value
  (Base.bytesToNat v.data.toList, ⟨state.key, v⟩)

/-- Step h.3 of RFC 6979 §3.2 on a rejected candidate: `K = HMAC_K(V | 00)`, `V = HMAC_K(V)`. -/
def nonceReject (state : NonceState) : NonceState :=
  let k := hmac state.key (state.value ++ ⟨#[0x00]⟩)
  ⟨k, hmac k state.value⟩

/-- The bound on the candidates that signing tries before it gives up. -/
def MAX_NONCES : Nat := 16

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

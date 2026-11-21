module

public import EthLib.Cryptography.Hash.Hmac
public import EthLib.Base.BigEndian

/-!
# Deterministic ECDSA nonces

The nonce generator of [RFC 6979 §3.2][rfc6979], with HMAC-SHA-256 and a 256-bit group order.

The private key is secret, and these functions make no constant-time claim.

[rfc6979]: https://www.rfc-editor.org/rfc/rfc6979#section-3.2
-/

@[expose] public section

namespace EthLib.Cryptography.Rfc6979

open Hash.Hmac

/-- An integer as 32 big-endian bytes, `int2octets` of RFC 6979 §2.3.3 with `rlen = 256`. -/
def int2octets (x : Nat) : ByteArray := ⟨(Base.natToBytes 32 x).toArray⟩

/-- The state `(K, V)` of the nonce generator of RFC 6979 §3.2. -/
structure NonceState where
  /-- The HMAC key `K`. -/
  key : ByteArray
  /-- The value `V`. -/
  value : ByteArray

/--
Steps b to g of RFC 6979 §3.2: the generator seeded with the key `x` and the hash `h1`.

The group order is `q`; with `qlen = hlen = 256`, `bits2octets(h1)` is `h1 mod q` as 32 bytes.

The result is that of RFC 6979 only for a 256-bit `q`, which both curves of EthLib have.

It reads only the private key and the message hash, so one pair gives one nonce.

The key is secret, and this function makes no constant-time claim.
-/
def nonceSeed (q x : Nat) (hash : Vector UInt8 32) : NonceState :=
  -- `int2octets(x) || bits2octets(h1)`, shared by steps d and f.
  let material := int2octets x ++ int2octets (Base.bytesToNat hash.toList % q)
  -- Step b: `V = 0x01 0x01 ... 0x01`, 32 bytes.
  let v : ByteArray := ⟨Array.replicate 32 0x01⟩
  -- Step c: `K = 0x00 0x00 ... 0x00`, 32 bytes.
  let k : ByteArray := ⟨Array.replicate 32 0x00⟩
  -- Step d: `K = HMAC_K(V || 0x00 || int2octets(x) || bits2octets(h1))`.
  let k := hmac k (v ++ ⟨#[0x00]⟩ ++ material)
  -- Step e: `V = HMAC_K(V)`.
  let v := hmac k v
  -- Step f: `K = HMAC_K(V || 0x01 || int2octets(x) || bits2octets(h1))`.
  let k := hmac k (v ++ ⟨#[0x01]⟩ ++ material)
  -- Step g: `V = HMAC_K(V)`.
  let v := hmac k v
  ⟨k, v⟩

/--
Step h.2 of RFC 6979 §3.2: the next `V`, which is the candidate `T`, since `hlen = qlen`.

The candidate is `bits2int(T)`, and the state keeps the new `V`.
-/
def nonceNext (state : NonceState) : Nat × NonceState :=
  -- Step h.2: `V = HMAC_K(V)`, and `T = V`, since one output already has `qlen` bits.
  let v := hmac state.key state.value
  -- Step h.3: `k = bits2int(T)`, the big-endian integer of the 32 bytes.
  (Base.bytesToNat v.data.toList, ⟨state.key, v⟩)

/-- Step h.3 of RFC 6979 §3.2 on a rejected candidate: `K = HMAC_K(V | 00)`, `V = HMAC_K(V)`. -/
def nonceReject (state : NonceState) : NonceState :=
  -- `K = HMAC_K(V || 0x00)`.
  let k := hmac state.key (state.value ++ ⟨#[0x00]⟩)
  -- `V = HMAC_K(V)`, with the new `K`.
  ⟨k, hmac k state.value⟩

/-- EthLib's bound on the candidates that signing tries; RFC 6979 §3.2 step h has none.

A definition of the specification must terminate, so the loop of step h takes this bound.

A candidate is rejected with probability about `2^-128` on secp256k1 and `2^-32` on P-256.

So sixteen rejections in a row are never seen, and signing then fails instead of looping. -/
def MAX_NONCES : Nat := 16

end EthLib.Cryptography.Rfc6979

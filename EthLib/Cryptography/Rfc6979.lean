module

public import EthLib.Cryptography.Hash.Hmac
public import EthLib.Base.BigEndian

/-!
# Deterministic ECDSA nonces

The nonce generator of [RFC 6979 §3.2][rfc6979], with HMAC-SHA-256 and a 256-bit group order.

With `qlen = hlen = 256`, each candidate is one HMAC output read as an integer.

The generator reads only the private key and the message hash, so one pair gives one nonce.

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

The key is secret, and this function makes no constant-time claim.
-/
def nonceSeed (q x : Nat) (hash : Vector UInt8 32) : NonceState :=
  let material := int2octets x ++ int2octets (Base.bytesToNat hash.toList % q)
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

end EthLib.Cryptography.Rfc6979

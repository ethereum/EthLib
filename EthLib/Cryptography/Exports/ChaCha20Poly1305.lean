module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.ChaCha20Poly1305

/-!
# Exports: ChaCha20 and Poly1305

The typed adapters reject wrong byte lengths before any cryptographic operation.
-/

public section

namespace EthLib.Cryptography.ChaCha20Poly1305.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- The ChaCha20-Poly1305 key length in bytes, RFC 8439 §2.8. -/
@[export eth_chachapoly_const_key_size]
def keySize (_ : Unit) : UInt64 := 32

/-- The ChaCha20-Poly1305 nonce length in bytes, RFC 8439 §2.8. -/
@[export eth_chachapoly_const_nonce_size]
def nonceSize (_ : Unit) : UInt64 := 12

/-- The Poly1305 tag length in bytes, RFC 8439 §2.8. -/
@[export eth_chachapoly_const_tag_size]
def tagSize (_ : Unit) : UInt64 := 16

/-- The ChaCha20 block length in bytes, RFC 8439 §2.3. -/
@[export eth_chacha20_const_block_size]
def blockSize (_ : Unit) : UInt64 := 64

/-- Map primitive failures to their stable code and constructor name. -/
def cipherResult {α : Type} (r : Except ChaCha20Poly1305Error α) : Result α :=
  r.mapError fun e => (e.code, reprStr e)

/-- The four-word quarter round, RFC 8439 §2.1. -/
@[export eth_chacha20_quarter_round]
def quarterRoundExport (args : PyValue) : Result PyValue :=
  pyExport (fun (a, b, c, d) => pure (quarterRound a b c d)) args

/-- A quarter round on a 64-byte state at four indices, RFC 8439 §2.2. -/
def quarterRoundStateOf (args : Vector UInt8 64 × Nat × Nat × Nat × Nat) :
    Result (Vector UInt8 64) := do
  let (bytes, a, b, c, d) := args
  if ha : a < 16 then
    if hb : b < 16 then
      if hc : c < 16 then
        if hd : d < 16 then
          return serializeState (quarterRoundState (stateOfBytes bytes) ⟨a, ha⟩ ⟨b, hb⟩
            ⟨c, hc⟩ ⟨d, hd⟩)
        else throw (0, "quarter-round index must be below 16")
      else throw (0, "quarter-round index must be below 16")
    else throw (0, "quarter-round index must be below 16")
  else throw (0, "quarter-round index must be below 16")

/-- A quarter round on a 64-byte state at four indices, RFC 8439 §2.2. -/
@[export eth_chacha20_quarter_round_state]
def quarterRoundStateExport (args : PyValue) : Result PyValue :=
  pyExport quarterRoundStateOf args

/-- The 64-byte ChaCha20 block at a 32-bit counter, RFC 8439 §2.3. -/
@[export eth_chacha20_block]
def blockExport (args : PyValue) : Result PyValue :=
  pyExport (fun (key, counter, nonce) => pure (block key counter nonce)) args

/-- ChaCha20 encryption or decryption without counter wrap, RFC 8439 §2.4. -/
@[export eth_chacha20_crypt]
def cryptExport (args : PyValue) : Result PyValue :=
  pyExport (fun (key, counter, nonce, input) => cipherResult (crypt key counter nonce input)) args

/-- Poly1305 with a 32-byte one-time key, RFC 8439 §2.5. -/
@[export eth_poly1305]
def poly1305Export (args : PyValue) : Result PyValue :=
  pyExport (fun (key, message) => pure (poly1305 key message)) args

/-- Derive a Poly1305 key from ChaCha20 block zero, RFC 8439 §2.6. -/
@[export eth_poly1305_key]
def poly1305KeyExport (args : PyValue) : Result PyValue :=
  pyExport (fun (key, nonce) => pure (poly1305Key key nonce)) args

/-- Encrypt and authenticate, returning ciphertext and a separate tag, RFC 8439 §2.8. -/
@[export eth_chacha20_poly1305_encrypt]
def encryptExport (args : PyValue) : Result PyValue :=
  pyExport (fun (key, nonce, aad, plaintext) => cipherResult (encrypt key nonce aad plaintext)) args

/-- Authenticate before returning plaintext, RFC 8439 §2.8. -/
@[export eth_chacha20_poly1305_decrypt]
def decryptExport (args : PyValue) : Result PyValue :=
  pyExport (fun (key, nonce, aad, ciphertext, tag) =>
    cipherResult (decrypt key nonce aad ciphertext tag)) args

end EthLib.Cryptography.ChaCha20Poly1305.Exports

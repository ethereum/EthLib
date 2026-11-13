module

public import EthLib.Networking.Exports.Quic
public import EthLib.Networking.Quic.Protection

/-!
# Exports: QUIC v1 packet protection

Traffic secrets cross the boundary as 32 bytes, and packet numbers as integers below `2^62`.
-/

public section

namespace EthLib.Networking.Quic.ProtectionExports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Cryptography.Hash

/-- Report packet-protection failures with their stable local code. -/
def result {α : Type} (r : Except Protection.Error α) : Result α :=
  r.mapError fun e => (e.code, reprStr e)

/-- Protect a QUIC v1 header and payload using a SHA-256 traffic secret, RFC 9001 §§5.1 to 5.4. -/
@[export eth_quic_protect]
def protectExport (args : PyValue) : Result PyValue :=
  pyExport (fun (suite, secret, number, offset, header, plaintext) => do
    let suite ← Exports.readSuite suite
    let keys ← Tls13.Exports.ofExcept (packetKeys suite (secret : Tls13.Secret))
    if h : number < 2 ^ 62 then
      result (Protection.protect suite keys ⟨number, h⟩ offset header plaintext)
    else result (.error .packetNumber : Except Protection.Error ByteArray)) args

/-- Authenticate one isolated QUIC v1 packet, RFC 9001 §§5.3 to 5.4.

`expected` is zero initially, or one greater than the largest authenticated packet number. -/
@[export eth_quic_unprotect]
def unprotectExport (args : PyValue) : Result PyValue :=
  pyExport (fun (suite, secret, expected, offset, packet) => do
    let suite ← Exports.readSuite suite
    let keys ← Tls13.Exports.ofExcept (packetKeys suite (secret : Tls13.Secret))
    result (Protection.unprotect suite keys expected offset packet)) args

/--
Compute a QUIC v1 Retry tag from the original destination ID and untagged Retry, RFC 9001 §5.8.
-/
@[export eth_quic_retry_tag]
def retryExport (args : PyValue) : Result PyValue :=
  pyExport (fun (originalDcid, retry) => result (Protection.retryTag originalDcid retry)) args

end EthLib.Networking.Quic.ProtectionExports

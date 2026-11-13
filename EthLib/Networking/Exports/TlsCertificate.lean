module

public import EthLib.Base.Exports.PyDerive
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Libp2p.Tls

/-!
# TLS certificate exports

The policy has no default: each caller names its accepted algorithms and unique-ID rule.
-/

public section

namespace EthLib.Networking.Libp2p.Tls.Exports

open EthLib.Exports (Result PyValue pyExport)

derive_py Extension
derive_py_laws Extension
derive_py HostAlgorithm
derive_py_laws HostAlgorithm
derive_py CertificateAlgorithm
derive_py_laws CertificateAlgorithm
derive_py Policy
derive_py_laws Policy

/-- The certificate's signed bytes, SPKI, validity and extensions.

Then its signature algorithm, signature and the two unique-ID flags.

A validity endpoint is a sign flag and its absolute seconds from the Unix epoch. -/
@[export eth_tls_certificate_read]
def readExport (args : PyValue) : Result PyValue :=
  pyExport (fun (bytes : ByteArray) => do
    let certificate ← (readCertificate bytes).mapError
      fun (e : TlsCertError) => (e.code, s!"TLS certificate rejected: {reprStr e}")
    return (certificate.tbs, certificate.spki,
      (decide (certificate.notBefore < 0), certificate.notBefore.natAbs),
      (decide (certificate.notAfter < 0), certificate.notAfter.natAbs), certificate.extensions,
      certificate.signatureAlgorithm, certificate.signature,
      certificate.issuerUniqueId, certificate.subjectUniqueId)) args

/-- The authenticated peer ID of a chain of exactly one certificate.

The policy names the accepted host and certificate algorithms and the unique-ID rule.

The implemented backends are secp256k1 and P-256 host keys, with P-256/SHA-256 self-signatures. -/
@[export eth_tls_certificate_authenticate]
def authenticateExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((policy, now, chain) : Policy × Nat × List ByteArray) => do
    let peer ← (Tls.authenticate policy now chain).mapError
      fun (e : TlsCertError) => (e.code, s!"TLS certificate rejected: {reprStr e}")
    return peer.peerId) args

/-- The peer ID of one authenticated certificate, checked against the intended peer ID. -/
@[export eth_tls_certificate_authenticate_peer]
def authenticatePeerExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((policy, now, expected, chain) : Policy × Nat × ByteArray × List ByteArray) => do
    let peer ← (Tls.authenticatePeer policy now expected chain).mapError
      fun (e : TlsCertError) => (e.code, s!"TLS certificate rejected: {reprStr e}")
    return peer.peerId) args

/-- Verify DER ECDSA/SHA-256 under an uncompressed P-256 SubjectPublicKeyInfo. -/
@[export eth_tls_certificate_verify_p256]
def verifyP256Export (args : PyValue) : Result PyValue :=
  pyExport (fun ((spki, message, signature) : ByteArray × ByteArray × ByteArray) =>
    (.ok (verifyP256 spki message signature) : Except (UInt32 × String) Bool)) args

end EthLib.Networking.Libp2p.Tls.Exports

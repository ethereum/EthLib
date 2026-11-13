module

public import EthLib.Networking.Libp2p.Tls
public import EthLib.Base.Except

/-!
# Certificate authentication checks

These theorems describe the concrete checks that a successful authentication passes.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.Tls

open EthLib.Networking.Libp2p.Tls
open EthLib.Base

/-- A certificate chain with two or more entries is rejected. -/
theorem authenticate_single (policy : Policy) (now : Nat) (first second : ByteArray)
    (rest : List ByteArray) : authenticate policy now (first :: second :: rest) = .error .chain :=
  rfl

/-- An empty certificate chain is rejected. -/
theorem authenticate_empty (policy : Policy) (now : Nat) :
    authenticate policy now [] = .error .chain := rfl

/-- Success requires exactly one parsed certificate and successful checks on that certificate. -/
theorem authenticate_ok_iff {policy : Policy} {now : Nat} {chain : List ByteArray}
    {peer : AuthenticatedPeer} : authenticate policy now chain = .ok peer ↔
    ∃ bytes certificate, chain = [bytes] ∧ readCertificate bytes = .ok certificate ∧
      authenticateCertificate policy now certificate = .ok peer := by
  cases chain with
  | nil => simp [authenticate]
  | cons first rest =>
    cases rest with
    | nil => simp [authenticate, bind_ok_iff]
    | cons second tail => simp [authenticate]

/-- Success gives the exact validity, algorithm, self-signature and identity checks. -/
theorem authenticateCertificate_ok_iff {policy : Policy} {now : Nat}
    {certificate : Certificate} {peer : AuthenticatedPeer} :
    authenticateCertificate policy now certificate = .ok peer ↔
    certificate.notBefore ≤ Int.ofNat now ∧ Int.ofNat now ≤ certificate.notAfter ∧
    (policy.rejectUniqueIds = false ∨
      (certificate.issuerUniqueId = false ∧ certificate.subjectUniqueId = false)) ∧
    (.p256Sha256 ∈ policy.certificateAlgorithms ∧
      certificate.signatureAlgorithm = ecdsaSha256Oid ∧
      certificate.signatureParameters.isEmpty = true) ∧
    verifyP256 certificate.spki certificate.tbs certificate.signature = true ∧
    ∃ key signature id, signedKey certificate = .ok (key, signature) ∧
      authenticateHost policy certificate.spki key signature = .ok id ∧
      ⟨id, certificate⟩ = peer := by
  simp [authenticateCertificate, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    and_assoc]

/-- Authentication returns the identity checked against the exact parsed certificate key. -/
theorem authenticate_peerId {policy : Policy} {now : Nat} {chain : List ByteArray}
    {peer : AuthenticatedPeer} (success : authenticate policy now chain = .ok peer) :
    ∃ bytes certificate key signature,
      chain = [bytes] ∧ readCertificate bytes = .ok certificate ∧
      peer.certificate = certificate ∧ signedKey certificate = .ok (key, signature) ∧
      authenticateHost policy certificate.spki key signature = .ok peer.peerId := by
  obtain ⟨bytes, certificate, singleton, parsed, checked⟩ := authenticate_ok_iff.mp success
  obtain ⟨_, _, _, _, _, key, signature, id, extension, identity, same⟩ :=
    authenticateCertificate_ok_iff.mp checked
  subst peer
  exact ⟨bytes, certificate, key, signature, singleton, parsed, rfl, extension, identity⟩

/-- A time outside the certificate's closed validity interval is rejected. -/
theorem authenticate_validity (policy : Policy) (now : Nat) (certificate : Certificate)
    (outside : Int.ofNat now < certificate.notBefore ∨ certificate.notAfter < Int.ofNat now) :
    authenticateCertificate policy now certificate = .error .validity := by
  have invalid : ¬(certificate.notBefore ≤ (now : Int) ∧
      (now : Int) ≤ certificate.notAfter) := by
    simp only [Int.ofNat_eq_natCast] at outside
    omega
  simp [authenticateCertificate, ensure, invalid, bind, Except.bind]

/-- A successful dialler authenticates exactly the peer ID it expected. -/
theorem authenticatePeer_peerId {policy : Policy} {now : Nat} {expected : ByteArray}
    {chain : List ByteArray} {peer : AuthenticatedPeer}
    (success : authenticatePeer policy now expected chain = .ok peer) :
    peer.peerId = expected := by
  simp only [authenticatePeer, bind_ok_iff, ensure_ok_iff] at success
  obtain ⟨remote, _, checked⟩ := success
  simp only [pure, Except.pure, Except.ok.injEq] at checked
  obtain ⟨_, sameId, samePeer⟩ := checked
  subst peer
  exact sameId

/-- A certificate without the extension cannot yield a signed host key. -/
theorem authenticate_extension (certificate : Certificate)
    (missing : certificate.extensions.filter (fun ext => ext.oid == libp2pOid) = []) :
    signedKey certificate ≠ .ok pair := by
  intro h
  unfold signedKey at h
  cases hc : certificate.extensions.all (fun ext => !ext.critical || ext.oid == libp2pOid) <;>
    simp [hc, ensure, missing, bind, Except.bind] at h

/-- Successful host authentication in the secp256k1 branch returns its point's peer ID.

The host signature verifies over the certificate's exact encoded SPKI. -/
theorem authenticateHost_secp256k1 {policy : Policy} {spki signature : ByteArray}
    {rest : List UInt8} {id : ByteArray}
    (success : authenticateHost policy spki ⟨(8 :: 2 :: rest).toArray⟩ signature = .ok id) :
    ∃ point, Libp2p.decodePublicKey ⟨(8 :: 2 :: rest).toArray⟩ = .ok point ∧
      Libp2p.verify ⟨(8 :: 2 :: rest).toArray⟩ (hostMessage spki) signature = true ∧
      id = Libp2p.peerId point := by
  simp only [authenticateHost, bind_ok_iff, ensure_ok_iff] at success
  obtain ⟨_, _, point, decoded, _, verified, sameId⟩ := success
  refine ⟨point, ?_, verified, ?_⟩
  · cases hd : Libp2p.decodePublicKey ⟨(8 :: 2 :: rest).toArray⟩ <;>
      simp [hd, Except.mapError] at decoded
    subst point
    rfl
  · simpa [pure, Except.pure] using sameId.symm

end EthLib.Networking.Proofs.Libp2p.Tls

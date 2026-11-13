module

public import EthLib.Networking.Libp2p.Tls
public import EthLib.Networking.Proofs.Libp2p.PeerId
public import EthLib.Base.Except

/-!
# Certificate authentication checks

These theorems describe the concrete checks that a successful authentication passes.

- A chain of any length other than one is rejected.
- A certificate outside its validity interval is rejected.
- A certificate without the libp2p extension, or with another critical extension, is rejected.
- The returned peer ID is that of the host key whose signature verifies over the certificate key.
- A dialer that succeeds gets the peer ID it expected.
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

/-- Authentication succeeds exactly when every check passes.

The checks are validity, unique identifiers, algorithm, self-signature and host key. -/
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

/-- A time outside the certificate's closed validity interval fails the certificate checks. -/
theorem authenticateCertificate_validity (policy : Policy) (now : Nat) (certificate : Certificate)
    (outside : Int.ofNat now < certificate.notBefore ∨ certificate.notAfter < Int.ofNat now) :
    authenticateCertificate policy now certificate = .error .validity := by
  have invalid : ¬(certificate.notBefore ≤ (now : Int) ∧
      (now : Int) ≤ certificate.notAfter) := by
    simp only [Int.ofNat_eq_natCast] at outside
    omega
  simp [authenticateCertificate, ensure, invalid, bind, Except.bind]

/-- A certificate read at a time outside its closed validity interval is rejected. -/
theorem authenticate_validity (policy : Policy) (now : Nat) (bytes : ByteArray)
    (certificate : Certificate) (parsed : readCertificate bytes = .ok certificate)
    (outside : Int.ofNat now < certificate.notBefore ∨ certificate.notAfter < Int.ofNat now) :
    authenticate policy now [bytes] = .error .validity := by
  simp [authenticate, parsed, bind, Except.bind,
    authenticateCertificate_validity policy now certificate outside]

/-- A certificate without the libp2p extension yields no signed host key. -/
theorem signedKey_missing {pair : ByteArray × ByteArray} (certificate : Certificate)
    (missing : certificate.extensions.filter (fun ext => ext.oid == libp2pOid) = []) :
    signedKey certificate ≠ .ok pair := by
  intro h
  unfold signedKey at h
  cases hc : certificate.extensions.all (fun ext => !ext.critical || ext.oid == libp2pOid) <;>
    simp [hc, ensure, missing, bind, Except.bind] at h

/-- A critical extension other than the libp2p one is rejected. -/
theorem signedKey_critical (certificate : Certificate) (ext : Extension)
    (mem : ext ∈ certificate.extensions) (critical : ext.critical = true)
    (other : (ext.oid == libp2pOid) = false) :
    signedKey certificate = .error .criticalExtension := by
  have unknown :
      certificate.extensions.all (fun ext => !ext.critical || ext.oid == libp2pOid) = false := by
    rw [Bool.eq_false_iff]
    intro h
    have := List.all_eq_true.mp h ext mem
    simp [critical, other] at this
  simp [signedKey, ensure, unknown, bind, Except.bind]

/-- A certificate without the libp2p extension is rejected. -/
theorem authenticate_extension {policy : Policy} {now : Nat} {bytes : ByteArray}
    {certificate : Certificate} {peer : AuthenticatedPeer}
    (parsed : readCertificate bytes = .ok certificate)
    (missing : certificate.extensions.filter (fun ext => ext.oid == libp2pOid) = []) :
    authenticate policy now [bytes] ≠ .ok peer := by
  intro h
  obtain ⟨b, c, hc, hp, hok⟩ := authenticate_ok_iff.mp h
  simp only [List.cons.injEq, and_true] at hc
  subst hc
  rw [parsed] at hp
  cases hp
  obtain ⟨_, _, _, _, _, _, _, _, hs, _⟩ := authenticateCertificate_ok_iff.mp hok
  exact signedKey_missing _ missing hs

/-- A certificate with a critical extension other than the libp2p one is rejected. -/
theorem authenticate_critical {policy : Policy} {now : Nat} {bytes : ByteArray}
    {certificate : Certificate} {peer : AuthenticatedPeer}
    (parsed : readCertificate bytes = .ok certificate) (ext : Extension)
    (mem : ext ∈ certificate.extensions) (critical : ext.critical = true)
    (other : (ext.oid == libp2pOid) = false) :
    authenticate policy now [bytes] ≠ .ok peer := by
  intro h
  obtain ⟨b, c, hc, hp, hok⟩ := authenticate_ok_iff.mp h
  simp only [List.cons.injEq, and_true] at hc
  subst hc
  rw [parsed] at hp
  cases hp
  obtain ⟨_, _, _, _, _, _, _, _, hs, _⟩ := authenticateCertificate_ok_iff.mp hok
  rw [signedKey_critical _ ext mem critical other] at hs
  cases hs

/-- A successful host check returns the peer ID of a host key that signed the certificate key.

A secp256k1 key gives the identity peer ID of its point.

A P-256 key gives the SHA-256 peer ID of its protobuf.

Either way the host signature verifies over the handshake prefix and the certificate's SPKI. -/
theorem authenticateHost_ok {policy : Policy} {spki key signature id : ByteArray}
    (success : authenticateHost policy spki key signature = .ok id) :
    (.secp256k1 ∈ policy.hostAlgorithms ∧ ∃ point, key = Libp2p.encodePublicKey point ∧
      Libp2p.verify key (hostMessage spki) signature = true ∧ id = Libp2p.peerId point) ∨
    (.p256 ∈ policy.hostAlgorithms ∧ ∃ hostSpki, key = ⟨#[8, 3, 18, 91]⟩ ++ hostSpki ∧
      verifyP256 hostSpki (hostMessage spki) signature = true ∧
      id = ⟨#[0x12, 0x20]⟩ ++ EthLib.Cryptography.Hash.Sha256.hash key) := by
  unfold authenticateHost at success
  split at success
  · simp only [bind_ok_iff, ensure_ok_iff] at success
    obtain ⟨_, allowed, point, decoded, _, verified, same⟩ := success
    refine .inl ⟨allowed, point, ?_, verified, ?_⟩
    · cases hd : Libp2p.decodePublicKey key <;> simp [hd, Except.mapError] at decoded
      subst point
      exact (PeerId.encodePublicKey_of_decodePublicKey hd).symm
    · simpa [pure, Except.pure] using same.symm
  · rename_i bytes heq
    simp only [bind_ok_iff, ensure_ok_iff] at success
    obtain ⟨_, allowed, _, _, _, _, _, verified, same⟩ := success
    refine .inr ⟨allowed, ⟨bytes.toArray⟩, ?_, verified, ?_⟩
    · cases key with
      | mk data =>
        have hdata : data = (8 :: 3 :: 18 :: 91 :: bytes).toArray := by
          rw [← heq]
        subst hdata
        rfl
    · simpa [pure, Except.pure] using same.symm
  all_goals simp [throw, throwThe, MonadExceptOf.throw] at success

/-- Authentication returns the peer ID of the host key in the certificate's libp2p extension.

That host key signed the handshake prefix and the certificate's exact encoded SPKI. -/
theorem authenticate_peerId {policy : Policy} {now : Nat} {chain : List ByteArray}
    {peer : AuthenticatedPeer} (success : authenticate policy now chain = .ok peer) :
    ∃ bytes key signature,
      chain = [bytes] ∧ readCertificate bytes = .ok peer.certificate ∧
      signedKey peer.certificate = .ok (key, signature) ∧
      ((.secp256k1 ∈ policy.hostAlgorithms ∧ ∃ point, key = Libp2p.encodePublicKey point ∧
        Libp2p.verify key (hostMessage peer.certificate.spki) signature = true ∧
        peer.peerId = Libp2p.peerId point) ∨
      (.p256 ∈ policy.hostAlgorithms ∧ ∃ hostSpki, key = ⟨#[8, 3, 18, 91]⟩ ++ hostSpki ∧
        verifyP256 hostSpki (hostMessage peer.certificate.spki) signature = true ∧
        peer.peerId = ⟨#[0x12, 0x20]⟩ ++ EthLib.Cryptography.Hash.Sha256.hash key)) := by
  obtain ⟨bytes, certificate, singleton, parsed, checked⟩ := authenticate_ok_iff.mp success
  obtain ⟨_, _, _, _, _, key, signature, id, extension, identity, same⟩ :=
    authenticateCertificate_ok_iff.mp checked
  subst peer
  exact ⟨bytes, key, signature, singleton, parsed, extension, authenticateHost_ok identity⟩

/-- A successful dialer authenticates exactly the peer ID it expected. -/
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

end EthLib.Networking.Proofs.Libp2p.Tls

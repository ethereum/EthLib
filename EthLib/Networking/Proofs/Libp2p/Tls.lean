module

public import EthLib.Base.Proofs.Except
public import EthLib.Networking.Libp2p.Tls
public import EthLib.Networking.Proofs.Libp2p.PeerId
public import EthLib.Serialization.Proofs.Der
import EthLib.Cryptography.Proofs.Secp256r1.Encoding
public import EthLib.Base.Except

/-!
# Certificate authentication checks

These theorems describe the checks that a successful libp2p TLS authentication passes.

They also describe the readers of certificate times, validity, extensions and P-256 keys.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.Tls

open EthLib.Networking.Libp2p.Tls
open EthLib.Base
open EthLib.Serialization

/-- A certificate chain with two or more entries is rejected. -/
theorem authenticate_single (policy : Policy) (now : Nat) (first second : ByteArray)
    (rest : List ByteArray) :
    authenticate policy now (first :: second :: rest) = .error (.chain (rest.length + 2)) :=
  rfl

/-- An empty certificate chain is rejected. -/
theorem authenticate_empty (policy : Policy) (now : Nat) :
    authenticate policy now [] = .error (.chain 0) := rfl

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
    authenticateCertificate policy now certificate =
      .error (.validity now certificate.notBefore certificate.notAfter) := by
  have invalid : ¬(certificate.notBefore ≤ (now : Int) ∧
      (now : Int) ≤ certificate.notAfter) := by
    simp only [Int.ofNat_eq_natCast] at outside
    omega
  simp [authenticateCertificate, ensure, invalid, bind, Except.bind]

/-- A certificate read at a time outside its closed validity interval is rejected. -/
theorem authenticate_validity (policy : Policy) (now : Nat) (bytes : ByteArray)
    (certificate : Certificate) (parsed : readCertificate bytes = .ok certificate)
    (outside : Int.ofNat now < certificate.notBefore ∨ certificate.notAfter < Int.ofNat now) :
    authenticate policy now [bytes] =
      .error (.validity now certificate.notBefore certificate.notAfter) := by
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
    signedKey certificate = .error (.criticalExtension (criticalOid certificate.extensions)) := by
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

/-- The `width` ASCII decimal digits of `n`, most significant first. -/
def decimalBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, n => decimalBytes width (n / 10) ++ [UInt8.ofNat (48 + n % 10)]

/-- The decimal digits of a number at a given width are that many bytes. -/
theorem decimalBytes_length (width n : Nat) : (decimalBytes width n).length = width := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih => simp [decimalBytes, ih]

/-- A byte string reads as `n` exactly when it is the digits of `n` at its length.

The number `n` then fits in those digits. -/
theorem decimal_eq_ok_iff {bytes : List UInt8} {n : Nat} :
    decimal bytes = .ok n ↔ bytes = decimalBytes bytes.length n ∧ n < 10 ^ bytes.length := by
  obtain ⟨r, rfl⟩ : ∃ r, bytes = r.reverse := ⟨bytes.reverse, by simp⟩
  induction r generalizing n with
  | nil =>
    simp only [decimal, List.reverse_nil, List.foldlM_nil, pure, Except.pure, Except.ok.injEq,
      List.length_nil, decimalBytes, Nat.pow_zero, true_and]
    omega
  | cons b r ih =>
    simp only [List.reverse_cons]
    generalize r.reverse = l at ih ⊢
    simp only [decimal, List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_ok_iff,
      ensure_ok_iff, pure, Except.pure, Except.ok.injEq] at ih ⊢
    simp only [List.length_append, List.length_singleton, decimalBytes]
    constructor
    · rintro ⟨k, hk, m, ⟨_, ⟨hb1, hb2⟩, rfl⟩, rfl⟩
      obtain ⟨hl, hlt⟩ := ih.mp hk
      have hq : (k * 10 + (b.toNat - 48)) / 10 = k := by omega
      have hr : (k * 10 + (b.toNat - 48)) % 10 = b.toNat - 48 := by omega
      refine ⟨?_, ?_⟩
      · rw [hq, hr, ← hl]
        congr
        apply UInt8.toNat_inj.mp
        have : (UInt8.ofNat (48 + (b.toNat - 48))).toNat = (48 + (b.toNat - 48)) % 256 := by
          simp
        omega
      · rw [Nat.pow_succ]
        omega
    · rintro ⟨he, hlt⟩
      obtain ⟨hl, hbe⟩ := List.append_inj he (by simp [decimalBytes_length])
      simp only [List.cons.injEq, and_true] at hbe
      have hlt' : n / 10 < 10 ^ l.length := by
        rw [Nat.pow_succ] at hlt
        omega
      have hbn : b.toNat = 48 + n % 10 := by
        have : (UInt8.ofNat (48 + n % 10)).toNat = (48 + n % 10) % 256 := by simp
        rw [hbe]
        omega
      exact ⟨n / 10, ih.mpr ⟨hl, hlt'⟩, n, ⟨(), ⟨by omega, by omega⟩, by omega⟩, rfl⟩

/-- The number of days of a year of the proleptic Gregorian calendar. -/
def daysInYear (year : Nat) : Nat :=
  if year % 4 = 0 ∧ (year % 100 ≠ 0 ∨ year % 400 = 0) then 366 else 365

/-- The lengths of the twelve months of a year, from January. -/
def monthLengths (year : Nat) : List Nat :=
  [31, if daysInYear year = 366 then 29 else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]

/-- The number of days from 1970-01-01 to January 1 of a year, negative before 1970. -/
def yearStart (year : Nat) : Int :=
  if 1970 ≤ year then ((List.range (year - 1970)).map (fun i => (daysInYear (1970 + i) : Int))).sum
  else -((List.range (1970 - year)).map (fun i => (daysInYear (year + i) : Int))).sum

/-- January 1 of the next year comes one year length later. -/
private theorem yearStart_succ (year : Nat) :
    yearStart (year + 1) = yearStart year + daysInYear year := by
  unfold yearStart
  by_cases h : 1970 ≤ year
  · simp only [show 1970 ≤ year + 1 by omega, h, ↓reduceIte]
    rw [show year + 1 - 1970 = (year - 1970) + 1 by omega,
      List.range_succ, List.map_append, List.sum_append]
    simp [show 1970 + (year - 1970) = year by omega]
  · simp only [h, ↓reduceIte]
    rw [show 1970 - year = (1970 - (year + 1)) + 1 by omega, List.range_succ_eq_map,
      List.map_cons, List.sum_cons, List.map_map]
    by_cases h' : 1970 ≤ year + 1
    · simp only [h', ↓reduceIte]
      rw [show year + 1 - 1970 = 0 by omega,
        show 1970 - (year + 1) = 0 by omega]
      simp only [List.range_zero, List.map_nil, List.sum_nil, Nat.add_zero]
      omega
    · simp only [h', ↓reduceIte]
      have hf : ((fun i => (daysInYear (year + i) : Int)) ∘ Nat.succ) =
          fun i => (daysInYear (year + 1 + i) : Int) := by
        funext i
        simp [Nat.add_assoc, Nat.add_comm 1 i]
      simp only [hf, Nat.add_zero]
      omega

/-- The closed form of the days in years 1 to `x` grows by the length of year `x + 1`. -/
private theorem daysBefore_succ (x : Nat) :
    365 * (x + 1) + (x + 1) / 4 - (x + 1) / 100 + (x + 1) / 400 =
      365 * x + x / 4 - x / 100 + x / 400 + daysInYear (x + 1) := by
  simp only [Nat.succ_div, Nat.dvd_iff_mod_eq_zero]
  have a : x / 100 ≤ x / 4 := Nat.div_le_div_left (by omega) (by omega)
  unfold daysInYear
  generalize x / 4 = p at *
  generalize x / 100 = q at *
  generalize x / 400 = r at *
  split <;> split <;> split <;> split <;> omega

/-- January 1 of year `x + 1` is the closed form of the days before it, less those before 1970. -/
private theorem yearStart_eq (x : Nat) :
    yearStart (x + 1) = ((365 * x + x / 4 - x / 100 + x / 400 : Nat) : Int) - 719162 := by
  -- The difference of the two sides does not change from one year to the next.
  have same : ∀ x, yearStart (x + 1) - ((365 * x + x / 4 - x / 100 + x / 400 : Nat) : Int) =
      yearStart 1 := by
    intro x
    induction x with
    | zero => simp
    | succ x ih =>
      rw [yearStart_succ (x + 1), daysBefore_succ, Int.natCast_add, ← ih]
      omega
  -- In 1970 both sides are zero.
  have epoch : yearStart (1969 + 1) = 0 := by simp [yearStart]
  have := same 1969
  rw [epoch] at this
  have := same x
  omega

/-- The bytes of a certificate time after its year.

They are two decimal digits each of month, day, hour, minute and second, then `Z` (byte 90). -/
def timeBytes (month day hour minute second : Nat) : List UInt8 :=
  decimalBytes 2 month ++ decimalBytes 2 day ++ decimalBytes 2 hour ++ decimalBytes 2 minute ++
    decimalBytes 2 second ++ [90]

/-- The number of days from 1970-01-01 to a date, negative before it. -/
def dayNumber (year month day : Nat) : Int :=
  yearStart year + (((monthLengths year).take (month - 1)).sum : Int) + day - 1

/-- The fields of a time read as numbers exactly when the bytes are their digits and `Z`.

Each number then fits in its digits. -/
private theorem timeFields_iff {width : Nat} {bytes : List UInt8}
    (length : bytes.length = width + 11)
    {raw month day hour minute second : Nat} :
    (bytes.getLast? = some 90 ∧ decimal (bytes.take width) = .ok raw ∧
      decimal ((bytes.drop width).take 2) = .ok month ∧
      decimal (((bytes.drop width).drop 2).take 2) = .ok day ∧
      decimal (((bytes.drop width).drop 4).take 2) = .ok hour ∧
      decimal (((bytes.drop width).drop 6).take 2) = .ok minute ∧
      decimal (((bytes.drop width).drop 8).take 2) = .ok second) ↔
    bytes = decimalBytes width raw ++ timeBytes month day hour minute second ∧ raw < 10 ^ width ∧
      month < 100 ∧ day < 100 ∧ hour < 100 ∧ minute < 100 ∧ second < 100 := by
  obtain ⟨A, R, rfl, hA, hR⟩ : ∃ A R, bytes = A ++ R ∧ A.length = width ∧ R.length = 11 :=
    ⟨bytes.take width, bytes.drop width, (List.take_append_drop _ _).symm,
      by simp [length], by simp [length]⟩
  have hd : (A ++ R).drop width = R := by simp [← hA]
  have ht : (A ++ R).take width = A := by simp [← hA]
  have split : A ++ R = decimalBytes width raw ++ timeBytes month day hour minute second ↔
      A = decimalBytes width raw ∧ R = timeBytes month day hour minute second :=
    ⟨fun h => List.append_inj h (by simp [hA, decimalBytes_length]),
      fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  rw [hd, ht, split, decimal_eq_ok_iff, hA]
  match R, hR with
  | [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10], _ =>
    simp only [decimal_eq_ok_iff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
      List.take_zero, List.length_cons, List.length_nil, List.getLast?_append, timeBytes,
      decimalBytes, List.nil_append, List.cons_append, List.cons.injEq, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.some_or, Option.some.injEq, and_true, Nat.zero_add,
      show 10 ^ (1 + 1) = 100 from rfl]
    constructor
    · rintro ⟨h10, ⟨hA, hraw⟩, ⟨⟨h0, h1⟩, hm⟩, ⟨⟨h2, h3⟩, hd⟩, ⟨⟨h4, h5⟩, hh⟩, ⟨⟨h6, h7⟩, hi⟩,
        ⟨h8, h9⟩, hs⟩
      exact ⟨⟨hA, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hraw, hm, hd, hh, hi, hs⟩
    · rintro ⟨⟨hA, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hraw, hm, hd, hh, hi, hs⟩
      exact ⟨h10, ⟨hA, hraw⟩, ⟨⟨h0, h1⟩, hm⟩, ⟨⟨h2, h3⟩, hd⟩, ⟨⟨h4, h5⟩, hh⟩, ⟨⟨h6, h7⟩, hi⟩,
        ⟨h8, h9⟩, hs⟩

/-- The leap-year rule of the time reader gives exactly the years of 366 days. -/
private theorem leapYear_iff (year : Nat) : leapYear year = true ↔ daysInYear year = 366 := by
  unfold leapYear daysInYear
  split <;> simp_all

/-- For a month from 1 to 12, the reader's month length is its entry in the year's list.

The lengths of the earlier months also sum to the same total. -/
private theorem monthDays_eq {year month : Nat} (low : 1 ≤ month) (high : month ≤ 12) :
    monthDays year month = (monthLengths year).getD (month - 1) 0 ∧
      ((List.range (month - 1)).map (fun m => monthDays year (m + 1))).sum =
        ((monthLengths year).take (month - 1)).sum := by
  have leap := leapYear_iff year
  rcases (by omega : month = 1 ∨ month = 2 ∨ month = 3 ∨ month = 4 ∨ month = 5 ∨ month = 6 ∨
    month = 7 ∨ month = 8 ∨ month = 9 ∨ month = 10 ∨ month = 11 ∨ month = 12) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals by_cases hy : daysInYear year = 366 <;>
    simp [monthDays, monthLengths, List.range_succ, hy, leap]

/-- The reader's closed form is 86400 seconds per day of the model, plus the time of day. -/
private theorem timeSeconds_eq {year month day hour minute second : Nat} (positive : 0 < year)
    (low : 1 ≤ month) (high : month ≤ 12) (first : 1 ≤ day) :
    (Int.ofNat (365 * (year - 1) + (year - 1) / 4 - (year - 1) / 100 + (year - 1) / 400 +
      ((List.range (month - 1)).map (fun m => monthDays year (m + 1))).sum + day - 1) - 719162) *
        86400 + Int.ofNat (hour * 3600 + minute * 60 + second) =
      86400 * dayNumber year month day + 3600 * hour + 60 * minute + second := by
  obtain ⟨x, rfl⟩ : ∃ x, year = x + 1 := ⟨year - 1, by omega⟩
  rw [(monthDays_eq low high).2]
  unfold dayNumber
  rw [yearStart_eq, Nat.add_sub_cancel]
  simp only [Int.ofNat_eq_natCast]
  generalize 365 * x + x / 4 - x / 100 + x / 400 = A
  generalize ((monthLengths (x + 1)).take (month - 1)).sum = M
  omega

/-- No month of the time reader is longer than 31 days. -/
private theorem monthDays_le (year month : Nat) : monthDays year month ≤ 31 := by
  unfold monthDays
  split
  · split <;> omega
  · split <;> omega

/-- A certificate time reads as `t` exactly when it writes a valid date and time in a fixed form.

The forms are those of [RFC 5280 §4.1.2.5](https://www.rfc-editor.org/rfc/rfc5280#section-4.1.2.5).

The reader takes seconds below 60, so no leap second, which RFC 5280 leaves open.

It also takes a GeneralizedTime before 2050, which issuers must write as UTCTime. -/
theorem readTime_eq_ok_iff {value : Der.Value} {t : Int} :
    readTime value = .ok t ↔ ∃ year month day hour minute second,
      -- Both forms end in `Z` (byte 90).
      --
      -- A UTCTime (tag 23) writes a year from 1950 to 2049 as its last two digits.
      ((value.tag = 0x17 ∧ 1950 ≤ year ∧ year < 2050 ∧ value.content.data.toList =
          decimalBytes 2 (year % 100) ++ timeBytes month day hour minute second) ∨
        -- A GeneralizedTime (tag 24) writes a year from 1 to 9999 as four digits.
        (value.tag = 0x18 ∧ 0 < year ∧ year < 10000 ∧ value.content.data.toList =
          decimalBytes 4 year ++ timeBytes month day hour minute second)) ∧
      1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧ day ≤ (monthLengths year).getD (month - 1) 0 ∧
      hour < 24 ∧ minute < 60 ∧ second < 60 ∧
      -- `t` counts 86400 seconds for each day from 1970-01-01, negative before it, plus the time.
      --
      -- Its days are those of the proleptic Gregorian calendar, before 1970 too.
      t = 86400 * dayNumber year month day + 3600 * hour + 60 * minute + second := by
  by_cases h17 : value.tag = 0x17
  · simp only [readTime, h17, bind_ok_iff, ensure_ok_iff, pure, Except.pure, Except.ok.injEq,
      ↓reduceIte, exists_eq_left', exists_const, true_and,
      show ((23 : UInt8) = 24) = False by decide,
      false_and, or_false]
    constructor
    · rintro ⟨⟨hlen, hlast⟩, raw, hraw, -, month, hm, day, hd, hour, hh, minute, hi, second, hs,
        ⟨m1, m12, d1, dle, h24, i60, s60⟩, rfl⟩
      obtain ⟨hbytes, hlt, -⟩ := (timeFields_iff hlen).mp ⟨hlast, hraw, hm, hd, hh, hi, hs⟩
      have hy : (if raw < 50 then 2000 + raw else 1900 + raw) % 100 = raw := by
        split <;> omega
      refine ⟨if raw < 50 then 2000 + raw else 1900 + raw, month, day, hour, minute, second,
        ⟨?_, ?_, ?_⟩, m1, m12, d1, ?_, h24, i60, s60,
        timeSeconds_eq (year := if raw < 50 then 2000 + raw else 1900 + raw) (by split <;> omega)
          m1 m12 d1⟩
      · split <;> omega
      · split <;> omega
      · rw [hy]
        exact hbytes
      · rw [← (monthDays_eq m1 m12).1]
        exact dle
    · rintro ⟨year, month, day, hour, minute, second, ⟨lo, hi, hbytes⟩, m1, m12, d1, dle, h24, i60,
        s60, rfl⟩
      have hlen : value.content.data.toList.length = 2 + 11 := by
        simp [hbytes, timeBytes, decimalBytes_length]
      have d31 : day ≤ 31 := by
        rw [← (monthDays_eq m1 m12).1] at dle
        exact Nat.le_trans dle (monthDays_le year month)
      obtain ⟨hlast, hraw, hm, hd, hh, hi, hs⟩ :=
        (timeFields_iff hlen).mpr
          ⟨hbytes, by omega, by omega, by omega, by omega, by omega, by omega⟩
      have hy : (if year % 100 < 50 then 2000 + year % 100 else 1900 + year % 100) = year := by
        split <;> omega
      refine ⟨⟨hlen, hlast⟩, year % 100, hraw, ?_⟩
      rw [hy]
      refine ⟨by omega, month, hm, day, hd, hour, hh, minute, hi,
        second, hs, ⟨m1, m12, d1, ?_, h24, i60, s60⟩, timeSeconds_eq (by omega) m1 m12 d1⟩
      rw [(monthDays_eq m1 m12).1]
      exact dle
  by_cases h18 : value.tag = 0x18
  · simp only [readTime, h18, bind_ok_iff, ensure_ok_iff, pure, Except.pure, Except.ok.injEq,
      ↓reduceIte, exists_eq_left', exists_const, true_and,
      show ((24 : UInt8) = 23) = False by decide, show ((4 : Nat) = 2) = False by decide,
      false_and, false_or]
    constructor
    · rintro ⟨⟨hlen, hlast⟩, year, hraw, pos, month, hm, day, hd, hour, hh, minute, hi, second, hs,
        ⟨m1, m12, d1, dle, h24, i60, s60⟩, rfl⟩
      obtain ⟨hbytes, hlt, -⟩ := (timeFields_iff hlen).mp ⟨hlast, hraw, hm, hd, hh, hi, hs⟩
      refine ⟨year, month, day, hour, minute, second, ⟨pos, hlt, hbytes⟩, m1, m12, d1, ?_, h24, i60,
        s60, timeSeconds_eq pos m1 m12 d1⟩
      rw [← (monthDays_eq m1 m12).1]
      exact dle
    · rintro ⟨year, month, day, hour, minute, second, ⟨pos, hi, hbytes⟩, m1, m12, d1, dle, h24, i60,
        s60, rfl⟩
      have hlen : value.content.data.toList.length = 4 + 11 := by
        simp [hbytes, timeBytes, decimalBytes_length]
      have d31 : day ≤ 31 := by
        rw [← (monthDays_eq m1 m12).1] at dle
        exact Nat.le_trans dle (monthDays_le year month)
      obtain ⟨hlast, hraw, hm, hd, hh, hi, hs⟩ :=
        (timeFields_iff hlen).mpr ⟨hbytes, hi, by omega, by omega, by omega, by omega, by omega⟩
      refine ⟨⟨hlen, hlast⟩, year, hraw, pos, month, hm, day, hd, hour, hh, minute, hi,
        second, hs, ⟨m1, m12, d1, ?_, h24, i60, s60⟩, timeSeconds_eq pos m1 m12 d1⟩
      rw [(monthDays_eq m1 m12).1]
      exact dle
  · simp only [readTime, h17, h18, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, bind,
      Except.bind, reduceCtorEq, false_iff, not_exists]
    rintro year month day hour minute second ⟨(⟨h, -⟩ | ⟨h, -⟩), -⟩ <;> contradiction

/-- A validity reads as its two endpoints exactly when it holds two times in order. -/
theorem readValidity_eq_ok_iff {value : Der.Value} {notBefore notAfter : Int} :
    readValidity value = .ok (notBefore, notAfter) ↔ ∃ first last,
      fields 0x30 value = .ok [first, last] ∧ readTime first = .ok notBefore ∧
        readTime last = .ok notAfter ∧ notBefore ≤ notAfter := by
  unfold readValidity
  rw [bind_ok_iff]
  constructor
  · rintro ⟨children, hc, h⟩
    rcases children with _ | ⟨first, _ | ⟨last, _ | ⟨other, rest⟩⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [bind_ok_iff, ensure_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨a, ha, b, hb, _, hab, rfl, rfl⟩ := h
      exact ⟨first, last, hc, ha, hb, hab⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rintro ⟨first, last, hc, ha, hb, hab⟩
    refine ⟨[first, last], hc, ?_⟩
    simp [ha, hb, hab, ensure, bind, Except.bind, pure, Except.pure]

/-- A DER step lifted to the certificate boundary returns a value exactly when the step does. -/
private theorem der_ok_iff {α : Type} {x : Except Der.Error α} {a : α} :
    der x = .ok a ↔ x = .ok a :=
  mapError_ok_iff

/-- An extension reads exactly when it is a SEQUENCE of an OID, optional TRUE and OCTET STRING.

The fields are those of RFC 5280 §4.1, where the critical flag is a BOOLEAN DEFAULT FALSE.

It reads as the OID content, a critical flag set when TRUE is present, and the string octets. -/
theorem readExtension_eq_ok_iff {value : Der.Value} {ext : Extension} :
    readExtension value = .ok ext ↔ ∃ oid data, Der.oid oid = .ok ext.oid ∧ data.tag = 4 ∧
      data.content = ext.value ∧
      ((fields 0x30 value = .ok [oid, data] ∧ ext.critical = false) ∨
        ∃ critical, fields 0x30 value = .ok [oid, critical, data] ∧ critical.tag = 1 ∧
          -- TRUE is the BOOLEAN with the one octet FF (X.690 §11.1).
          --
          -- DER omits a value equal to its default (X.690 §11.5).
          --
          -- So an explicit FALSE is rejected.
          critical.content.data.toList = [0xFF] ∧ ext.critical = true) := by
  unfold readExtension
  rw [bind_ok_iff]
  constructor
  · rintro ⟨children, hc, h⟩
    rcases children with _ | ⟨oid, _ | ⟨data, _ | ⟨last, _ | ⟨other, rest⟩⟩⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [bind_ok_iff, ensure_ok_iff, der_ok_iff, pure, Except.pure,
        Except.ok.injEq] at h
      obtain ⟨_, tag, o, ho, rfl⟩ := h
      exact ⟨oid, data, ho, tag, rfl, .inl ⟨hc, rfl⟩⟩
    · simp only [bind_ok_iff, ensure_ok_iff, der_ok_iff, pure, Except.pure,
        Except.ok.injEq] at h
      obtain ⟨_, tag, flag, hflag, _, rfl, o, ho, rfl⟩ := h
      obtain ⟨one, ff⟩ := Proofs.Der.boolean_ok_iff.mp hflag
      exact ⟨oid, last, ho, tag, rfl, .inr ⟨data, hc, one, by simpa using ff, rfl⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rintro ⟨oid, data, ho, tag, hv, (⟨hc, hf⟩ | ⟨critical, hc, one, ff, hf⟩)⟩
    · refine ⟨[oid, data], hc, ?_⟩
      refine bind_unit_ok_iff.mpr ⟨ensure_ok_iff.mpr tag, ?_⟩
      refine bind_ok_iff.mpr ⟨_, der_ok_iff.mpr ho, ?_⟩
      -- The extension is its three fields.
      rw [hv, ← hf]
      rfl
    · refine ⟨[oid, critical, data], hc, ?_⟩
      have hb : Der.boolean critical = .ok true :=
        Proofs.Der.boolean_ok_iff.mpr ⟨one, by simpa using ff⟩
      refine bind_unit_ok_iff.mpr ⟨ensure_ok_iff.mpr tag, ?_⟩
      refine bind_ok_iff.mpr ⟨_, der_ok_iff.mpr hb, ?_⟩
      refine bind_unit_ok_iff.mpr ⟨ensure_ok_iff.mpr rfl, ?_⟩
      refine bind_ok_iff.mpr ⟨_, der_ok_iff.mpr ho, ?_⟩
      rw [hv, ← hf]
      rfl

/-- The validity endpoints of a parsed certificate are what its own validity field reads as.

The signed part is the first field of the certificate that the input bytes encode.

The validity is the fourth field of the signed part, after the version when there is one. -/
theorem readCertificate_validity {bytes : ByteArray} {certificate : Certificate}
    (parsed : readCertificate bytes = .ok certificate) :
    ∃ outer tbs rest values validity, der (Der.exact 0x30 bytes) = .ok outer ∧
      fields 0x30 outer = .ok (tbs :: rest) ∧ tbs.encoded = certificate.tbs ∧
      fields 0x30 tbs = .ok values ∧
      values[if values.head?.map (·.tag) = some 0xa0 then 4 else 3]? = some validity ∧
      readValidity validity = .ok (certificate.notBefore, certificate.notAfter) := by
  unfold readCertificate at parsed
  simp only [bind_ok_iff] at parsed
  obtain ⟨_, hOuter, children, hChildren, h⟩ := parsed
  split at h
  · simp only [bind_ok_iff] at h
    obtain ⟨_, _, _, _, values, hValues, h⟩ := h
    split at h
    · split at h
      case' isTrue =>
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at h
        obtain ⟨_, _, _, _, _, _, h⟩ := h
      case' isFalse =>
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at h
      -- Both version branches end in the same match on the remaining fields.
      all_goals
        split at h
        · simp only [bind_ok_iff] at h
          obtain ⟨_, _, _, _, _, _, _, _, _, _, x, hx, _, _, h⟩ := h
          split at h
          · simp only [bind_ok_iff, Except.ok.injEq] at h
            obtain ⟨_, _, _, _, _, _, rfl⟩ := h
            exact ⟨_, _, _, _, _, hOuter, hChildren, rfl, hValues, by simp_all, hx⟩
          · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The values of the extension errors -/

/-- A list with a repeated value names one that occurs at least twice. -/
theorem firstRepeated_some (l : List (List UInt8)) (h : ¬ l.Nodup) :
    ∃ x, firstRepeated l = some x ∧ 2 ≤ l.count x := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    by_cases m : a ∈ t
    · refine ⟨a, by simp [firstRepeated, m], ?_⟩
      have := List.count_pos_iff.mpr m
      simp
      omega
    · have : ¬ t.Nodup := by simpa [List.nodup_cons, m] using h
      obtain ⟨x, hx, d⟩ := ih this
      refine ⟨x, by simp [firstRepeated, m, hx], ?_⟩
      simp [List.count_cons]
      omega

/-- When a critical extension other than the libp2p one is present, the error names its OID. -/
theorem criticalOid_spec (es : List Extension)
    (h : es.all (fun ext => !ext.critical || ext.oid == libp2pOid) = false) :
    ∃ e ∈ es, e.critical = true ∧ (e.oid == libp2pOid) = false ∧
      criticalOid es = e.oid.data.toList := by
  have : ∃ e ∈ es, (e.critical && !(e.oid == libp2pOid)) = true := by
    simpa [List.all_eq_false] using h
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr this)
  have mem := List.mem_of_find?_eq_some he
  have q := List.find?_some he
  simp at q
  exact ⟨e, mem, q.1, by simpa using q.2, by simp [criticalOid, he]⟩

/-! ## The P-256 key of a certificate -/

open Proofs.Der (data_toList_eq_nil_of_isEmpty data_toList_eq_of_read_ok read_eq_ok_of_length_lt
  exists_read_of_children_eq_ok_pair children_go_succ_eq_ok_of_read children_go_empty
  size_eq_length)

/-- The fields of a value are its children, after a check of its tag. -/
private theorem fields_ok_iff {tag : UInt8} {value : Der.Value} {values : List Der.Value} :
    fields tag value = .ok values ↔ value.tag = tag ∧ Der.children value.content = .ok values := by
  unfold fields
  by_cases ht : value.tag = tag
  · cases Der.children value.content <;>
      simp [ensure, ht, der, Except.mapError, bind, Except.bind]
  · simp only [ensure, ht, ite_false, bind, Except.bind, reduceCtorEq, false_and]

/-- An input that the uncompressed decoder accepts is 65 octets. -/
private theorem length_of_decodeUncompressed {key : List UInt8}
    {point : Cryptography.Secp256r1.Point}
    (h : Cryptography.Secp256r1.decodeUncompressed key = some point) : key.length = 65 := by
  obtain ⟨x, y, -, -, rfl⟩ := Cryptography.Secp256r1.decodeUncompressed_eq_some_iff.mp h
  simp [Cryptography.Secp256r1.encodeUncompressed, Cryptography.Secp256r1.Fp.toBytes,
    ]

/-- The content octets of the algorithm id-ecPublicKey with the curve secp256r1. -/
private abbrev p256Algorithm : List UInt8 :=
  [0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01,
    0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]

/-- A P-256 key reads from an SPKI exactly when the SPKI is 26 fixed octets, then its encoding.

Every other key type, curve, parameter form and length form is rejected.

So is an unused bit or a trailing octet. -/
theorem readP256_eq_ok_iff {spki : ByteArray} {point : Cryptography.Secp256r1.Point} :
    readP256 spki = .ok point ↔ ∃ key, Cryptography.Secp256r1.decodeUncompressed key = some point ∧
      -- The 26 octets start with a SEQUENCE header and the DER of id-ecPublicKey with secp256r1.
      --
      -- They end with a BIT STRING header.
      --
      -- The key type OID is `1.2.840.10045.2.1` of RFC 5480 §2.1.1.
      --
      -- The curve OID is `1.2.840.10045.3.1.7` of RFC 5480 §2.1.1.1.
      --
      -- The BIT STRING has no unused bits and holds an uncompressed point (RFC 5480 §2.2).
      spki.data.toList = [0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02,
        0x01, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07, 0x03, 0x42, 0x00] ++
          key := by
  constructor
  · intro h
    unfold readP256 at h
    obtain ⟨sequence, hseq, h1⟩ := bind_ok_iff.mp h
    obtain ⟨values, hvalues, h2⟩ := bind_ok_iff.mp h1
    rcases values with _ | ⟨algorithm, _ | ⟨key, _ | ⟨_, _⟩⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h2
    · simp [throw, throwThe, MonadExceptOf.throw] at h2
    rotate_left
    · simp [throw, throwThe, MonadExceptOf.throw] at h2
    obtain ⟨⟨oid, parameter⟩, halg, h3⟩ := bind_ok_iff.mp h2
    obtain ⟨curve, hcurve, h4⟩ := bind_ok_iff.mp h3
    obtain ⟨curveOid, hcurveOid, h5⟩ := bind_ok_iff.mp h4
    obtain ⟨hensure, h6⟩ := bind_unit_ok_iff.mp h5
    obtain ⟨bytes, hbytes, h7⟩ := bind_ok_iff.mp h6
    clear h h1 h2 h3 h4 h5 h6
    obtain ⟨rfl, rfl⟩ := ensure_ok_iff.mp hensure
    cases hdec : Cryptography.Secp256r1.decodeUncompressed bytes.data.toList with
    | none => simp [hdec, throw, throwThe, MonadExceptOf.throw] at h7
    | some p =>
    simp only [hdec, pure, Except.pure, Except.ok.injEq] at h7
    subst h7
    refine ⟨bytes.data.toList, hdec, ?_⟩
    have hk := length_of_decodeUncompressed hdec
    -- The algorithm holds the key type and one parameter, the curve.
    unfold readAlgorithm at halg
    obtain ⟨parts, hparts, halg⟩ := bind_ok_iff.mp halg
    obtain ⟨atag, achildren⟩ := fields_ok_iff.mp hparts
    rcases parts with _ | ⟨o, _ | ⟨q, _ | ⟨_, _⟩⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at halg
    · obtain ⟨b, -, halg⟩ := bind_ok_iff.mp halg
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at halg
      obtain ⟨-, rfl⟩ := halg
      have empty : Der.exact 6 ByteArray.empty = .error (.truncated 2 0) := rfl
      rw [der_ok_iff, empty] at hcurve
      cases hcurve
    rotate_left
    · simp [throw, throwThe, MonadExceptOf.throw] at halg
    obtain ⟨-, -, halg⟩ := bind_ok_iff.mp halg
    obtain ⟨b, hb, halg⟩ := bind_ok_iff.mp halg
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at halg
    obtain ⟨rfl, rfl⟩ := halg
    -- Each value is short, so its octets are its tag, its length and its content.
    obtain ⟨otag, ocontent, -⟩ := Proofs.Der.oid_ok_iff.mp (der_ok_iff.mp hb)
    obtain ⟨ctag, ccontent, -⟩ := Proofs.Der.oid_ok_iff.mp (der_ok_iff.mp hcurveOid)
    obtain ⟨crest, hcread, cempty⟩ := Proofs.Der.exact_ok_iff.mp (der_ok_iff.mp hcurve)
    obtain ⟨hcread, -⟩ := Proofs.Der.readTag_ok_iff.mp hcread
    obtain ⟨ktag, kcontent⟩ := Proofs.Der.bitString_ok_iff.mp (der_ok_iff.mp hbytes)
    obtain ⟨s1, s2, hoRead, hqRead, s2empty⟩ := exists_read_of_children_eq_ok_pair achildren
    obtain ⟨r1, r2, haRead, hkRead, r2empty⟩ :=
      exists_read_of_children_eq_ok_pair (fields_ok_iff.mp hvalues).2
    obtain ⟨srest, hsread, sempty⟩ := Proofs.Der.exact_ok_iff.mp (der_ok_iff.mp hseq)
    obtain ⟨hsread, stag⟩ := Proofs.Der.readTag_ok_iff.mp hsread
    have hq : q.encoded.data.toList =
        [0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07] := by
      rw [data_toList_eq_of_read_ok hcread
        (content := [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07])
        (by rw [← ccontent]; rfl) (by decide), ctag, data_toList_eq_nil_of_isEmpty cempty]
      rfl
    have hs1 : s1.data.toList = q.encoded.data.toList := by
      obtain ⟨-, -, hin, -⟩ := Proofs.Der.read_ok_iff.mp hqRead
      rw [hin, data_toList_eq_nil_of_isEmpty s2empty, List.append_nil]
    have hacontent : algorithm.content.data.toList = p256Algorithm := by
      rw [data_toList_eq_of_read_ok hoRead (content := [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01])
        (by rw [← ocontent]; rfl) (by decide), otag, hs1, hq]
      rfl
    have hr1 : r1.data.toList = [0x03, 0x42, 0x00] ++ bytes.data.toList := by
      rw [data_toList_eq_of_read_ok hkRead kcontent (by simp [hk]), ktag,
        data_toList_eq_nil_of_isEmpty r2empty]
      simp [hk]
    have hscontent : sequence.content.data.toList =
        [0x30, 0x13] ++ p256Algorithm ++ [0x03, 0x42, 0x00] ++ bytes.data.toList := by
      rw [data_toList_eq_of_read_ok haRead hacontent (by decide), atag, hr1]
      rfl
    rw [data_toList_eq_of_read_ok hsread hscontent (by simp [hk]), stag,
      data_toList_eq_nil_of_isEmpty sempty]
    simp [hk]
  · rintro ⟨key, hdec, hspki⟩
    have hk := length_of_decodeUncompressed hdec
    obtain ⟨data⟩ := spki
    have hdata : data = (0x30 :: UInt8.ofNat (0x30 :: UInt8.ofNat p256Algorithm.length ::
        (p256Algorithm ++ (3 :: UInt8.ofNat (0 :: key).length :: ((0 :: key) ++ [])))).length ::
        ((0x30 :: UInt8.ofNat p256Algorithm.length ::
        (p256Algorithm ++ (3 :: UInt8.ofNat (0 :: key).length :: ((0 :: key) ++ [])))) ++
          [])).toArray := by
      apply Array.toList_inj.mp
      rw [show data.toList = _ from hspki]
      simp [hk]
    subst hdata
    have hkey := read_eq_ok_of_length_lt (tag := 3) (content := 0 :: key) (rest := [])
      (by decide) (by decide)
      (by simp [hk])
    have halgorithm := read_eq_ok_of_length_lt (tag := 0x30) (content := p256Algorithm)
      (rest := 3 :: UInt8.ofNat (0 :: key).length :: ((0 :: key) ++ [])) (by decide) (by decide)
      (by decide)
    have hsequence := read_eq_ok_of_length_lt (tag := 0x30) (rest := []) (by decide) (by decide)
      (content := 0x30 :: UInt8.ofNat p256Algorithm.length ::
        (p256Algorithm ++ (3 :: UInt8.ofNat (0 :: key).length :: ((0 :: key) ++ []))))
      (by simp [hk])
    have hexact := Proofs.Der.exact_ok_iff.mpr
      ⟨_, Proofs.Der.readTag_ok_iff.mpr ⟨hsequence, rfl⟩, rfl⟩
    have hchildren := children_go_succ_eq_ok_of_read halgorithm
      (children_go_succ_eq_ok_of_read (fuel := 87) hkey (children_go_empty _))
    have hsize : (⟨(0x30 :: UInt8.ofNat p256Algorithm.length :: (p256Algorithm ++
        (3 :: UInt8.ofNat (0 :: key).length :: ((0 :: key) ++ [])))).toArray⟩ : ByteArray).size =
        87 + 1 + 1 := by
      rw [size_eq_length]
      simp [hk]
    have hcurve : Der.exact 6 ⟨#[0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]⟩ =
        .ok ⟨6, ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]⟩,
          ⟨#[0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]⟩⟩ := by
      rfl
    have hparameters : readAlgorithm ⟨0x30, ⟨p256Algorithm.toArray⟩,
        ⟨(0x30 :: UInt8.ofNat p256Algorithm.length :: p256Algorithm).toArray⟩⟩ =
        .ok (ecPublicKeyOid, ⟨#[0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]⟩) := by
      rfl
    have hbits : Der.bitString ⟨3, ⟨(0 :: key).toArray⟩,
        ⟨(3 :: UInt8.ofNat (0 :: key).length :: (0 :: key)).toArray⟩⟩ = .ok ⟨key.toArray⟩ :=
      Proofs.Der.bitString_ok_iff.mpr ⟨rfl, by simp⟩
    have hoid : Der.oid ⟨6, ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]⟩,
        ⟨#[0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]⟩⟩ = .ok p256Oid := by
      rfl
    unfold readP256
    refine bind_ok_iff.mpr ⟨_, der_ok_iff.mpr hexact, ?_⟩
    refine bind_ok_iff.mpr
      ⟨_, fields_ok_iff.mpr ⟨rfl, by rw [Der.children, hsize]; exact hchildren⟩, ?_⟩
    dsimp only
    refine bind_ok_iff.mpr ⟨_, hparameters, ?_⟩
    refine bind_ok_iff.mpr ⟨_, der_ok_iff.mpr hcurve, ?_⟩
    refine bind_ok_iff.mpr ⟨_, der_ok_iff.mpr hoid, ?_⟩
    refine bind_unit_ok_iff.mpr ⟨ensure_ok_iff.mpr ⟨rfl, rfl⟩, ?_⟩
    refine bind_ok_iff.mpr ⟨_, der_ok_iff.mpr hbits, ?_⟩
    simp [hdec, pure, Except.pure]

/-- An SPKI that a P-256 key reads from is 91 octets.

That is the length that the host key check of authentication requires of an ECDSA key. -/
theorem size_of_readP256_eq_ok {spki : ByteArray} {point : Cryptography.Secp256r1.Point}
    (h : readP256 spki = .ok point) : spki.size = 91 := by
  obtain ⟨key, hdec, hspki⟩ := readP256_eq_ok_iff.mp h
  rw [size_eq_length, hspki, List.length_append, length_of_decodeUncompressed hdec]
  rfl

end EthLib.Networking.Proofs.Libp2p.Tls

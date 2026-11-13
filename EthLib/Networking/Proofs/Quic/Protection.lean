module

public import EthLib.Networking.Quic.Protection
public import EthLib.Cryptography.Proofs.Aes.Gcm
public import EthLib.Cryptography.Proofs.ChaCha20Poly1305

/-!
# Proofs: QUIC packet protection

Payload decryption undoes encryption for both supported suites.

The header mask undoes itself for every header layout and every mask.
-/

public section

namespace EthLib.Networking.Quic.Protection

open EthLib.Base EthLib.Cryptography

/-- Payload decryption returns the encrypted plaintext, RFC 9001 §5.3. -/
theorem decryptPayload_encryptPayload (suite : CipherSuite) (keys : PacketKeys suite)
    (number : PacketNumber) (header plaintext ciphertext tag : ByteArray)
    (h : encryptPayload suite keys number header plaintext = .ok (ciphertext, tag)) :
    decryptPayload suite keys number header ciphertext tag = .ok plaintext := by
  cases suite with
  | aes128GcmSha256 =>
    unfold encryptPayload at h
    cases he : Aes.Gcm.encrypt (Aes.ciph .aes128 keys.key) 16
        (packBytes (nonce keys.iv number)) plaintext header with
    | error e => simp [he, Except.mapError] at h
    | ok out =>
      simp [he, Except.mapError] at h
      cases h
      change (Aes.Gcm.decrypt (Aes.ciph .aes128 keys.key) 16
        (packBytes (nonce keys.iv number)) ciphertext header tag).mapError Error.aes = .ok plaintext
      rw [Aes.Gcm.decrypt_encrypt _ _ _ _ _ _ _ he]
      rfl
  | chacha20Poly1305Sha256 =>
    unfold encryptPayload at h
    cases he : ChaCha20Poly1305.encrypt keys.key (nonce keys.iv number) header plaintext with
    | error e => simp [he, Except.mapError, Except.map] at h
    | ok out =>
      obtain ⟨c, t⟩ := out
      simp [he, Except.mapError, Except.map] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [decryptPayload, size_packBytes, ↓reduceDIte, readBytes_packBytes]
      rw [ChaCha20Poly1305.decrypt_encrypt _ _ _ _ _ _ he]
      rfl

/-- Header protection preserves every packet's length, RFC 9001 §5.4.1. -/
@[simp] theorem size_applyMask (longHeader : Bool) (offset : Nat)
    (width : Packet.PacketNumberLength) (mask : Vector UInt8 5) (bytes : ByteArray) :
    (applyMask longHeader offset width mask bytes).size = bytes.size := by
  simp only [applyMask, ByteArray.size, List.size_toArray, List.length_mapIdx, Array.length_toList]

/-- Applying one header mask twice restores every byte, RFC 9001 §5.4.1. -/
theorem applyMask_applyMask (longHeader : Bool) (offset : Nat) (width : Packet.PacketNumberLength)
    (mask : Vector UInt8 5) (bytes : ByteArray) :
    applyMask longHeader offset width mask
      (applyMask longHeader offset width mask bytes) = bytes := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size_data, size_applyMask]
  · intro i h₁ h₂
    simp only [applyMask, List.getElem_toArray, List.getElem_mapIdx, Array.getElem_toList]
    simp [UInt8.xor_assoc]



/-- Each header-protection byte is the input byte XOR its selected mask byte. -/
theorem getElem_applyMask (longHeader : Bool) (offset : Nat) (width : Packet.PacketNumberLength)
    (mask : Vector UInt8 5) (bytes : ByteArray) (i : Nat) (hi : i < bytes.size) :
    (applyMask longHeader offset width mask bytes)[i]'(by simpa using hi) =
      bytes[i] ^^^ maskByte longHeader offset width mask i := by
  simp only [applyMask, ByteArray.getElem_eq_getElem_data, List.getElem_toArray,
    List.getElem_mapIdx, Array.getElem_toList]

/-- Header masking never changes the ciphertext sample, RFC 9001 §5.4.2. -/
theorem sample_applyMask (longHeader : Bool) (offset : Nat) (width : Packet.PacketNumberLength)
    (mask : Vector UInt8 5) (bytes : ByteArray) :
    sample (applyMask longHeader offset width mask bytes) offset = sample bytes offset := by
  unfold sample
  simp only [size_applyMask]
  split
  · congr 1
    apply Vector.ext
    intro i hi
    simp only [readBytes, Vector.getElem_ofFn]
    change (applyMask longHeader offset width mask bytes)[offset + 4 + i]'
      (by rw [size_applyMask]; omega) = _
    rw [getElem_applyMask _ _ _ _ _ _ (by omega)]
    have hzero : offset + 4 + i ≠ 0 := by omega
    have hpn : ¬(offset ≤ offset + 4 + i ∧
        offset + 4 + i < offset + (width.val + 1)) := by omega
    rw [maskByte, ite_eq_right hzero, dite_eq_right hpn, UInt8.xor_zero]
    rfl
  · rfl

private theorem and_xor (a b c : UInt8) :
    (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_and, UInt8.toNat_xor, Nat.and_xor_distrib_right]

/-- Masking low bits preserves the Header Form bit, RFC 9001 §5.4.1. -/
theorem headerForm_xor (first mask : UInt8) (longHeader : Bool) :
    (first ^^^ (mask &&& (if longHeader then 0x0f else 0x1f))) &&& 0x80 =
      first &&& 0x80 := by
  rw [and_xor, UInt8.and_assoc]
  cases longHeader <;> simp only [Bool.false_eq_true, ↓reduceIte,
    show (0x0f : UInt8) &&& 0x80 = 0 by decide,
    show (0x1f : UInt8) &&& 0x80 = 0 by decide, UInt8.and_zero, UInt8.xor_zero]


/-- Header removal restores an unmasked packet's fields under the mask of its own sample.

The sample lies beyond every possible encoded packet number, RFC 9001 §§5.4.1 to 5.4.2. -/
theorem removeHeaderProtection_applyMask (suite : CipherSuite)
    (hp : Vector UInt8 suite.keyLength) (offset : Nat) (bytes : ByteArray)
    (hoff : 0 < offset) (hsize : offset + 20 ≤ bytes.size)
    (s : Vector UInt8 16) (hs : sample bytes offset = .ok s) :
    let first := bytes[0]'(by omega)
    let width := Packet.widthOfFirst first
    let masked := applyMask (first &&& 0x80 != 0) offset width (headerMask suite hp s) bytes
    removeHeaderProtection suite hp offset masked = .ok
      ⟨bytes.extract 0 (offset + width.val + 1),
        bytes.extract (offset + width.val + 1) (bytes.size - 16),
        bytes.extract (bytes.size - 16) bytes.size,
        bytesToNat (bytes.extract offset (offset + width.val + 1)).data.toList, width⟩ := by
  dsimp only
  let first := bytes[0]'(by omega)
  let width := Packet.widthOfFirst first
  let longHeader := first &&& 0x80 != 0
  let mask := headerMask suite hp s
  have hfirst : (applyMask longHeader offset width mask bytes)[0]'(by simp; omega) =
      first ^^^ (mask[0] &&& (if longHeader then 0x0f else 0x1f)) := by
    rw [getElem_applyMask]
    rfl
  have hform :
      ((applyMask longHeader offset width mask bytes)[0]'(by simp; omega) &&& 0x80 != 0) =
        longHeader := by
    rw [hfirst, headerForm_xor]
  have hwidth : Packet.widthOfFirst
      ((applyMask longHeader offset width mask bytes)[0]'(by simp; omega) ^^^
        (mask[0] &&& (if longHeader then 0x0f else 0x1f))) = width := by
    rw [hfirst, UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]
  change removeHeaderProtection suite hp offset (applyMask longHeader offset width mask bytes) = _
  unfold removeHeaderProtection
  rw [show ensure (0 < offset ∧ offset < (applyMask longHeader offset width mask bytes).size)
      Error.header = .ok () by simp only [ensure, size_applyMask]; rw [ite_eq_left (by omega)]]
  simp only [bind, Except.bind]
  rw [sample_applyMask, hs]
  dsimp only
  rw [dite_eq_left (by simp only [size_applyMask]; omega)]
  rw [hform, hwidth]
  rw [show ensure (offset + width.val + 1 + 16 ≤
      (applyMask longHeader offset width mask bytes).size) Error.header = .ok () by
    simp only [ensure, size_applyMask]; rw [ite_eq_left (by omega)]]
  dsimp only
  rw [applyMask_applyMask]
  rfl


/-- An Initial packet's suite check accepts exactly AES-128-GCM, RFC 9001 §5. -/
theorem checkSuite_initial_ok_iff (suite : CipherSuite) (destination source token : List UInt8)
    (width : Packet.PacketNumberLength) (length : Varint) (number : Nat) :
    checkSuite suite (.initial destination source token width length number) = .ok () ↔
      suite = .aes128GcmSha256 := by
  simp only [checkSuite, ensure_ok_iff]

/-- Both supported AEADs preserve text length and append a 16-byte tag, RFC 9001 §5.3. -/
theorem encryptPayload_sizes (suite : CipherSuite) (keys : PacketKeys suite)
    (number : PacketNumber) (header plaintext ciphertext tag : ByteArray)
    (h : encryptPayload suite keys number header plaintext = .ok (ciphertext, tag)) :
    ciphertext.size = plaintext.size ∧ tag.size = 16 := by
  cases suite with
  | aes128GcmSha256 =>
    change (Aes.Gcm.encrypt (Aes.ciph .aes128 keys.key) 16
      (packBytes (nonce keys.iv number)) plaintext header).mapError Error.aes =
        .ok (ciphertext, tag) at h
    cases he : Aes.Gcm.encrypt (Aes.ciph .aes128 keys.key) 16
        (packBytes (nonce keys.iv number)) plaintext header with
    | error e => simp [he, Except.mapError] at h
    | ok out =>
      simp [he, Except.mapError] at h
      cases h
      unfold Aes.Gcm.encrypt at he
      cases hc : Aes.Gcm.checkLengths 16 (packBytes (nonce keys.iv number)) plaintext header with
      | error e => simp [hc, bind, Except.bind] at he
      | ok u =>
        simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he
        cases he
        exact ⟨Aes.size_ctr _ _ _ _, Aes.Gcm.size_tag _ (by decide) _ _ _ _⟩
  | chacha20Poly1305Sha256 =>
    unfold encryptPayload at h
    cases he : ChaCha20Poly1305.encrypt keys.key (nonce keys.iv number) header plaintext with
    | error e => simp [he, Except.mapError, Except.map] at h
    | ok out =>
      obtain ⟨c, t⟩ := out
      simp [he, Except.mapError, Except.map] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ChaCha20Poly1305.encrypt_size _ _ _ _ _ _ he, size_packBytes _⟩

/-- A header that passes the header checks has zero reserved bits. -/
theorem checkReservedBits_of_checkHeader {suite : CipherSuite} {header : ByteArray}
    {protectedLength : Nat} (h : checkHeader suite header protectedLength = .ok ()) :
    checkReservedBits header = .ok () := by
  have ha : checkAuthenticatedHeader header = .ok () := by
    cases hc : checkAuthenticatedHeader header with
    | error e => simp [checkHeader, hc, bind, Except.bind] at h
    | ok u => rfl
  unfold checkAuthenticatedHeader at ha
  unfold checkReservedBits
  split
  · rename_i hs
    simp only [hs, ↓reduceDIte, ensure_ok_iff] at ha
    exact ensure_ok_iff.mpr (Or.inr ha.2)
  · rfl

/-- The whole protected packet returns its header and payload when number reconstruction is exact.

RFC 9001 §5.5 allows authentication to fail when a delayed packet reconstructs to another number.

The explicit reconstruction hypothesis is therefore necessary. -/
theorem unprotect_protect (suite : CipherSuite) (keys : PacketKeys suite)
    (number : PacketNumber) (expected offset : Nat) (header plaintext packet : ByteArray)
    (hheader : 0 < header.size)
    (hreconstruct : reconstructNumber (Packet.widthOfFirst header[0])
      (number.val % 256 ^ ((Packet.widthOfFirst header[0]).val + 1)) expected = .ok number)
    (hprotect : protect suite keys number offset header plaintext = .ok packet) :
    unprotect suite keys expected offset packet = .ok (header, plaintext) := by
  unfold protect at hprotect
  cases hc : checkHeader suite header (plaintext.size + 16) with
  | error e => simp [hc, bind, Except.bind] at hprotect
  | ok u =>
    have hcheck : checkHeader suite header (plaintext.size + 16) = .ok () := by
      simpa only [Subsingleton.elim u ()] using hc
    simp only [hc, bind, Except.bind] at hprotect
    rw [dite_eq_left hheader] at hprotect
    generalize hw : Packet.widthOfFirst header[0] = width at hprotect
    rw [hw] at hreconstruct
    cases ho : ensure (0 < offset ∧ header.size = offset + width.val + 1) Error.header with
    | error e => rw [ho] at hprotect; cases hprotect
    | ok u =>
      rw [ho] at hprotect
      have ho' : 0 < offset ∧ header.size = offset + width.val + 1 := ensure_ok_iff.mp ho
      cases hn : ensure (bytesToNat (header.extract offset header.size).data.toList =
          number.val % 256 ^ (width.val + 1)) Error.packetNumber with
      | error e => rw [hn] at hprotect; cases hprotect
      | ok u =>
        rw [hn] at hprotect
        have hn' := ensure_ok_iff.mp hn
        cases he : encryptPayload suite keys number header plaintext with
        | error e => rw [he] at hprotect; cases hprotect
        | ok out =>
          rw [he] at hprotect
          dsimp only at hprotect
          obtain ⟨ciphertext, tag⟩ := out
          cases hs : sample (header ++ ciphertext ++ tag) offset with
          | error e => rw [hs] at hprotect; cases hprotect
          | ok s =>
            simp only [hs, pure, Except.pure, Except.ok.injEq] at hprotect
            subst packet
            obtain ⟨htext, htag⟩ := encryptPayload_sizes suite keys number header plaintext
              ciphertext tag he
            have hsize : offset + 20 ≤ (header ++ ciphertext ++ tag).size := by
              by_cases h : offset + 4 + 16 ≤ (header ++ ciphertext ++ tag).size
              · omega
              · simp only [sample, dite_eq_right h] at hs
                cases hs
            have hfirst : (header ++ ciphertext ++ tag)[0]'(by simp; omega) = header[0] := by
              rw [ByteArray.getElem_append_left (by simp; omega),
                ByteArray.getElem_append_left hheader]
            have hm := removeHeaderProtection_applyMask suite keys.hp offset
              (header ++ ciphertext ++ tag) ho'.1 hsize s hs
            simp only [hfirst, hw] at hm
            have hprefix : (header ++ ciphertext ++ tag).extract 0
                (offset + width.val + 1) = header := by
              rw [← ho'.2, ByteArray.append_assoc, ByteArray.extract_append_eq_left rfl]
            have hend : (header ++ ciphertext ++ tag).size - 16 =
                header.size + ciphertext.size := by simp only [ByteArray.size_append, htag]; omega
            have hct : (header ++ ciphertext ++ tag).extract (offset + width.val + 1)
                ((header ++ ciphertext ++ tag).size - 16) = ciphertext := by
              rw [← ho'.2, hend, ByteArray.append_assoc]
              change (header ++ (ciphertext ++ tag)).extract (header.size + 0)
                (header.size + ciphertext.size) = ciphertext
              rw [ByteArray.extract_append_size_add]
              exact ByteArray.extract_append_eq_left rfl
            have htag' : (header ++ ciphertext ++ tag).extract
                ((header ++ ciphertext ++ tag).size - 16)
                (header ++ ciphertext ++ tag).size = tag := by
              rw [hend]
              exact ByteArray.extract_append_eq_right (by simp only [ByteArray.size_append])
                (by simp only [ByteArray.size_append])
            have hpn : (header ++ ciphertext ++ tag).extract offset
                (offset + width.val + 1) = header.extract offset header.size := by
              rw [← ho'.2, ByteArray.append_assoc, ByteArray.extract_append_size_left]
            simp only [hprefix, hct, htag', hpn] at hm
            unfold unprotect
            rw [hm]
            simp only [bind, Except.bind]
            rw [hn', hreconstruct]
            dsimp only
            rw [decryptPayload_encryptPayload suite keys number header plaintext ciphertext tag he]
            rw [htext, htag, checkReservedBits_of_checkHeader hcheck, hcheck]
            rfl

/-- An error map keeps success and its value. -/
private theorem mapError_eq_ok {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by
  cases x <;> simp [Except.mapError]

/-- An AEAD failure comes before any header check, so reserved bits are read after it (§17.2). -/
theorem unprotect_eq_error_of_decryptPayload (suite : CipherSuite) (keys : PacketKeys suite)
    (expected offset : Nat) (packet : ByteArray) (recovered : Unmasked) (number : PacketNumber)
    (error : Error) (hr : removeHeaderProtection suite keys.hp offset packet = .ok recovered)
    (hn : reconstructNumber recovered.width recovered.truncatedNumber expected = .ok number)
    (hd : decryptPayload suite keys number recovered.header recovered.ciphertext
      recovered.tag = .error error) :
    unprotect suite keys expected offset packet = .error error := by
  simp only [unprotect, bind, Except.bind, hr, hn, hd]

/-- Header removal, number reconstruction, AEAD and authenticated header checks are the only gates.

The AEAD authenticates the recovered header and uses the reconstructed number in its nonce.

RFC 9001 §5.3 defines these inputs. -/
theorem unprotect_ok_iff (suite : CipherSuite) (keys : PacketKeys suite)
    (expected : Nat)
    (offset : Nat) (packet header plaintext : ByteArray) :
    unprotect suite keys expected offset packet = .ok (header, plaintext) ↔
      ∃ recovered number,
        removeHeaderProtection suite keys.hp offset packet = .ok recovered ∧
        reconstructNumber recovered.width recovered.truncatedNumber expected = .ok number ∧
        decryptPayload suite keys number recovered.header recovered.ciphertext recovered.tag =
          .ok plaintext ∧
        checkReservedBits recovered.header = .ok () ∧
        checkHeader suite recovered.header (recovered.ciphertext.size + recovered.tag.size) =
          .ok () ∧
        recovered.header = header := by
  simp only [unprotect, bind_ok_iff, mapError_eq_ok]
  constructor
  · rintro ⟨recovered, hr, number, hn, output, ho, u, hres, v, hu, hf⟩
    have hp : (recovered.header, output) = (header, plaintext) := Except.ok.inj hf
    obtain ⟨hh, hp⟩ := Prod.mk.inj hp
    exact ⟨recovered, number, hr, hn, hp ▸ ho, (Subsingleton.elim u ()) ▸ hres,
      (Subsingleton.elim v ()) ▸ hu, hh⟩
  · rintro ⟨recovered, number, hr, hn, ho, hres, hu, hh⟩
    exact ⟨recovered, hr, number, hn, plaintext, ho, (), hres, (), hu, by simp [hh]; rfl⟩

/-- A sample needs 20 bytes from the packet-number offset, RFC 9001 §5.4.2. -/
theorem sample_eq_error_of_short (packet : ByteArray) (offset : Nat)
    (h : packet.size < offset + 20) : sample packet offset = .error .sample := by
  simp [sample, show ¬offset + 4 + 16 ≤ packet.size by omega]

/-- An error map can only return a mapped error. -/
private theorem mapError_eq_error {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {e : ε'}
    (h : x.mapError f = .error e) : ∃ e', e = f e' := by
  cases x with
  | error a =>
    simp only [Except.mapError, Except.error.injEq] at h
    exact ⟨a, h.symm⟩
  | ok a => simp [Except.mapError] at h

private theorem ensure_eq_error {ε : Type} {c : Prop} [Decidable c] {e e' : ε}
    (h : ensure c e = .error e') : e' = e := by
  unfold ensure at h
  split at h <;> simp_all

private theorem removeHeaderProtection_ne (suite : CipherSuite)
    (hp : Vector UInt8 suite.keyLength) (offset : Nat) (packet : ByteArray) :
    removeHeaderProtection suite hp offset packet ≠ .error .reservedBits := by
  intro h
  unfold removeHeaderProtection at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i err heq
    have := ensure_eq_error heq
    simp_all
  · split at h
    · rename_i err heq
      unfold sample at heq
      split at heq <;> simp_all
    · split at h
      · split at h
        · rename_i err heq
          have := ensure_eq_error heq
          simp_all
        · simp at h
      · cases h

private theorem reconstructNumber_ne (width : Packet.PacketNumberLength)
    (truncated expected : Nat) :
    reconstructNumber width truncated expected ≠ .error .reservedBits := by
  intro h
  unfold reconstructNumber at h
  cases hd : Packet.decodePacketNumber width truncated expected <;>
    simp only [hd, bind, Except.bind, Except.mapError, pure, Except.pure] at h
  · cases h
  · split at h
    · cases h
    · cases h

private theorem decryptPayload_ne (suite : CipherSuite) (keys : PacketKeys suite)
    (number : PacketNumber) (header ciphertext tag : ByteArray) :
    decryptPayload suite keys number header ciphertext tag ≠ .error .reservedBits := by
  intro h
  unfold decryptPayload at h
  split at h
  · obtain ⟨e, he⟩ := mapError_eq_error h
    cases he
  · split at h
    · obtain ⟨e, he⟩ := mapError_eq_error h
      cases he
    · cases h

/-- A reserved-bit error comes only from a packet that authenticates, RFC 9000 §§17.2, 17.3.1.

So a caller can treat it as a connection error without acting on unauthenticated bytes. -/
theorem unprotect_eq_reservedBits_iff (suite : CipherSuite) (keys : PacketKeys suite)
    (expected offset : Nat) (packet : ByteArray) :
    unprotect suite keys expected offset packet = .error .reservedBits ↔
      ∃ recovered number plaintext,
        removeHeaderProtection suite keys.hp offset packet = .ok recovered ∧
        reconstructNumber recovered.width recovered.truncatedNumber expected = .ok number ∧
        decryptPayload suite keys number recovered.header recovered.ciphertext recovered.tag =
          .ok plaintext ∧
        checkReservedBits recovered.header = .error .reservedBits := by
  constructor
  · intro h
    unfold unprotect at h
    cases hr : removeHeaderProtection suite keys.hp offset packet with
    | error e =>
      simp only [hr, bind, Except.bind] at h
      cases h
      exact absurd hr (removeHeaderProtection_ne _ _ _ _)
    | ok recovered =>
      simp only [hr, bind, Except.bind] at h
      cases hn : reconstructNumber recovered.width recovered.truncatedNumber expected with
      | error e =>
        simp only [hn] at h
        cases h
        exact absurd hn (reconstructNumber_ne _ _ _)
      | ok number =>
        simp only [hn] at h
        cases hd : decryptPayload suite keys number recovered.header recovered.ciphertext
            recovered.tag with
        | error e =>
          simp only [hd] at h
          cases h
          exact absurd hd (decryptPayload_ne _ _ _ _ _ _)
        | ok plaintext =>
          simp only [hd] at h
          cases hc : checkReservedBits recovered.header with
          | error e =>
            simp only [hc] at h
            cases h
            exact ⟨recovered, number, plaintext, rfl, hn, hd, hc⟩
          | ok u =>
            simp only [hc] at h
            cases hh : checkHeader suite recovered.header
                (recovered.ciphertext.size + recovered.tag.size) <;>
              simp [hh, Except.mapError, pure, Except.pure] at h
  · rintro ⟨recovered, number, plaintext, hr, hn, hd, hc⟩
    simp only [unprotect, bind, Except.bind, hr, hn, hd, hc]

end EthLib.Networking.Quic.Protection

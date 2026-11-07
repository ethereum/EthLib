module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Cryptography.Proofs.Aes.Ctr
public import EthLib.Cryptography.Proofs.Aes.Gcm
public import EthLib.Networking.Discv5.Packet

/-!
# `Networking.Proofs.Discv5.Packet`

Properties of the discv5 packet encoding.

- Masking twice under one key and IV gives the data back.
- The mask of a prefix is the prefix of the mask.
- The authdata of each flag decodes back from its bytes.
- A packet that the encoder writes, within the size limits, decodes back.
- Bytes decode to authdata or a packet exactly when they encode it and pass the decoder's checks.
- The additional data of a message is the masking IV and the unmasked bytes up to the message.
- A message that the encryption writes decrypts back.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Discv5.Packet

open EthLib.Networking.Discv5
open EthLib.Cryptography

/-! ## Masking -/

/-- A pairwise map with a list of at most `k` elements ignores the second list past `k`. -/
theorem zipWith_take_right {α β γ : Type} (f : α → β → γ) {k : Nat} :
    ∀ (l : List α) (l' : List β), l.length ≤ k → List.zipWith f l (l'.take k) = List.zipWith f l l'
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: l, b :: l', h => by
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at h; omega⟩
    simp only [List.take_succ_cons, List.zipWith_cons_cons]
    rw [zipWith_take_right f l l' (by simp at h; omega)]

/-- The key stream of a prefix is the prefix of the key stream. -/
theorem xorKeystream_take (ciph : Aes.Block → Aes.Block) (m n : Nat) (T : Aes.Block)
    (data : List UInt8) (k : Nat) :
    Aes.xorKeystream ciph m n T (data.take k) = (Aes.xorKeystream ciph m n T data).take k := by
  induction n generalizing T data k with
  | zero => simp [Aes.xorKeystream_zero]
  | succ n ih =>
    simp only [Aes.xorKeystream_succ, List.take_take, List.drop_take, ih, List.take_append,
      List.take_zipWith, List.length_zipWith, List.length_take, Vector.length_toList]
    rw [zipWith_take_right _ _ _ (by simp [List.length_take]; omega), Nat.min_comm k 16]
    congr 1
    by_cases hd : 16 ≤ data.length
    · rw [show min (min 16 data.length) 16 = 16 by omega]
    · have : data.drop 16 = [] := List.drop_eq_nil_of_le (by omega)
      simp [this, Aes.xorKeystream_nil]

/-- More blocks than the data needs change nothing. -/
theorem xorKeystream_add (ciph : Aes.Block → Aes.Block) (m n j : Nat) (T : Aes.Block)
    (data : List UInt8) (h : data.length ≤ 16 * n) :
    Aes.xorKeystream ciph m (n + j) T data = Aes.xorKeystream ciph m n T data := by
  induction n generalizing T data with
  | zero =>
    have : data = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [Aes.xorKeystream_nil]
  | succ n ih =>
    rw [show n + 1 + j = (n + j) + 1 by omega]
    simp only [Aes.xorKeystream_succ]
    rw [ih _ _ (by simp; omega)]

/-- Masking keeps the length of the data. -/
theorem length_mask (destId : NodeId) (iv : Vector UInt8 16) (data : List UInt8) :
    (mask destId iv data).length = data.length := by
  have := Aes.size_ctr (Aes.ciph .aes128 (maskingKey destId)) 128 iv ⟨data.toArray⟩
  simp only [mask, Array.length_toList]
  exact this

/-- Masking twice gives the data back. -/
theorem mask_mask (destId : NodeId) (iv : Vector UInt8 16) (data : List UInt8) :
    mask destId iv (mask destId iv data) = data := by
  have := Aes.ctr_ctr (Aes.ciph .aes128 (maskingKey destId)) 128 iv ⟨data.toArray⟩
  simp only [mask]
  rw [show ({ data := (Aes.ctr (Aes.ciph .aes128 (maskingKey destId)) 128 iv
    ⟨data.toArray⟩).data.toList.toArray } : ByteArray) =
    Aes.ctr (Aes.ciph .aes128 (maskingKey destId)) 128 iv ⟨data.toArray⟩ by simp, this]

/-- Masking a prefix gives the prefix of the masked data. -/
theorem mask_take (destId : NodeId) (iv : Vector UInt8 16) (data : List UInt8) (k : Nat) :
    mask destId iv (data.take k) = (mask destId iv data).take k := by
  simp only [mask, Aes.ctr, List.toList_toArray, List.size_toArray, ByteArray.size,
    List.length_take]
  -- Both sides use the blocks of the whole data, which cover the prefix too.
  have hn : (min k data.length + 15) / 16 + ((data.length + 15) / 16 -
      (min k data.length + 15) / 16) = (data.length + 15) / 16 := by
    have : (min k data.length + 15) / 16 ≤ (data.length + 15) / 16 :=
      Nat.div_le_div_right (by omega)
    omega
  have hmore := xorKeystream_add (Aes.ciph .aes128 (maskingKey destId)) 128
    ((min k data.length + 15) / 16)
    ((data.length + 15) / 16 - (min k data.length + 15) / 16) iv (data.take k)
    (by simp [List.length_take]; omega)
  rw [hn] at hmore
  rw [← hmore, xorKeystream_take]

/-! ## Authdata -/

/-- The bytes of a vector read back as the vector. -/
theorem vectorOf_toList {n : Nat} (v : Vector UInt8 n) :
    Authdata.vectorOf n v.toList = some v := by
  obtain ⟨a, h⟩ := v
  simp [Authdata.vectorOf, Vector.toList, h]

/-- The authdata of each flag decodes back from its bytes, when its sizes fit their fields. -/
theorem Authdata.decode_encode (a : Authdata) (h : a.fits = true) :
    Authdata.decode a.flag a.encode = .ok a := by
  cases a with
  | message srcId => simp [Authdata.decode, Authdata.flag, Authdata.encode, vectorOf_toList]
  | whoareyou idNonce enrSeq =>
    have hl : (Base.natToBytes 8 enrSeq.toNat).length = 8 := Base.natToBytes_length 8 _
    have hv : Base.bytesToNat (Base.natToBytes 8 enrSeq.toNat) = enrSeq.toNat :=
      Base.bytesToNat_natToBytes_of_lt (by have := enrSeq.toNat_lt; simpa using this)
    simp [Authdata.decode, Authdata.flag, Authdata.encode, List.take_left',
      List.drop_left', vectorOf_toList, hl, hv]
  | handshake srcId idSignature ephemeralPubkey record =>
    simp only [Authdata.fits, Bool.and_eq_true, decide_eq_true_eq] at h
    have hs : (UInt8.ofNat idSignature.size).toNat = idSignature.size :=
      UInt8.toNat_ofNat_of_lt' h.1
    have hk : (UInt8.ofNat ephemeralPubkey.size).toNat = ephemeralPubkey.size :=
      UInt8.toNat_ofNat_of_lt' h.2
    have hsl : idSignature.data.toList.length = idSignature.size := Array.length_toList
    have hkl : ephemeralPubkey.data.toList.length = ephemeralPubkey.size := Array.length_toList
    simp only [Authdata.decode, Authdata.flag, Authdata.encode, List.append_assoc,
      List.cons_append, List.nil_append]
    simp [List.take_left', List.drop_left', vectorOf_toList, hs, hk, hsl, hkl]
    rw [← List.drop_drop, List.drop_left' hsl, List.drop_left' hkl]

/-- A vector read from a list of bytes holds exactly those bytes. -/
theorem toList_of_vectorOf {n : Nat} {bytes : List UInt8} {v : Vector UInt8 n}
    (h : Authdata.vectorOf n bytes = some v) : v.toList = bytes := by
  unfold Authdata.vectorOf at h
  split at h
  · cases h
    simp [Vector.toList]
  · cases h

/-- Authdata that its bytes decode to has the flag it was read under, fits, and encodes back. -/
private theorem Authdata.encode_of_decode {flag : UInt8} {bytes : List UInt8} {a : Authdata}
    (h : Authdata.decode flag bytes = .ok a) :
    a.flag = flag ∧ a.fits = true ∧ a.encode = bytes := by
  unfold Authdata.decode at h
  split at h
  · rename_i h0
    split at h
    · rename_i srcId hv
      cases h
      exact ⟨h0.symm, rfl, toList_of_vectorOf hv⟩
    · cases h
  split at h
  · rename_i h1
    split at h
    · rename_i idNonce hv
      split at h
      · rename_i hl
        cases h
        -- The last 8 bytes are below 2^64, so they read back as the sequence number.
        have hd : (bytes.drop 16).length = 8 := by simp [hl]
        have hlt : Base.bytesToNat (bytes.drop 16) < 2 ^ 64 := by
          have := Base.bytesToNat_lt (bytes.drop 16)
          rw [hd] at this
          simpa using this
        refine ⟨h1.symm, rfl, ?_⟩
        simp only [Authdata.encode, toList_of_vectorOf hv, UInt64.toNat_ofNat',
          Nat.mod_eq_of_lt hlt]
        rw [← hd, Base.natToBytes_bytesToNat, List.take_append_drop]
      · cases h
    · cases h
  split at h
  · rename_i h2
    split at h
    · rename_i srcId sigSize keySize rest hv hrest
      split at h
      · rename_i hfit
        cases h
        have hs : (rest.take sigSize.toNat).length = sigSize.toNat := by
          simp only [List.length_take]; omega
        have hk : ((rest.drop sigSize.toNat).take keySize.toNat).length = keySize.toNat := by
          simp only [List.length_take, List.length_drop]; omega
        refine ⟨h2.symm, ?_, ?_⟩
        · simp only [Authdata.fits, ByteArray.size, List.size_toArray, hs, hk, Bool.and_eq_true,
            decide_eq_true_eq]
          exact ⟨sigSize.toNat_lt, keySize.toNat_lt⟩
        · simp only [Authdata.encode, ByteArray.size, List.size_toArray, hs, hk,
            UInt8.ofNat_toNat, toList_of_vectorOf hv]
          -- The bytes after the source ID are the two sizes, then the three fields in turn.
          conv => rhs; rw [← List.take_append_drop 32 bytes, hrest]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
      · cases h
    · cases h
  · cases h

/-- Bytes decode to authdata under a flag exactly when it has that flag and encodes to them.

The authdata must also fit its size fields. -/
theorem Authdata.decode_eq_ok_iff (flag : UInt8) (bytes : List UInt8) (a : Authdata) :
    Authdata.decode flag bytes = .ok a ↔ a.flag = flag ∧ a.fits = true ∧ a.encode = bytes := by
  refine ⟨Authdata.encode_of_decode, ?_⟩
  rintro ⟨rfl, hfits, rfl⟩
  exact Authdata.decode_encode a hfits

/-! ## Packets -/

/-- Unmasking the bytes after the IV of a packet starts with the header that was masked. -/
theorem mask_masked_append (destId : NodeId) (iv : Vector UInt8 16) (header rest : List UInt8) :
    mask destId iv (mask destId iv header ++ rest) =
      header ++ (mask destId iv (mask destId iv header ++ rest)).drop header.length := by
  conv => lhs; rw [← List.take_append_drop header.length (mask destId iv _)]
  rw [← mask_take, List.take_left' (length_mask destId iv header), mask_mask]

/-- A packet that the encoder writes decodes back, within the size limits of a packet.

A WHOAREYOU packet must also carry no message, as the decoder requires. -/
theorem Packet.decode_encode {destId : NodeId} {p : Packet} {bytes : ByteArray}
    (h : p.encode destId = .ok bytes) (hmin : MIN_PACKET_SIZE ≤ bytes.size)
    (hmax : bytes.size ≤ MAX_PACKET_SIZE)
    (hw : p.header.authdata.flag = 1 → p.message.size = 0) :
    Packet.decode destId bytes = .ok p := by
  obtain ⟨iv, ⟨nonce, a⟩, msg⟩ := p
  simp only at hw
  simp only [Packet.encode] at h
  cases hh : Header.encode ⟨nonce, a⟩ with
  | error e => simp [hh, bind, Except.bind] at h
  | ok hb =>
    simp only [hh, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    -- The header bytes, with the length of the authdata below 2^16.
    simp only [Header.encode] at hh
    split at hh
    case isFalse => cases hh
    case isTrue hfit =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfit
    obtain ⟨hL, hfits⟩ := hfit
    simp only [Except.ok.injEq] at hh
    subst hh
    -- Name the parts of the header.
    generalize hae : a.encode = ae at hL hmin hmax ⊢
    generalize hnb : Base.natToBytes 2 ae.length = nb at hmin hmax ⊢
    have hnbl : nb.length = 2 := by rw [← hnb]; exact Base.natToBytes_length 2 _
    have hnbv : Base.bytesToNat nb = ae.length := by
      rw [← hnb]; exact Base.bytesToNat_natToBytes_of_lt (by simpa using hL)
    have hnl : nonce.toList.length = 12 := by simp
    let pre : List UInt8 := [0x64, 0x69, 0x73, 0x63, 0x76, 0x35, 0x00, 0x01, a.flag]
    have hH : PROTOCOL_ID ++ VERSION ++ [a.flag] ++ nonce.toList ++ nb ++ ae =
        pre ++ (nonce.toList ++ (nb ++ ae)) := by
      simp [pre, PROTOCOL_ID, VERSION]
    rw [hH, List.append_assoc] at hmin hmax ⊢
    generalize hR : mask destId iv (pre ++ (nonce.toList ++ (nb ++ ae))) ++ msg.data.toList = R
      at hmin hmax ⊢
    have hRl : R.length = 23 + ae.length + msg.size := by
      have hm : msg.size = msg.data.size := rfl
      rw [← hR]
      simp only [List.length_append, length_mask, pre, List.length_cons, List.length_nil, hnl,
        hnbl, Array.length_toList]
      omega
    have hRdrop : R.drop (23 + ae.length) = msg.data.toList := by
      rw [← hR]
      refine List.drop_left' ?_
      simp only [List.length_append, length_mask, pre, List.length_cons, List.length_nil, hnl,
        hnbl]
      omega
    -- The unmasked bytes start with the header.
    have hplain := mask_masked_append destId iv (pre ++ (nonce.toList ++ (nb ++ ae)))
      msg.data.toList
    rw [hR] at hplain
    generalize (mask destId iv R).drop _ = X at hplain
    have h8 : (pre ++ (nonce.toList ++ (nb ++ ae)) ++ X).take 8 = PROTOCOL_ID ++ VERSION := by
      simp [pre, PROTOCOL_ID, VERSION]
    have hflag : (pre ++ (nonce.toList ++ (nb ++ ae)) ++ X)[8]? = some a.flag := by
      simp [pre]
    have h9 : (pre ++ (nonce.toList ++ (nb ++ ae)) ++ X).drop 9 =
        nonce.toList ++ (nb ++ (ae ++ X)) := by
      rw [List.append_assoc, List.drop_left' (by simp [pre])]; simp
    have hnonce : ((pre ++ (nonce.toList ++ (nb ++ ae)) ++ X).drop 9).take 12 = nonce.toList := by
      rw [h9, List.take_left' hnl]
    have h21 : (pre ++ (nonce.toList ++ (nb ++ ae)) ++ X).drop 21 = nb ++ (ae ++ X) := by
      rw [show 21 = 9 + 12 from rfl, ← List.drop_drop, h9, List.drop_left' hnl]
    have hsize : ((pre ++ (nonce.toList ++ (nb ++ ae)) ++ X).drop 21).take 2 = nb := by
      rw [h21, List.take_left' hnbl]
    have hauth : ((pre ++ (nonce.toList ++ (nb ++ ae)) ++ X).drop STATIC_HEADER_SIZE).take
        ae.length = ae := by
      rw [show STATIC_HEADER_SIZE = 21 + 2 from rfl, ← List.drop_drop, h21,
        List.drop_left' hnbl, List.take_left' rfl]
    have hdec : Authdata.decode a.flag ae = .ok a := hae ▸ Authdata.decode_encode a hfits
    -- Each check of the decoder passes, and each field reads back.
    have hsz : ¬ ((⟨(iv.toList ++ R).toArray⟩ : ByteArray).size < MIN_PACKET_SIZE ∨
        MAX_PACKET_SIZE < (⟨(iv.toList ++ R).toArray⟩ : ByteArray).size) := by omega
    have h16 : (iv.toList ++ R).take 16 = iv.toList := List.take_left' (by simp)
    have hd16 : (iv.toList ++ R).drop 16 = R := List.drop_left' (by simp)
    have hrest : ¬ R.length < STATIC_HEADER_SIZE + ae.length := by
      rw [hRl]; unfold STATIC_HEADER_SIZE; omega
    have hmsg : R.drop (STATIC_HEADER_SIZE + ae.length) = msg.data.toList := hRdrop
    have hwho : ¬ (a.flag = 1 ∧ msg.data.toList ≠ []) := by
      rintro ⟨h1, h2⟩
      apply h2
      exact List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; exact hw h1)
    simp only [Packet.decode, hsz, ite_false, h16, hd16, vectorOf_toList,
      hplain, h8, hflag, hnonce, hsize, hnbv, hauth, hdec, hrest, hmsg, hwho]
    simp only [ite_true, Array.toArray_toList]
    rfl

/-- The additional data of a message is the masking IV, then the unmasked bytes that follow it.

The unmasked part has the length of the additional data minus the 16 bytes of the masking IV. -/
theorem Packet.messageAd_eq {destId : NodeId} {p : Packet} {bytes ad : ByteArray}
    (he : p.encode destId = .ok bytes) (ha : p.messageAd = .ok ad) :
    ad.data.toList = bytes.data.toList.take 16 ++
      mask destId p.maskingIv ((bytes.data.toList.drop 16).take (ad.size - 16)) := by
  obtain ⟨iv, header, msg⟩ := p
  simp only [Packet.encode] at he
  simp only [Packet.messageAd] at ha
  cases hh : header.encode with
  | error e => simp [hh, bind, Except.bind] at ha
  | ok hb =>
    simp only [hh, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ha
    subst he ha
    have hlen := length_mask destId iv hb
    have hiv : iv.toList.length = 16 := by simp
    have hsize : (⟨(iv.toList ++ hb).toArray⟩ : ByteArray).size - 16 = hb.length := by
      simp [ByteArray.size, hiv]
    simp only [hsize]
    rw [List.append_assoc, List.take_left' hiv, List.drop_left' hiv, List.take_left' hlen,
      mask_mask]

/-- The additional data of a message and the message fill the whole packet.

So the unmasked part of the additional data ends where the message starts. -/
theorem Packet.size_messageAd_add {destId : NodeId} {p : Packet} {bytes ad : ByteArray}
    (he : p.encode destId = .ok bytes) (ha : p.messageAd = .ok ad) :
    ad.size + p.message.size = bytes.size := by
  obtain ⟨iv, header, msg⟩ := p
  simp only [Packet.encode] at he
  simp only [Packet.messageAd] at ha
  cases hh : header.encode with
  | error e => simp [hh, bind, Except.bind] at ha
  | ok hb =>
    simp only [hh, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he ha
    subst he ha
    simp only [ByteArray.size, List.size_toArray, List.length_append, length_mask,
      Array.length_toList]

/-- Bytes that decode to a packet are its encoding, and they pass the checks of the decoder.

The checks are the size limits, and a WHOAREYOU packet with no message. -/
private theorem Packet.encode_and_checks_of_decode {destId : NodeId} {bytes : ByteArray}
    {p : Packet} (h : Packet.decode destId bytes = .ok p) :
    p.encode destId = .ok bytes ∧ MIN_PACKET_SIZE ≤ bytes.size ∧ bytes.size ≤ MAX_PACKET_SIZE ∧
      (p.header.authdata.flag = 1 → p.message.size = 0) := by
  unfold Packet.decode at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  rename_i hsize
  split at h
  case h_2 => cases h
  rename_i iv hiv
  split at h
  case isFalse => cases h
  rename_i hprotocol
  split at h
  case h_2 => cases h
  rename_i flag hflag
  split at h
  case h_2 => cases h
  rename_i nonce hnonce
  split at h
  case isTrue => cases h
  rename_i hlength
  split at h
  case h_1 => cases h
  rename_i a ha
  split at h
  case isTrue => cases h
  rename_i hwho
  cases h
  -- Name the bytes after the IV, their unmasked form and the size of the authdata.
  generalize hR : bytes.data.toList.drop 16 = R at *
  generalize hP : mask destId iv R = P at *
  generalize hL : Base.bytesToNat ((P.drop 21).take 2) = L at *
  unfold STATIC_HEADER_SIZE at *
  have hPl : P.length = R.length := by rw [← hP, length_mask]
  obtain ⟨hflagEq, hfits, hae⟩ := Authdata.encode_of_decode ha
  -- The size field has two bytes, so the authdata has fewer than 2^16 bytes.
  have hsizeBytes : ((P.drop 21).take 2).length = 2 := by simp; omega
  have hLlt : L < 2 ^ 16 := by
    have := Base.bytesToNat_lt ((P.drop 21).take 2)
    rw [hsizeBytes] at this
    omega
  have hael : a.encode.length = L := by rw [hae]; simp; omega
  have hsizeField : Base.natToBytes 2 a.encode.length = (P.drop 21).take 2 := by
    have := Base.natToBytes_bytesToNat ((P.drop 21).take 2)
    rwa [hsizeBytes, hL, ← hael] at this
  -- The unmasked header is the first `23 + L` bytes of the unmasked data.
  have h8 : 8 < P.length := by omega
  have hPflag : P[8] = flag := (List.getElem?_eq_some_iff.mp hflag).2
  have hheader : PROTOCOL_ID ++ VERSION ++ [a.flag] ++ nonce.toList ++
      Base.natToBytes 2 a.encode.length ++ a.encode = P.take (23 + L) := by
    rw [show 23 + L = 8 + (1 + (12 + (2 + L))) by omega, List.take_add, List.take_add,
      List.take_add, List.take_add, ← hprotocol, hflagEq, toList_of_vectorOf hnonce, hsizeField,
      hae, List.drop_eq_getElem_cons h8, hPflag]
    simp only [List.drop_drop, List.take_succ_cons, List.take_zero, List.append_assoc,
      List.cons_append, List.nil_append, List.drop_succ_cons]
  have hencode : Header.encode ⟨nonce, a⟩ = .ok (P.take (23 + L)) := by
    rw [← hheader]
    simp [Header.encode, hael, hLlt, hfits]
  -- Masking the header again gives the bytes of the packet before the message.
  have hmasked : mask destId iv (P.take (23 + L)) = R.take (23 + L) := by
    rw [mask_take, ← hP, mask_mask]
  refine ⟨?_, by omega, by omega, fun hone => ?_⟩
  · simp only [Packet.encode, hencode, hmasked, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq]
    rw [toList_of_vectorOf hiv, List.append_assoc, List.take_append_drop, ← hR,
      List.take_append_drop]
  -- A WHOAREYOU packet passed the check that its message is empty.
  · have hempty : R.drop (23 + L) = [] :=
      Classical.byContradiction fun hne => hwho ⟨by rw [← hflagEq]; exact hone, hne⟩
    simp [ByteArray.size, hempty]

/-- Bytes that decode to a packet are the encoding of that packet. -/
theorem Packet.encode_of_decode {destId : NodeId} {bytes : ByteArray} {p : Packet}
    (h : Packet.decode destId bytes = .ok p) : p.encode destId = .ok bytes :=
  (Packet.encode_and_checks_of_decode h).1

/-- Bytes decode to a packet exactly when they are its encoding and pass the checks.

The checks are the size limits, and a WHOAREYOU packet with no message. -/
theorem Packet.decode_eq_ok_iff (destId : NodeId) (bytes : ByteArray) (p : Packet) :
    Packet.decode destId bytes = .ok p ↔
      p.encode destId = .ok bytes ∧ MIN_PACKET_SIZE ≤ bytes.size ∧
        bytes.size ≤ MAX_PACKET_SIZE ∧ (p.header.authdata.flag = 1 → p.message.size = 0) :=
  ⟨Packet.encode_and_checks_of_decode,
    fun ⟨he, hmin, hmax, hw⟩ => Packet.decode_encode he hmin hmax hw⟩

/-! ## Messages -/

/-- The 16 bytes of the GCM tag are a tag length of SP 800-38D. -/
theorem tagSize_mem : TAG_SIZE ∈ Aes.Gcm.tagLengths := by decide

/-- A message that the encryption writes decrypts back to its plaintext. -/
theorem decryptMessage_encryptMessage {key : Aes.Key .aes128} {nonce : Vector UInt8 12}
    {plaintext ad message : ByteArray} (h : encryptMessage key nonce plaintext ad = .ok message) :
    decryptMessage key nonce message ad = .ok plaintext := by
  unfold encryptMessage at h
  cases he : Aes.Gcm.encrypt (Aes.ciph .aes128 key) TAG_SIZE ⟨nonce.toArray⟩ plaintext ad with
  | error e => simp [he, bind, Except.bind] at h
  | ok ct =>
    obtain ⟨c, T⟩ := ct
    simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    -- The tag has 16 bytes, so the split before the last 16 bytes finds the ciphertext.
    have hT : T.size = TAG_SIZE := by
      unfold Aes.Gcm.encrypt at he
      cases hc : Aes.Gcm.checkLengths TAG_SIZE ⟨nonce.toArray⟩ plaintext ad with
      | error e => simp [hc, bind, Except.bind] at he
      | ok u =>
        simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at he
        rw [← he.2]
        exact Aes.Gcm.size_tag _ tagSize_mem _ _ _ _
    have hn : (c ++ T).size - TAG_SIZE = c.size := by rw [ByteArray.size_append, hT]; omega
    unfold decryptMessage
    simp only [hn]
    rw [ByteArray.extract_append_eq_left rfl,
      ByteArray.extract_append_eq_right rfl (by rw [ByteArray.size_append])]
    exact Aes.Gcm.decrypt_encrypt _ _ _ _ _ _ _ he

/-! ## Error codes -/

section

open EthLib.Networking.Discv5

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Discv5.PacketError.code_injective
    (e₁ e₂ : PacketError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [PacketError.code] at h; exact absurd h (by decide))

end

end EthLib.Networking.Proofs.Discv5.Packet

module

public import EthLib.Networking.Rlpx.Ecies
public import EthLib.Cryptography.Proofs.Aes.Ctr
public import EthLib.Cryptography.Proofs.Hash.ConcatKdf
public import EthLib.Cryptography.Proofs.Hash.Hmac
public import EthLib.Cryptography.Proofs.Secp256k1.Ecdh
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding

/-!
# Proofs: ECIES encryption

The recipient decrypts every ciphertext to its message, for every nonzero ephemeral key.

A ciphertext with any other tag is rejected.

A ciphertext that decrypts starts with an uncompressed key that lies on the curve and is not `O`.
-/

@[expose] public section

namespace EthLib.Networking.Rlpx.Ecies

open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1
open EthLib.Cryptography.Secp256k1.Point

/-- A successful encryption is `R || iv || c || d`, from one shared secret and its keys. -/
theorem encrypt_eq_ok {recipient : Point} {ephemeral : Fn} {iv : Aes.Block}
    {sharedMac m c : ByteArray} (h : encrypt recipient ephemeral iv sharedMac m = .ok c) :
    ∃ secret encKey macKey, ecdh ephemeral recipient = .ok secret ∧
      deriveKeys secret = .ok (encKey, macKey) ∧
      c = (mul ephemeral generator).encodeUncompressed ++ ⟨iv.toArray⟩ ++ cipher encKey iv m ++
        tag macKey iv (cipher encKey iv m) sharedMac := by
  unfold encrypt at h
  cases hs : ecdh ephemeral recipient with
  | error e => simp [hs, Except.mapError, bind, Except.bind] at h
  | ok secret =>
    cases hk : deriveKeys secret with
    | error e => simp [hs, hk, Except.mapError, bind, Except.bind] at h
    | ok keys =>
      rcases keys with ⟨encKey, macKey⟩
      simp only [hs, hk, Except.mapError, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at h
      exact ⟨secret, encKey, macKey, rfl, hk, h.symm⟩

/-- The four parts of `a ++ b ++ c ++ d`, cut at the sizes of `R`, `iv` and `d`. -/
theorem split_parts {α : Type} (a b c d : List α) (ha : a.length = EPHEMERAL_KEY_SIZE)
    (hb : b.length = IV_SIZE) (hd : d.length = TAG_SIZE) :
    (a ++ b ++ c ++ d).take EPHEMERAL_KEY_SIZE = a ∧
      ((a ++ b ++ c ++ d).drop EPHEMERAL_KEY_SIZE).take IV_SIZE = b ∧
      ((a ++ b ++ c ++ d).drop (EPHEMERAL_KEY_SIZE + IV_SIZE)).take
        ((a ++ b ++ c ++ d).length - OVERHEAD) = c ∧
      (a ++ b ++ c ++ d).drop ((a ++ b ++ c ++ d).length - TAG_SIZE) = d := by
  simp only [EPHEMERAL_KEY_SIZE, IV_SIZE, TAG_SIZE, OVERHEAD] at *
  have hlen : (a ++ b ++ c ++ d).length = 65 + 16 + c.length + 32 := by
    simp [ha, hb, hd]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ha]
  · simp [ha, hb]
  · rw [hlen, show a ++ b ++ c ++ d = (a ++ b) ++ (c ++ d) by simp,
      List.drop_left' (by simp [ha, hb]), List.take_left' (by omega)]
  · rw [hlen, List.drop_left' (by simp [ha, hb]; omega)]

/-- The tag is one HMAC-SHA-256 output, 32 bytes. -/
theorem size_tag (macKey : ByteArray) (iv : Aes.Block) (c sharedMac : ByteArray) :
    (tag macKey iv c sharedMac).size = TAG_SIZE :=
  Hash.Hmac.hmac_size _ _

/--
How the recipient reads `R || iv || c || d`, for a point `R` other than `O`.

Once the key agreement and the key derivation succeed, only the tag decides.
-/
theorem decrypt_eq {key : Fn} {p : Point} (hp : p.isOnCurve = true) (hinf : p ≠ .infinity)
    {secret : Vector UInt8 32} {encKey : Aes.Key .aes128} {macKey : ByteArray}
    (hs : ecdh key p = .ok secret) (hk : deriveKeys secret = .ok (encKey, macKey))
    (iv : Aes.Block) (c d sharedMac : ByteArray) (hd : d.size = TAG_SIZE) :
    decrypt key sharedMac (p.encodeUncompressed ++ ⟨iv.toArray⟩ ++ c ++ d) =
      if d = tag macKey iv c sharedMac then .ok (cipher encKey iv c) else .error .tagMismatch := by
  have hR : p.encodeUncompressed.data.toList.length = EPHEMERAL_KEY_SIZE := by
    cases p with
    | infinity => exact absurd rfl hinf
    | affine x y => exact size_encodeUncompressed x y
  have hiv : iv.toArray.toList.length = IV_SIZE := by simp [IV_SIZE]
  have hd' : d.data.toList.length = TAG_SIZE := hd
  obtain ⟨h1, h2, h3, h4⟩ := split_parts _ _ c.data.toList _ hR hiv hd'
  have hlong : ¬ (p.encodeUncompressed.data.toList ++ iv.toArray.toList ++ c.data.toList ++
      d.data.toList).length < OVERHEAD := by
    simp only [List.length_append, hR, hiv, hd', OVERHEAD]; omega
  have hdec : Point.decode ⟨(p.encodeUncompressed.data.toList).toArray⟩ = .ok p := by
    simpa using decode_encodeUncompressed hp hinf
  unfold decrypt
  simp only [ByteArray.data_append, Array.toList_append]
  rw [dite_eq_right_of_eq_false (eq_false hlong)]
  simp only [h1, h2, h3, h4, hdec, hs, hk, Except.mapError, bind, Except.bind,
    Array.toArray_toList]
  -- Two byte arrays are equal when their lists of bytes are.
  have hbytes (a b : ByteArray) : (a.data.toList = b.data.toList) = (a = b) := by
    rw [Array.toList_inj]
    exact propext ⟨fun h => by cases a; cases b; cases h; rfl, fun h => by rw [h]⟩
  simp only [hbytes]

/-- The key derivation succeeds for every shared secret. -/
theorem exists_deriveKeys_eq_ok (secret : Vector UInt8 32) :
    ∃ keys, deriveKeys secret = .ok keys := by
  have hsize : (ByteArray.mk secret.toArray).size = 32 := by simp [ByteArray.size]
  simp [deriveKeys, Hash.ConcatKdf.concatKdf, Hash.ConcatKdf.HASH_LEN, hsize, Except.mapError,
    bind, Except.bind, pure, Except.pure]

/-- The derived keys are the two halves of the 32-byte KDF output.

`k_E` is the first 16 bytes, and `k_M` is the last 16. -/
theorem deriveKeys_eq_ok_iff (secret : Vector UInt8 32) (encKey : Aes.Key .aes128)
    (macKey : ByteArray) :
    deriveKeys secret = .ok (encKey, macKey) ↔
      ∃ keys, Hash.ConcatKdf.concatKdf ⟨secret.toArray⟩ .empty 32 = .ok keys ∧
        ByteArray.mk encKey.toArray = keys.extract 0 16 ∧ macKey = keys.extract 16 32 := by
  cases hk : Hash.ConcatKdf.concatKdf ⟨secret.toArray⟩ .empty 32 with
  | error e => simp [deriveKeys, hk, Except.mapError, bind, Except.bind]
  | ok keys =>
    have hsize := Hash.ConcatKdf.concatKdf_size hk
    -- The first 16 bytes, read one at a time, are the first 16 bytes of the output.
    have hfirst : ByteArray.mk (Vector.ofFn fun i : Fin 16 => keys.data.getD i.val 0).toArray =
        keys.extract 0 16 := by
      apply ByteArray.ext
      apply Array.ext
      · simp [ByteArray.data_extract, hsize]
      · intro i h₁ h₂
        simp only [Vector.toArray_ofFn, Array.size_ofFn] at h₁
        have hi : i < keys.data.size := by
          change i < keys.size
          omega
        simp only [Vector.toArray_ofFn, Array.getElem_ofFn, ByteArray.data_extract,
          Array.getElem_extract, Nat.zero_add, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem hi, Option.getD_some]
    simp only [deriveKeys, hk, Except.mapError, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq, exists_eq_left', ← hfirst]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨h₁, rfl⟩
      refine ⟨Vector.toArray_inj.mp ?_, rfl⟩
      exact (congrArg ByteArray.data h₁).symm

/-- Encryption to a nonzero private key succeeds for every nonzero ephemeral key. -/
theorem exists_encrypt_eq_ok {key ephemeral : Fn} (hk : key ≠ 0) (hr : ephemeral ≠ 0)
    (iv : Aes.Block) (sharedMac m : ByteArray) :
    ∃ c, encrypt (mul key generator) ephemeral iv sharedMac m = .ok c := by
  obtain ⟨secret, hs⟩ := exists_ecdh_eq_ok hr hk
  obtain ⟨⟨encKey, macKey⟩, hkeys⟩ := exists_deriveKeys_eq_ok secret
  simp [encrypt, hs, hkeys, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- The ephemeral point `R` of a successful encryption is a point of the curve other than `O`. -/
theorem ephemeral_ne_infinity {key ephemeral : Fn} {secret : Vector UInt8 32}
    (hs : ecdh ephemeral (mul key generator) = .ok secret) :
    mul ephemeral generator ≠ .infinity := by
  intro h
  rw [← ecdh_comm, h] at hs
  simp [ecdh] at hs

/--
The recipient decrypts every ciphertext to its message.

The encryption succeeds for every nonzero ephemeral key, by the theorem above.
-/
theorem decrypt_encrypt {key ephemeral : Fn} {iv : Aes.Block} {sharedMac m c : ByteArray}
    (h : encrypt (mul key generator) ephemeral iv sharedMac m = .ok c) :
    decrypt key sharedMac c = .ok m := by
  obtain ⟨secret, encKey, macKey, hs, hkeys, rfl⟩ := encrypt_eq_ok h
  have hinf := ephemeral_ne_infinity hs
  rw [decrypt_eq (isOnCurve_mul _ isOnCurve_generator) hinf ((ecdh_comm _ _).trans hs) hkeys
    _ _ _ _ (size_tag _ _ _ _)]
  simp [cipher, Aes.ctr_ctr]

/--
A ciphertext with its tag replaced by any other 32 bytes is rejected.

Here `body` is `R || iv || c`, and `d` is the tag of the encryption.
-/
theorem decrypt_wrong_tag {key ephemeral : Fn} {iv : Aes.Block} {sharedMac m body d : ByteArray}
    (h : encrypt (mul key generator) ephemeral iv sharedMac m = .ok (body ++ d))
    (hd : d.size = TAG_SIZE) {d' : ByteArray} (hd' : d'.size = TAG_SIZE) (hne : d' ≠ d) :
    decrypt key sharedMac (body ++ d') = .error .tagMismatch := by
  obtain ⟨secret, encKey, macKey, hs, hkeys, hc⟩ := encrypt_eq_ok h
  -- The last 32 bytes of the ciphertext are the tag, and the bytes before them are the body.
  have hl := congrArg (fun b : ByteArray => b.data.toList) hc
  simp only [ByteArray.data_append, Array.toList_append] at hl
  obtain ⟨hbody, htag⟩ := List.append_inj' hl (by
    have := size_tag macKey iv (cipher encKey iv m) sharedMac
    simp only [ByteArray.size, Array.length_toList] at hd this ⊢; omega)
  have hbody : body = (mul ephemeral generator).encodeUncompressed ++ ⟨iv.toArray⟩ ++
      cipher encKey iv m :=
    ByteArray.ext (Array.toList_inj.mp (by simpa using hbody))
  have hne' : d' ≠ tag macKey iv (cipher encKey iv m) sharedMac := by
    rw [← ByteArray.ext (Array.toList_inj.mp htag)]; exact hne
  rw [hbody, decrypt_eq (isOnCurve_mul _ isOnCurve_generator) (ephemeral_ne_infinity hs)
    ((ecdh_comm _ _).trans hs) hkeys _ _ _ _ hd']
  simp [hne']

/-- A ciphertext is its message and the 113 bytes of `R`, `iv` and `d`. -/
theorem size_encrypt {key ephemeral : Fn} {iv : Aes.Block} {sharedMac m c : ByteArray}
    (h : encrypt (mul key generator) ephemeral iv sharedMac m = .ok c) :
    c.size = m.size + OVERHEAD := by
  obtain ⟨secret, encKey, macKey, hs, -, rfl⟩ := encrypt_eq_ok h
  have hR : (mul ephemeral generator).encodeUncompressed.size = EPHEMERAL_KEY_SIZE := by
    cases hm : mul ephemeral generator with
    | infinity => exact absurd hm (ephemeral_ne_infinity hs)
    | affine x y => exact size_encodeUncompressed x y
  have hiv : (⟨iv.toArray⟩ : ByteArray).size = IV_SIZE := by simp [ByteArray.size, IV_SIZE]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, hR, hiv, size_tag,
    cipher, Aes.size_ctr]
  simp only [OVERHEAD]
  omega

/-- A decrypted ciphertext starts with the uncompressed bytes of a key `R`.

`R` lies on the curve and is not `O`. -/
theorem ephemeral_of_decrypt_eq_ok {key : Fn} {sharedMac ciphertext m : ByteArray}
    (h : decrypt key sharedMac ciphertext = .ok m) :
    ∃ R : Point, R.isOnCurve = true ∧ R ≠ .infinity ∧
      ⟨(ciphertext.data.toList.take EPHEMERAL_KEY_SIZE).toArray⟩ = R.encodeUncompressed := by
  unfold decrypt at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hlong
    cases hd : Point.decode ⟨(ciphertext.data.toList.take EPHEMERAL_KEY_SIZE).toArray⟩ with
    | error e => simp [hd, Except.mapError, bind, Except.bind] at h
    | ok R =>
      cases hs : ecdh key R with
      | error e => simp [hd, hs, Except.mapError, bind, Except.bind] at h
      | ok secret =>
        obtain ⟨hon, hinf, hform⟩ := (Point.decode_eq_ok_iff _ _).mp hd
        refine ⟨R, hon, hinf, ?_⟩
        rcases hform with hcomp | hunc
        · cases R with
          | infinity => exact absurd rfl hinf
          | affine x y =>
            have hsize := congrArg ByteArray.size hcomp
            rw [size_encodeCompressed] at hsize
            simp only [ByteArray.size, List.size_toArray, List.length_take] at hsize
            simp only [OVERHEAD, EPHEMERAL_KEY_SIZE, IV_SIZE, TAG_SIZE] at hlong hsize
            omega
        · exact hunc

/-! ## Error codes -/

section

open EthLib.Networking.Rlpx.Ecies

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Rlpx.Ecies.EciesError.code_injective
    (e₁ e₂ : EciesError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [EciesError.code] at h; exact absurd h (by decide))

/-- Every code of an ECIES error is from 1 to 5. -/
theorem _root_.EthLib.Networking.Rlpx.Ecies.EciesError.code_le (e : EciesError) :
    1 ≤ e.code.toNat ∧ e.code.toNat ≤ 5 := by
  cases e <;> simp only [EciesError.code] <;> decide

end

end EthLib.Networking.Rlpx.Ecies

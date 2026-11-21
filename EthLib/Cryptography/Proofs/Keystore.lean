module

public import EthLib.Base.Proofs.ByteList
public import EthLib.Base.Proofs.Bytes
public import EthLib.Base.Proofs.Hex
public import EthLib.Base.Proofs.Json
public import EthLib.Base.Proofs.MapM
public import EthLib.Cryptography.Keystore
public import EthLib.Cryptography.Proofs.Aes.Ctr
public import EthLib.Cryptography.Proofs.Bls.KeyPath
public import EthLib.Cryptography.Proofs.Hash.Pbkdf2
public import EthLib.Cryptography.Proofs.Hash.Scrypt
public import EthLib.Cryptography.Proofs.Hash.Sha256

/-!
# Proofs: ERC-2335 decryption

A mismatched checksum prevents secret decryption.

A key derivation beyond the caller's limits gives the limit error.

Verification accepts exactly a key of at least 32 bytes whose checksum matches the ciphertext.

A successful derivation gives at least 32 bytes, so verification never refuses its key as too short.

Decryption returns as many bytes as the ciphertext holds.

AES-128-CTR undoes itself: decrypting the secret under its own checksum gives back the ciphertext.

The prepared password bytes encode the NFKD form of the password, in order, less its control codes.

A password already in NFKD form and free of control codes prepares to its own UTF-8 bytes.

A well-formed key derivation other than PBKDF2 and scrypt is refused before any parameter is read.

A store of a version other than 4 is refused before any other field is read.

A UUID written in its text form reads back as itself.

A keystore that encryption writes reads back with its key derivation, its IV and its metadata.

Decrypting it with the same password, under limits that admit its key derivation, gives the secret.

A keystore written with the public key of its secret passes the public key check.

A keystore without a public key fails that check.
-/

@[expose] public section

namespace EthLib.Cryptography.Keystore

/-- Comparing 32-byte checksums gives the same mismatch result as comparing their bytes. -/
theorem passwordChecksum_bne_eq (key message : ByteArray) (checksum : Vector UInt8 32) :
    (passwordChecksum key message != checksum) =
      (Hash.Sha256.hash (key.extract 16 32 ++ message) != Base.packBytes checksum) := by
  change (!(passwordChecksum key message == checksum)) =
    !((passwordChecksum key message).toArray == checksum.toArray)
  rw [Vector.toArray_beq_toArray]

/-- A short intermediate key is refused before either cryptographic step reads it. -/
theorem decryptWithKey_of_short (store : Store) (key : ByteArray) (h : key.size < 32) :
    decryptWithKey store key = .error (.shortKey key.size) := by
  simp [decryptWithKey, Nat.not_le.mpr h]
  rfl

/-- A checksum mismatch prevents the AES step. -/
theorem decryptWithKey_of_checksum_mismatch (store : Store) (key : ByteArray)
    (hsize : 32 ≤ key.size)
    (hcheck : (passwordChecksum key store.message != store.checksum) = true) :
    decryptWithKey store key = .error .checksumMismatch := by
  simp [decryptWithKey, hsize, hcheck]
  rfl

/-- A key derivation beyond the limits gives the limit error, for any checksum and ciphertext. -/
theorem decryptStore_of_not_admits (limits : KdfLimits) (store : Store) (password : String)
    (h : limits.admits (passwordBytes password).size store.kdf = false) :
    decryptStore limits store password =
      .error (.limitExceeded store.kdf.memory (store.kdf.work (passwordBytes password).size)) := by
  simp [decryptStore, h]
  rfl

/-! ## What verification accepts -/

/-- A key of at least 32 bytes whose checksum matches the ciphertext passes verification.

With the short-key and checksum refusals, nothing else stops the AES step of this function.
-/
theorem exists_decryptWithKey_eq_ok (store : Store) (key : ByteArray)
    (hsize : 32 ≤ key.size)
    (hcheck : (passwordChecksum key store.message != store.checksum) = false) :
    ∃ secret, decryptWithKey store key = .ok secret := by
  simp [decryptWithKey, hsize, hcheck]
  exact ⟨_, rfl⟩

/-- A successful verification read a key of at least 32 bytes and a matching checksum. -/
theorem decryptWithKey_ok_inv {store : Store} {key secret : ByteArray}
    (h : decryptWithKey store key = .ok secret) :
    32 ≤ key.size ∧
      (passwordChecksum key store.message != store.checksum) = false := by
  by_cases hsize : 32 ≤ key.size
  · refine ⟨hsize, ?_⟩
    by_cases hcheck : (passwordChecksum key store.message != store.checksum) = true
    · rw [decryptWithKey_of_checksum_mismatch store key hsize hcheck] at h
      nomatch h
    · simpa using hcheck
  · rw [decryptWithKey_of_short store key (Nat.lt_of_not_le hsize)] at h
    nomatch h

/-- Verification accepts exactly a key of at least 32 bytes whose checksum matches. -/
theorem exists_decryptWithKey_eq_ok_iff (store : Store) (key : ByteArray) :
    (∃ secret, decryptWithKey store key = .ok secret) ↔
      32 ≤ key.size ∧
        (passwordChecksum key store.message != store.checksum) = false :=
  ⟨fun ⟨_, h⟩ => decryptWithKey_ok_inv h,
    fun ⟨hsize, hcheck⟩ => exists_decryptWithKey_eq_ok store key hsize hcheck⟩

/-- Decryption returns as many bytes as the ciphertext holds.

It neither pads the secret nor cuts it to a key length.
-/
theorem decryptWithKey_size {store : Store} {key secret : ByteArray}
    (h : decryptWithKey store key = .ok secret) : secret.size = store.message.size := by
  obtain ⟨hsize, hcheck⟩ := decryptWithKey_ok_inv h
  simp [decryptWithKey, hsize, hcheck] at h
  simp only [Pure.pure, Except.pure] at h
  obtain rfl := Except.ok.inj h
  exact Aes.size_ctr _ _ _ _

/-! ## The derived key is long enough -/

/-- A successful derivation gives at least the 32 bytes that password verification reads.

PBKDF2 and scrypt return exactly the requested length, and one below 32 bytes is refused first.
-/
theorem le_size_of_deriveKey {password key : ByteArray} {kdf : Kdf}
    (h : deriveKey password kdf = .ok key) : 32 ≤ key.size := by
  unfold deriveKey at h
  split at h <;> split at h
  · nomatch h
  · rw [Base.mapError_ok_iff] at h
    rw [Hash.Pbkdf2.pbkdf2_size h]
    omega
  · nomatch h
  · rw [Base.mapError_ok_iff] at h
    rw [Hash.Scrypt.scrypt_size h]
    omega

/-- Password verification never refuses a derived key as too short.

So a short-key error never reports the size of a key that derivation produced.
-/
theorem decryptWithKey_ne_shortKey_of_deriveKey {password key : ByteArray} {kdf : Kdf}
    (hkey : deriveKey password kdf = .ok key) (store : Store) (size : Nat) :
    decryptWithKey store key ≠ .error (.shortKey size) := by
  by_cases hcheck : (passwordChecksum key store.message != store.checksum) = true
  · rw [decryptWithKey_of_checksum_mismatch store key (le_size_of_deriveKey hkey) hcheck]
    simp
  · obtain ⟨secret, hok⟩ :=
      exists_decryptWithKey_eq_ok store key (le_size_of_deriveKey hkey) (by simpa using hcheck)
    rw [hok]
    simp

/-! ## CTR undoes itself -/

/-- Encrypting the decrypted secret again gives back the stored ciphertext.

The AES step is CTR under one key and counter, and CTR is its own inverse.

The second store holds the checksum of the secret, so its verification passes.
-/
theorem decryptWithKey_decryptWithKey {store : Store} {key secret : ByteArray}
    (h : decryptWithKey store key = .ok secret) :
    decryptWithKey { store with message := secret, checksum := passwordChecksum key secret } key =
      .ok store.message := by
  obtain ⟨hsize, hmatch⟩ := decryptWithKey_ok_inv h
  simp [decryptWithKey, hsize, hmatch] at h
  simp only [Pure.pure, Except.pure] at h
  obtain rfl := Except.ok.inj h
  simp [decryptWithKey, hsize, Aes.ctr_ctr]
  rfl

/-! ## The password that the reader prepares -/

/-- The prepared bytes are the UTF-8 encoding of a subsequence of the NFKD form of the password.

That subsequence holds no control code of ERC-2335, "Password requirements".

It keeps every other character as often as the NFKD form holds it.

These three facts determine the prepared string. -/
theorem exists_passwordBytes_eq_toUTF8 (password : String) :
    ∃ prepared : String, passwordBytes password = prepared.toUTF8 ∧
      prepared.toList.Sublist (Base.Unicode.nfkd password).toList ∧
      (∀ c ∈ prepared.toList, isControl c = false) ∧
      ∀ c, isControl c = false →
        prepared.toList.count c = (Base.Unicode.nfkd password).toList.count c := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [String.toList_ofList]
    exact List.filter_sublist
  · intro c hc
    rw [String.toList_ofList] at hc
    simpa using (List.mem_filter.mp hc).2
  · intro c hc
    rw [String.toList_ofList]
    exact List.count_filter (by simp [hc])

/-- A password already in NFKD form and free of control codes prepares to its own UTF-8 bytes. -/
theorem passwordBytes_eq_toUTF8 {password : String}
    (hn : Base.Unicode.nfkd password = password)
    (hc : ∀ c ∈ password.toList, isControl c = false) :
    passwordBytes password = password.toUTF8 := by
  unfold passwordBytes
  rw [hn, List.filter_eq_self.mpr (by simpa using hc), String.ofList_toList]

/-! ## What the reader refuses -/

/-- A well-formed key derivation other than PBKDF2 and scrypt is refused as unsupported.

No field of its parameters is read, so an unsupported function is reported before any of them. -/
theorem readKdf_eq_error_of_unsupported {value : Lean.Json} {name : String}
    {params message : Lean.Json}
    (h : moduleFields "kdf" value = .ok (name, params, message))
    (hp : name ≠ "pbkdf2") (hs : name ≠ "scrypt") :
    readKdf value = .error (.unsupportedFunction "kdf" name) := by
  simp [readKdf, h, hp, hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A store of a version other than 4 is refused before any other field is read.

ERC-2335 fixes the version at 4 under "Version". -/
theorem readStore_eq_error_of_version_ne {value json : Lean.Json} {version : Nat}
    (hf : field "keystore" value "version" = .ok json)
    (hn : number "version" json = .ok version) (hv : version ≠ 4) :
    readStore value = .error (.unsupportedVersion version) := by
  simp [readStore, hf, hn, hv, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-! ## Writing a keystore -/

/-- A string reads as its own text. -/
theorem string_str (what text : String) : string what (.str text) = .ok text := by
  rw [string, Base.Toolchain.Json.getStr?_eq]
  rfl

/-- Bytes written as hex digits read back as themselves. -/
theorem bytes_hexText (what : String) (data : List UInt8) :
    bytes what (.str (hexText data)) = .ok ⟨data.toArray⟩ := by
  -- Two digits per byte, so the number of digits is even.
  have even : (data.flatMap Base.byteHexDigits).length = 2 * data.length := by
    induction data with
    | nil => rfl
    | cons byte rest ih =>
      simp only [List.flatMap_cons, List.length_append, ih]
      simp only [Base.byteHexDigits, List.length_cons, List.length_nil]
      omega
  simp only [bytes, string_str, hexText, bind, Except.bind, String.toList_ofList, even,
    Nat.mul_mod_right, Base.hexBytes?_flatMap]
  rfl

/-- Bytes of a fixed size written as hex digits read back as themselves. -/
theorem fixed_hexText (what : String) {n : Nat} (data : Vector UInt8 n) :
    fixed what n (.str (hexText data.toList)) = .ok data := by
  simp only [fixed, bytes_hexText, bind, Except.bind, Base.exactBytes, Vector.toArray_toList,
    Base.exactArray_toArray]

/-- A natural number written as JSON reads back as itself. -/
theorem number_toJson (what : String) (n : Nat) : number what (Lean.toJson n) = .ok n := by
  rw [number, Base.Toolchain.Json.getNat?_eq]
  rfl

/-- A field written once into an object reads back as its value. -/
theorem field_mkObj {what name : String} {pairs : List (String × Lean.Json)} {value : Lean.Json}
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (member : (name, value) ∈ pairs) :
    field what (Lean.Json.mkObj pairs) name = .ok value := by
  rw [field, Base.Json.getObjVal?_mkObj distinct member]
  rfl

/-- A module reads back as its function, its parameters and its message. -/
theorem moduleFields_moduleJson (what function : String) (params : List (String × Lean.Json))
    (message : String) :
    moduleFields what (moduleJson function params message) =
      .ok (function, Lean.Json.mkObj params, .str message) := by
  simp [moduleFields, moduleJson, field_mkObj, string_str, object, bind, Except.bind]
  rw [Base.Toolchain.Json.mkObj_eq, Base.Toolchain.Json.getObj?_eq]
  rfl

/-- A key derivation that runs reads back from the module it writes.

A derivation that runs asks for 32 bytes or more, which the reader requires. -/
theorem readKdf_toJson {kdf : Kdf} {password key : ByteArray}
    (derived : deriveKey password kdf = .ok key) : readKdf kdf.toJson = .ok kdf := by
  cases kdf with
  | pbkdf2 iterations length salt =>
    have long : ¬ length < 32 := fun short => by simp [deriveKey, short] at derived
    simp [readKdf, Kdf.toJson, moduleFields_moduleJson, field_mkObj, number_toJson, string_str,
      bytes_hexText, long, bind, Except.bind, pure, Except.pure, Base.toList_eq_data_toList]
  | scrypt n r p length salt =>
    have long : ¬ length < 32 := fun short => by simp [deriveKey, short] at derived
    simp [readKdf, Kdf.toJson, moduleFields_moduleJson, field_mkObj, number_toJson, bytes_hexText,
      long, bind, Except.bind, pure, Except.pure, Base.toList_eq_data_toList]

/-- A UUID written in its text form reads back as itself. -/
theorem readUuid_uuidText (uuid : Vector UInt8 16) :
    readUuid (.str (uuidText uuid)) = .ok uuid := by
  -- Name the sixteen bytes, so that every digit and hyphen sits at a known place.
  have bytes : uuid.toList = List.ofFn fun i : Fin 16 => uuid[i] := by
    rw [← Vector.toList_ofFn]
    exact congrArg Vector.toList Vector.ofFn_getElem.symm
  -- Each byte is two digits, kept abstract so that the hex reader can be applied at the end.
  obtain ⟨high, low, digits⟩ : ∃ high low : UInt8 → Char,
      ∀ byte, Base.byteHexDigits byte = [high byte, low byte] := ⟨_, _, fun _ => rfl⟩
  have read : Base.hexBytes? ((List.ofFn fun i : Fin 16 => uuid[i]).flatMap Base.byteHexDigits) =
      some ⟨uuid.toArray⟩ := by
    rw [← bytes, Base.hexBytes?_flatMap]
    rfl
  simp [List.ofFn_succ, digits] at read
  simp [readUuid, uuidText, hexText, bytes, List.ofFn_succ, string_str, bind, Except.bind,
    digits, uuidHyphens, read, Base.exactBytes]

/-- A written path reads back as itself, and the empty string as no path. -/
theorem readPath_elim (path : Option Bls.KeyPath.Path) :
    readPath (.str (path.elim "" Bls.KeyPath.Path.toString)) = .ok path := by
  cases path with
  | none => simp [readPath, string_str, bind, Except.bind, pure, Except.pure]
  | some path =>
    -- A written path starts with `m/`, so it is never the empty string.
    have written : path.toString ≠ "" := by
      simp [Bls.KeyPath.Path.toString]
    simp [readPath, string_str, written, Bls.KeyPath.parsePath_toString, bind, Except.bind,
      pure, Except.pure]

/-- The metadata fields, beside the cryptographic modules, read back as the metadata. -/
theorem readMetadata_mkObj (crypto : Lean.Json) (metadata : Metadata) :
    readMetadata (Lean.Json.mkObj ([("crypto", crypto)] ++ metadata.fields)) = .ok metadata := by
  -- Each optional field is present or absent, which fixes the names that the object holds.
  obtain ⟨path, uuid, pubkey, description⟩ := metadata
  cases pubkey <;> cases description <;>
    simp [readMetadata, Metadata.fields, field_mkObj, readPath_elim, readUuid_uuidText,
      optionalField, Base.Json.getObjVal?_mkObj, Base.Json.getObjVal?_mkObj_of_not_mem,
      string_str, fixed_hexText, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

/-- The document that encryption builds reads back as the store it describes. -/
theorem readStore_mkObj {kdf : Kdf} {password key : ByteArray}
    (derived : deriveKey password kdf = .ok key) (iv : Aes.Block) (metadata : Metadata)
    (checksum : Vector UInt8 32) (message : ByteArray) :
    readStore (Lean.Json.mkObj ([("crypto", Lean.Json.mkObj [
      ("kdf", kdf.toJson),
      ("checksum", moduleJson "sha256" [] (hexText checksum.toList)),
      ("cipher", moduleJson "aes-128-ctr" [("iv", .str (hexText iv.toList))]
        (hexText message.toList))])] ++ metadata.fields)) =
      .ok ⟨kdf, checksum, iv, message, metadata⟩ := by
  have read := readMetadata_mkObj (Lean.Json.mkObj [
    ("kdf", kdf.toJson),
    ("checksum", moduleJson "sha256" [] (hexText checksum.toList)),
    ("cipher", moduleJson "aes-128-ctr" [("iv", .str (hexText iv.toList))]
      (hexText message.toList))]) metadata
  obtain ⟨path, uuid, pubkey, description⟩ := metadata
  -- Each optional field is present or absent, which fixes the names that the object holds.
  cases pubkey <;> cases description <;>
    simp [Metadata.fields, Base.toList_eq_data_toList] at read <;>
    simp [readStore, Metadata.fields, field_mkObj, number_toJson, read,
      readKdf_toJson derived, moduleFields_moduleJson, fixed_hexText, bytes_hexText,
      Base.toList_eq_data_toList, bind, Except.bind, pure, Except.pure]

/-- What encryption writes, read back: the derived key and the store with its ciphertext. -/
theorem readStore_of_encrypt {kdf : Kdf} {iv : Aes.Block} {metadata : Metadata}
    {password : String} {secret : ByteArray} {json : Lean.Json}
    (written : encrypt kdf iv metadata password secret = .ok json) :
    ∃ key, deriveKey (passwordBytes password) kdf = .ok key ∧ ∃ long : 32 ≤ key.size,
      readStore json = .ok ⟨kdf,
        passwordChecksum key (Aes.ctr (Aes.ciph .aes128 (aesKey key long)) 128 iv secret), iv,
        Aes.ctr (Aes.ciph .aes128 (aesKey key long)) 128 iv secret, metadata⟩ := by
  unfold encrypt at written
  cases derived : deriveKey (passwordBytes password) kdf with
  | error error =>
    rw [derived] at written
    nomatch written
  | ok key =>
    rw [derived] at written
    have long := le_size_of_deriveKey derived
    simp only [bind, Except.bind, long, ↓reduceDIte, pure, Except.pure, Except.ok.injEq]
      at written
    subst written
    exact ⟨key, rfl, long, readStore_mkObj derived iv metadata _ _⟩

/-- A keystore that encryption writes reads back with its key derivation, IV and metadata. -/
theorem readStore_encrypt {kdf : Kdf} {iv : Aes.Block} {metadata : Metadata}
    {password : String} {secret : ByteArray} {json : Lean.Json}
    (written : encrypt kdf iv metadata password secret = .ok json) :
    ∃ store, readStore json = .ok store ∧ store.kdf = kdf ∧ store.iv = iv ∧
      store.metadata = metadata := by
  obtain ⟨_, _, _, read⟩ := readStore_of_encrypt written
  exact ⟨_, read, rfl, rfl, rfl⟩

/-- Decrypting what encryption wrote gives the secret back.

The password is the same, and the limits admit the key derivation that encryption ran. -/
theorem decrypt_encrypt {limits : KdfLimits} {kdf : Kdf} {iv : Aes.Block}
    {metadata : Metadata} {password : String} {secret : ByteArray} {json : Lean.Json}
    (written : encrypt kdf iv metadata password secret = .ok json)
    (admitted : limits.admits (passwordBytes password).size kdf = true) :
    decrypt limits json password = .ok secret := by
  obtain ⟨key, derived, long, read⟩ := readStore_of_encrypt written
  simp [decrypt, decryptStore, read, admitted, derived, decryptWithKey, long, Aes.ctr_ctr,
    bind, Except.bind, pure, Except.pure]

/-- A keystore written with the public key of its secret passes the public key check. -/
theorem checkPubkey_encrypt {kdf : Kdf} {iv : Aes.Block} {metadata : Metadata}
    {password : String} {secret : ByteArray} {json : Lean.Json}
    {key : Bls.Signatures.SecretKey}
    (secretKey : Bls.Signatures.SecretKey.fromBytes secret = .ok key)
    (written : encrypt kdf iv { metadata with pubkey := some (Bls.Signatures.skToPk key) }
      password secret = .ok json) :
    ∃ store, readStore json = .ok store ∧ checkPubkey secret store.metadata = true := by
  obtain ⟨_, _, _, read⟩ := readStore_of_encrypt written
  exact ⟨_, read, by simp [checkPubkey, secretKey]⟩

/-- Metadata without a public key fails the public key check, whatever the secret. -/
theorem checkPubkey_of_pubkey_eq_none {secret : ByteArray} {metadata : Metadata}
    (absent : metadata.pubkey = none) : checkPubkey secret metadata = false := by
  unfold checkPubkey
  rw [absent]

end EthLib.Cryptography.Keystore

module

public import EthLib.Consensus.KeymanagerApi.Types
public import EthLib.Consensus.Proofs.BeaconApi.Encoding
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Proofs.SlashingProtection
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonHexCase

/-!
# Proofs: the values of the Keymanager API

Each reader gives back the value that its writer writes.

For a value held as text, this holds for its document; the text goes through the toolchain.

An integer reads exactly from the strings of the source's pattern whose value is below 2^64.

A key and an address read the same with any characters after `0x` in uppercase.
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls Serialization.Ssz

/-! ## Scalars -/

/-- A string reads back as itself. -/
theorem readString_stringJson (path text : String) :
    readString path (stringJson text) = .ok text := rfl

/-- A boolean reads back as itself. -/
theorem readBool_bool (path : String) (flag : Bool) : readBool path (.bool flag) = .ok flag := rfl

/-- A 64-bit integer reads back as itself. -/
theorem readUint64_uint64Json (path : String) (value : UInt64) :
    readUint64 path (Interchange.uint64Json value) = .ok value := by
  simp [readUint64, Interchange.readUInt64_uint64Json, ofProtection]

/-- A public key reads back as itself. -/
theorem readPubkey_bytesJson (path : String) (pubkey : BLSPubkey) :
    readPubkey path (Interchange.bytesJson pubkey) = .ok pubkey := by
  simp [readPubkey, Interchange.readBytes_bytesJson, ofProtection]

/-- An address reads back as itself. -/
theorem readEthAddress_bytesJson (path : String) (address : ExecutionAddress) :
    readEthAddress path (Interchange.bytesJson address) = .ok address := by
  simp [readEthAddress, Interchange.readBytes_bytesJson, ofProtection]

/-- A signature reads back as itself. -/
theorem readSignature_bytesJson (path : String) (signature : BLSSignature) :
    readSignature path (Interchange.bytesJson signature) = .ok signature := by
  simp [readSignature, Interchange.readBytes_bytesJson, ofProtection]

/-! ## The letter case of hex -/

/-- Fixed-size bytes read the same with some characters after `0x` in uppercase. -/
theorem readBytes_hexCase {path text other : String} {size : Nat} (cased : HexCase text other) :
    Interchange.readBytes path size (.str text) = Interchange.readBytes path size (.str other) := by
  simp only [Interchange.readBytes, Interchange.readString, bind, Except.bind]
  rw [ofHex_hexCase cased]

/-- A public key reads the same with some characters after `0x` in uppercase. -/
theorem readPubkey_hexCase {path text other : String} (cased : HexCase text other) :
    readPubkey path (.str text) = readPubkey path (.str other) := by
  rw [readPubkey, readPubkey, readBytes_hexCase cased]

/-- An address reads the same with some characters after `0x` in uppercase. -/
theorem readEthAddress_hexCase {path text other : String} (cased : HexCase text other) :
    readEthAddress path (.str text) = readEthAddress path (.str other) := by
  rw [readEthAddress, readEthAddress, readBytes_hexCase cased]

/-! ## The pattern of an integer -/

/-- Whether a string matches `^(0|[1-9][0-9]{0,19})$`, the pattern of [`uint.yaml`].

That is `0` alone, or a digit other than `0` followed by at most 19 digits.

[`uint.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/uint.yaml
-/
def Uint64Pattern (text : String) : Prop :=
  text.toList = ['0'] ∨
    ∃ first rest, text.toList = first :: rest ∧ first.isDigit = true ∧ first ≠ '0' ∧
      (∀ c ∈ rest, c.isDigit = true) ∧ rest.length ≤ 19

/-- A decimal string reads as a number exactly when it is the number written in decimal. -/
private theorem readNat_str_eq_ok_iff {text : String} {n : Nat} :
    readNat (.str text) = .ok n ↔ text = toString n := by
  constructor
  · intro read
    simp only [readNat] at read
    split at read
    · rename_i same
      cases read
      exact (beq_iff_eq.mp same).symm
    · cases read
  · rintro rfl
    simp only [readNat, Nat.toString_eq_repr, Nat.toList_repr, Nat.ofDigitChars_ten_toDigits,
      beq_self_eq_true, ↓reduceIte]

/-- A digit character is the character of its value, which is below ten. -/
private theorem digitChar_of_isDigit {c : Char} (digit : c.isDigit = true) :
    c.toNat - 48 < 10 ∧ (c.toNat - 48).digitChar = c := by
  have bounds := Char.isDigit_iff_toNat.mp digit
  have zero : '0'.toNat = 48 := rfl
  have nine : '9'.toNat = 57 := rfl
  refine ⟨by omega, Char.toNat_inj.mp ?_⟩
  rw [Nat.toNat_digitChar_of_lt_ten (by omega)]
  omega

/-- The decimal form of a positive number starts with a digit other than `0`. -/
private theorem toDigits_head_ne_zero :
    ∀ n, 0 < n → ∃ first rest, Nat.toDigits 10 n = first :: rest ∧ first ≠ '0' := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro positive
    by_cases small : n < 10
    · exact ⟨n.digitChar, [], Nat.toDigits_of_lt_base small, by
        simp only [ne_eq, Nat.digitChar_eq_zero]
        omega⟩
    · obtain ⟨first, rest, eq, ne⟩ := ih (n / 10) (by omega) (by omega)
      refine ⟨first, rest ++ [(n % 10).digitChar], ?_, ne⟩
      rw [Nat.toDigits_of_base_le (by decide) (by omega), eq, List.cons_append]

/-- A digit other than `0`, then digits, read as a positive number. -/
private theorem ofDigitChars_pos {first : Char} {rest : List Char} (digit : first.isDigit = true)
    (ne : first ≠ '0') : 0 < Nat.ofDigitChars 10 (first :: rest) 0 := by
  have ⟨_, back⟩ := digitChar_of_isDigit digit
  have pos : 0 < first.toNat - 48 := by
    rcases Nat.eq_zero_or_pos (first.toNat - 48) with zero | pos
    · exact absurd (by rw [← back, zero]; simp) ne
    · exact pos
  rw [Nat.ofDigitChars_cons, Nat.ofDigitChars_eq_ofDigitChars_zero]
  have : 0 < 10 ^ rest.length := Nat.pow_pos (by decide)
  have : 0 < 10 ^ rest.length * (10 * 0 + (first.toNat - '0'.toNat)) :=
    Nat.mul_pos this (by simpa using pos)
  omega

/-- A decimal form stays one when a digit is written after it. -/
private theorem toDigits_ofDigitChars_append {front : List Char} {last : Char}
    (positive : 0 < Nat.ofDigitChars 10 front 0)
    (decimal : Nat.toDigits 10 (Nat.ofDigitChars 10 front 0) = front)
    (digit : last.isDigit = true) :
    Nat.toDigits 10 (Nat.ofDigitChars 10 (front ++ [last]) 0) = front ++ [last] := by
  have ⟨small, back⟩ := digitChar_of_isDigit digit
  rw [Nat.ofDigitChars_append, Nat.ofDigitChars_cons, Nat.ofDigitChars_nil,
    show last.toNat - '0'.toNat = last.toNat - 48 from rfl,
    ← Nat.toDigits_append_toDigits (by decide) positive small, decimal,
    Nat.toDigits_of_lt_base small, back]

/-- Digits after a decimal form of a positive number make a decimal form again. -/
private theorem toDigits_ofDigitChars_of_front :
    ∀ (rest front : List Char), 0 < Nat.ofDigitChars 10 front 0 →
      Nat.toDigits 10 (Nat.ofDigitChars 10 front 0) = front → (∀ c ∈ rest, c.isDigit = true) →
        Nat.toDigits 10 (Nat.ofDigitChars 10 (front ++ rest) 0) = front ++ rest
  | [], front, _, decimal, _ => by rw [List.append_nil, decimal]
  | last :: rest, front, positive, decimal, digits => by
    have grown := toDigits_ofDigitChars_append positive decimal (digits last (by simp))
    have larger : 0 < Nat.ofDigitChars 10 (front ++ [last]) 0 := by
      rw [Nat.ofDigitChars_append, Nat.ofDigitChars_cons, Nat.ofDigitChars_nil]
      have := Nat.mul_le_mul_left 10 positive
      omega
    have step := toDigits_ofDigitChars_of_front rest (front ++ [last]) larger grown
      fun c mem => digits c (by simp [mem])
    simpa using step

/-- A digit other than `0`, then digits, is the decimal form of the number they write. -/
private theorem toDigits_ofDigitChars {first : Char} {rest : List Char}
    (digit : first.isDigit = true) (ne : first ≠ '0') (digits : ∀ c ∈ rest, c.isDigit = true) :
    Nat.toDigits 10 (Nat.ofDigitChars 10 (first :: rest) 0) = first :: rest := by
  have ⟨small, back⟩ := digitChar_of_isDigit digit
  have single : Nat.toDigits 10 (Nat.ofDigitChars 10 [first] 0) = [first] := by
    simp only [Nat.ofDigitChars_cons, Nat.ofDigitChars_nil, Nat.mul_zero, Nat.zero_add]
    rw [show first.toNat - '0'.toNat = first.toNat - 48 from rfl, Nat.toDigits_of_lt_base small,
      back]
  have := toDigits_ofDigitChars_of_front rest [first] (ofDigitChars_pos (rest := []) digit ne)
    single digits
  simpa using this

/-- A string is the decimal form of a number below 2^64 exactly when it matches the pattern.

The number is then the one that its digits write. -/
private theorem eq_toString_iff {text : String} {n : Nat} (bound : n < 2 ^ 64) :
    text = toString n ↔ Uint64Pattern text ∧ Nat.ofDigitChars 10 text.toList 0 = n := by
  constructor
  · rintro rfl
    have digits : (toString n).toList = Nat.toDigits 10 n := by simp
    refine ⟨?_, by rw [digits, Nat.ofDigitChars_ten_toDigits]⟩
    rcases Nat.eq_zero_or_pos n with rfl | positive
    · exact .inl (by simp)
    · obtain ⟨first, rest, eq, ne⟩ := toDigits_head_ne_zero n positive
      have isDigit : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := fun c mem =>
        Nat.isDigit_of_mem_toDigits (by decide) (by decide) mem
      have short :=
        (Nat.length_toDigits_le_iff (b := 10) (n := n) (k := 20) (by decide) (by decide)).mpr
        (Nat.lt_of_lt_of_le bound (by decide))
      rw [eq] at isDigit short
      refine .inr ⟨first, rest, by rw [digits, eq], isDigit first (by simp), ne,
        fun c mem => isDigit c (by simp [mem]), by simpa using short⟩
  · rintro ⟨pattern, rfl⟩
    apply String.toList_inj.mp
    rw [Nat.toString_eq_repr, Nat.toList_repr]
    rcases pattern with zero | ⟨first, rest, eq, digit, ne, digits, _⟩
    · rw [zero]
      simp [Nat.ofDigitChars_cons]
    · rw [eq, toDigits_ofDigitChars digit ne digits]

/-- An integer reads from a string as a value exactly when the string matches the pattern.

The value is then the number that the digits write, so that number is below 2^64. -/
theorem readUint64_str_eq_ok_iff {path text : String} {value : UInt64} :
    readUint64 path (.str text) = .ok value ↔
      Uint64Pattern text ∧ Nat.ofDigitChars 10 text.toList 0 = value.toNat := by
  rw [← eq_toString_iff value.toNat_lt]
  simp only [readUint64, Interchange.readUInt64, Interchange.readString, bind, Except.bind]
  constructor
  · intro read
    split at read
    · rename_i n parsed
      split at read
      · rename_i small
        simp only [ofProtection, Except.ok.injEq] at read
        subst read
        rw [readNat_str_eq_ok_iff.mp parsed,
          show n.toUInt64.toNat = n from UInt64.toNat_ofNat_of_lt' small]
      · simp [ofProtection] at read
    · simp [ofProtection] at read
  · intro eq
    have parsed : readNat (.str text) = .ok value.toNat := readNat_str_eq_ok_iff.mpr eq
    simp [parsed, value.toNat_lt, ofProtection]

/-- An integer reads from a string exactly when it matches the pattern and is below 2^64. -/
theorem readUint64_str_ok_iff {path text : String} :
    (∃ value, readUint64 path (.str text) = .ok value) ↔
      Uint64Pattern text ∧ Nat.ofDigitChars 10 text.toList 0 < 2 ^ 64 := by
  simp only [readUint64_str_eq_ok_iff]
  constructor
  · rintro ⟨value, pattern, eq⟩
    exact ⟨pattern, eq ▸ value.toNat_lt⟩
  · rintro ⟨pattern, small⟩
    exact ⟨UInt64.ofNat (Nat.ofDigitChars 10 text.toList 0), pattern,
      (UInt64.toNat_ofNat_of_lt' small).symm⟩

/-- An integer reads only from a string. -/
theorem eq_str_of_readUint64 {path : String} {document : Json} {value : UInt64}
    (read : readUint64 path document = .ok value) : ∃ text, document = .str text := by
  cases document with
  | str text => exact ⟨text, rfl⟩
  | _ => simp [readUint64, Interchange.readUInt64, Interchange.readString, ofProtection, bind,
      Except.bind] at read

/-! ## Documents held as text -/

/-- Slashing protection data reads back from its document. -/
theorem slashingProtectionOfDocument_toJson (interchange : Interchange) :
    slashingProtectionOfDocument interchange.toJson = .ok interchange := by
  simp [slashingProtectionOfDocument, Interchange.ofJson_toJson, Except.mapError]

/-! ## Objects -/

/-- An object built from pairs of distinct names gives the value of the pair with a name. -/
theorem getObjVal?_mkObj_eq {pairs : List (String × Json)}
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (name : String) :
    (Json.mkObj pairs).getObjVal? name = match pairs.lookup name with
      | some value => .ok value
      | none => .error s!"property not found: {name}" := by
  cases found : pairs.lookup name with
  | none =>
    apply getObjVal?_mkObj_of_not_mem
    rw [List.lookup_eq_none_iff] at found
    intro mem
    obtain ⟨pair, member, rfl⟩ := List.mem_map.mp mem
    simpa using found pair member
  | some value =>
    obtain ⟨front, back, rfl, -⟩ := List.lookup_eq_some_iff.mp found
    exact getObjVal?_mkObj distinct (by simp)

/-- The definition of a remote key reads back as itself. -/
theorem readSignerDefinition_signerDefinitionJson (path : String) (definition : SignerDefinition) :
    readSignerDefinition path (signerDefinitionJson definition) = .ok definition := by
  rcases definition with ⟨pubkey, url, readonly⟩
  rcases url with _ | url <;> rcases readonly with _ | readonly <;>
    simp (disch := simp) [readSignerDefinition, signerDefinitionJson, optionalFields,
      requiredField, optionalField, Interchange.field, getObjVal?_mkObj_eq, List.lookup,
      readPubkey_bytesJson, readString_stringJson, readBool_bool, ofProtection, bind, Except.bind,
      pure, Except.pure]

/-- A remote key to import reads back as itself. -/
theorem readImportRemoteSignerDefinition_importRemoteSignerDefinitionJson (path : String)
    (definition : ImportRemoteSignerDefinition) :
    readImportRemoteSignerDefinition path (importRemoteSignerDefinitionJson definition) =
      .ok definition := by
  rcases definition with ⟨pubkey, url⟩
  rcases url with _ | url <;>
    simp (disch := simp) [readImportRemoteSignerDefinition, importRemoteSignerDefinitionJson,
      optionalFields, requiredField, optionalField, Interchange.field, getObjVal?_mkObj_eq,
      List.lookup, readPubkey_bytesJson, readString_stringJson, ofProtection, bind, Except.bind,
      pure, Except.pure]

/-- A fee recipient reads back as itself. -/
theorem readFeeRecipient_feeRecipientJson (path : String) (recipient : FeeRecipient) :
    readFeeRecipient path (feeRecipientJson recipient) = .ok recipient := by
  rcases recipient with ⟨pubkey, ethaddress⟩
  rcases pubkey with _ | pubkey <;>
    simp (disch := simp) [readFeeRecipient, feeRecipientJson, optionalFields, requiredField,
      optionalField, Interchange.field, getObjVal?_mkObj_eq, List.lookup, readPubkey_bytesJson,
      readEthAddress_bytesJson, ofProtection, bind, Except.bind, pure, Except.pure]

/-- A gas limit reads back as itself. -/
theorem readGasLimit_gasLimitJson (path : String) (limit : GasLimit) :
    readGasLimit path (gasLimitJson limit) = .ok limit := by
  rcases limit with ⟨pubkey, gasLimit⟩
  rcases pubkey with _ | pubkey <;>
    simp (disch := simp) [readGasLimit, gasLimitJson, optionalFields, requiredField,
      optionalField, Interchange.field, getObjVal?_mkObj_eq, List.lookup, readPubkey_bytesJson,
      readUint64_uint64Json, ofProtection, bind, Except.bind, pure, Except.pure]

/-- The body of an error response reads back as itself. -/
theorem readErrorResponse_errorResponseJson (path : String) (response : ErrorResponse) :
    readErrorResponse path (errorResponseJson response) = .ok response := by
  simp (disch := simp) [readErrorResponse, errorResponseJson, requiredField, Interchange.field,
    getObjVal?_mkObj_eq, List.lookup, readString_stringJson, ofProtection, bind, Except.bind, pure,
    Except.pure]

/-- The writer of a signed voluntary exit never fails. -/
theorem signedVoluntaryExitJson_total (signed : SignedVoluntaryExit) :
    ∃ document, signedVoluntaryExitJson signed = .ok document := by
  obtain ⟨document, wrote⟩ := BeaconApi.toApiJson_total signed
  exact ⟨document, by simp [signedVoluntaryExitJson, wrote, Except.mapError]⟩

/-- A signed voluntary exit reads back from the document that its writer gives. -/
theorem readSignedVoluntaryExit_of_signedVoluntaryExitJson {path : String}
    {signed : SignedVoluntaryExit} {document : Json}
    (wrote : signedVoluntaryExitJson signed = .ok document) :
    readSignedVoluntaryExit path document = .ok signed := by
  cases written : BeaconApi.toApiJson signed with
  | error => simp [signedVoluntaryExitJson, written, Except.mapError] at wrote
  | ok other =>
    simp only [signedVoluntaryExitJson, written, Except.mapError, Except.ok.injEq] at wrote
    subst wrote
    simp [readSignedVoluntaryExit, BeaconApi.ofApiJson_toApiJson written, Except.mapError]

end EthLib.Consensus.KeymanagerApi

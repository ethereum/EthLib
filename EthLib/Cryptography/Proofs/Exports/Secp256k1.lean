module

public import EthLib.Cryptography.Exports.Secp256k1
public import EthLib.Cryptography.Proofs.Secp256k1.Recovery
import EthLib.Base.Proofs.BigEndianWords
import all EthLib.Cryptography.Exports.Secp256k1

/-!
# Proofs for the secp256k1 recovery export

The export reads the hash and signature as words.

Its result agrees with the shared readers followed by recovery and encoding.
-/

public section

namespace EthLib.Cryptography.Secp256k1.Exports

open EthLib.Cryptography.Ecdsa (SIGNATURE_LEN)
open EthLib.Cryptography.Secp256k1.Ecdsa Fp.RecoveryField

private theorem readRecoveryWords_toNat (bytes : ByteArray) (start : Nat)
    (h : start + 32 ≤ bytes.size) :
    Fp.RecoveryField.rawToNat (readRecoveryWords bytes start h) =
      Base.byteArrayToNat32 bytes start h := by
  simp only [readRecoveryWords, Base.withByteArrayWords32, Base.byteArrayToNat32,
    Base.indexedBytesToNat32, Base.withIndexedWords32, Fp.RecoveryField.rawToNat]

private theorem recoveryDigest_toNat (hash : ByteArray) (h : hash.size = 32) :
    rawToNat (readRecoveryWords hash 0 (by omega)) = hashToInt ⟨hash.data, h⟩ := by
  rw [readRecoveryWords_toNat, Base.byteArrayToNat32_eq, hashToInt, List.drop_zero]
  change Base.bytesToNat (hash.data.toList.take 32) = Base.bytesToNat hash.data.toList
  rw [List.take_of_length_le]
  simp only [Array.length_toList, ByteArray.size_data, h, Nat.le_refl]

private theorem readSignature_eq_of_size (signature : ByteArray) (h : signature.size = 64) :
    Cryptography.Ecdsa.read signature Secp256k1Error.badSignatureSize =
      .ok (rawToNat (readRecoveryWords signature 0 (by omega)),
        rawToNat (readRecoveryWords signature 32 (by omega))) := by
  have hs : signature.data.size = SIGNATURE_LEN := h
  have hlen : signature.data.toList.length = 64 := by
    rw [Array.length_toList, ByteArray.size_data]
    exact h
  have ht : (signature.data.toList.drop 32).length ≤ 32 := by
    rw [List.length_drop, hlen]
  simp only [Cryptography.Ecdsa.read, Base.exactBytes, Base.exactArray, Base.exactArray?,
    dite_eq_left hs, Except.map, Cryptography.Ecdsa.toNats, Vector.toList_mk,
    readRecoveryWords_toNat, Base.byteArrayToNat32_eq, List.drop_zero, List.take_of_length_le ht]

private theorem recoverExport_eq_encoded
    (hash signature : ByteArray) (recoveryId : UInt8) :
    recoverExport hash signature recoveryId =
      runSecp256k1 (do
        let digest ← readHash hash
        let (r, s) ← Cryptography.Ecdsa.read signature .badSignatureSize
        if h : recoveryId.toNat < 2 then
          recoverEncoded digest r s ⟨recoveryId.toNat, h⟩
        else throw (.badRecoveryId recoveryId)) := by
  by_cases hh : hash.size = HASH_LEN
  · have hhd : hash.data.size = HASH_LEN := hh
    by_cases hs : signature.size = SIGNATURE_LEN
    · by_cases hi : recoveryId.toNat < 2
      · have hh' : hash.size = 32 := by simpa only [HASH_LEN] using hh
        have hs' : signature.size = 64 := by simpa only [SIGNATURE_LEN] using hs
        simp only [recoverExport, readHash, Base.exactBytes, Base.exactArray, Base.exactArray?,
          dite_eq_left hh, dite_eq_left hhd, dite_eq_left hs, dite_eq_left hi,
          readSignature_eq_of_size signature hs]
        exact congrArg runSecp256k1 <| recoverEncodedFromWords_eq ⟨hash.data, hh'⟩
          (readRecoveryWords hash 0 (by omega)) (readRecoveryWords signature 0 (by omega))
          (readRecoveryWords signature 32 (by omega)) (recoveryDigest_toNat hash hh') ⟨_, hi⟩
      · simp only [recoverExport, readHash, Base.exactBytes, Base.exactArray, Base.exactArray?,
          dite_eq_left hh, dite_eq_left hhd, dite_eq_left hs, dite_eq_right hi,
          readSignature_eq_of_size signature hs]
        rfl
    · have hsd : signature.data.size ≠ SIGNATURE_LEN := hs
      simp only [recoverExport, readHash, Cryptography.Ecdsa.read, Base.exactBytes, Base.exactArray,
        Base.exactArray?, dite_eq_left hh, dite_eq_left hhd, dite_eq_right hs, dite_eq_right hsd]
      rfl
  · have hhd : hash.data.size ≠ HASH_LEN := hh
    simp only [recoverExport, readHash, Base.exactBytes, Base.exactArray, Base.exactArray?,
      dite_eq_right hh, dite_eq_right hhd]
    rfl

/-- The recovery export gives the same bytes or error as the shared readers and recovery. -/
theorem recoverExport_eq
    (hash signature : ByteArray) (recoveryId : UInt8) :
    recoverExport hash signature recoveryId =
      runSecp256k1 (do
        let digest ← readHash hash
        let (r, s) ← Cryptography.Ecdsa.read signature .badSignatureSize
        if h : recoveryId.toNat < 2 then
          let q ← recover digest r s ⟨recoveryId.toNat, h⟩
          return q.encodeUncompressed
        else throw (.badRecoveryId recoveryId)) := by
  rw [recoverExport_eq_encoded]
  apply congrArg runSecp256k1
  apply congrArg (fun next => (readHash hash).bind next)
  funext digest
  apply congrArg
    (fun next => (Cryptography.Ecdsa.read signature Secp256k1Error.badSignatureSize).bind next)
  funext scalars
  obtain ⟨r, s⟩ := scalars
  change (if h : recoveryId.toNat < 2 then recoverEncoded digest r s ⟨recoveryId.toNat, h⟩
      else throw _) = _
  split
  · rename_i h
    rw [recoverEncoded_eq]
    change (recover digest r s ⟨recoveryId.toNat, h⟩).map Point.encodeUncompressedDirect =
      (recover digest r s ⟨recoveryId.toNat, h⟩).bind (fun p => .ok p.encodeUncompressed)
    cases recover digest r s ⟨recoveryId.toNat, h⟩ with
    | error e => rfl
    | ok p => exact congrArg Except.ok (Point.encodeUncompressedDirect_eq p)
  · rfl

end EthLib.Cryptography.Secp256k1.Exports

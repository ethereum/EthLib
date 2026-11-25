module

public import EthLib.Networking.Proofs.Enr.V4
public import EthLib.Cryptography.Proofs.Secp256k1.Ecdsa
public import EthLib.Serialization.Proofs.Rlp.RoundTrip

/-!
# Proofs: forgeries and malleability of "v4" records

The "v4" identity scheme of EIP-778 signs the Keccak-256 hash of the RLP content with ECDSA.

A forged record gives the forgery half of a reduction to the chosen-message security of that ECDSA.

That half needs no cryptographic assumption.

No game with an adversary and oracles is stated here.

The security of records then rests on the chosen-message security of that ECDSA, an assumption.

Source: [EIP-778][eip-778], section "v4" identity scheme.

[eip-778]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-778.md
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1
open EthLib.Serialization.Rlp

/-! ## The scalars of a signature -/

/-- The scalar `r` of a record's signature: its first 32 bytes, big-endian. -/
def sigR (rec : Enr) : Nat := Base.ByteOrder.ofBE (rec.signature.data.toList.take 32)

/-- The scalar `s` of a record's signature: the bytes after the first 32, big-endian. -/
def sigS (rec : Enr) : Nat := Base.ByteOrder.ofBE (rec.signature.data.toList.drop 32)

/-- For a 64-byte signature, the record with `s` replaced by `n - s`, in 32 big-endian bytes.

The sequence number, the pairs and the bytes of `r` stay. -/
def negS (rec : Enr) : Enr :=
  { rec with signature :=
      ⟨(rec.signature.data.toList.take 32
        ++ (Base.ByteOrder.toBE 32 (Fn.modulus - sigS rec)).toList).toArray⟩ }

/-! ## Malleability

ECDSA accepts `(r, s)` exactly when it accepts `(r, n - s)`, and EIP-778 adds no low-s rule.

So one content has two valid records: the scheme is not strongly unforgeable.
-/

/-- ECDSA rejects a scalar `s` outside `[1, n - 1]`. -/
private theorem verify_eq_false_of_s {q : Point} {h : Vector UInt8 32} {r s : Nat}
    (hs : ¬(0 < s ∧ s < Fn.modulus)) : Ecdsa.verify q h r s = false := by
  simp only [Ecdsa.verify, Cryptography.Ecdsa.Curve.verify, hs, dite_false, dite_eq_ite, ite_self]

/-- The bytes of the copy with `n - s`. -/
private theorem negS_data (rec : Enr) : (negS rec).signature.data.toList =
    rec.signature.data.toList.take 32
      ++ (Base.ByteOrder.toBE 32 (Fn.modulus - sigS rec)).toList := rfl

/-- The first 32 bytes of a 64-byte signature. -/
private theorem length_take_of_size {rec : Enr} (hsize : rec.signature.size = 64) :
    (rec.signature.data.toList.take 32).length = 32 := by
  simp only [ByteArray.size] at hsize
  rw [List.length_take, Array.length_toList, hsize]
  rfl

/-- The copy with `n - s` of a record with a 64-byte signature reads `r`, then `n - s`. -/
private theorem negS_scalars {rec : Enr} (hsize : rec.signature.size = 64) :
    (negS rec).signature.size = 64 ∧
      (negS rec).signature.data.toList.take 32 = rec.signature.data.toList.take 32 ∧
      Base.ByteOrder.ofBE ((negS rec).signature.data.toList.drop 32) = Fn.modulus - sigS rec := by
  have ht := length_take_of_size hsize
  have hl := Base.ByteOrder.length_toList_toBE 32 (Fn.modulus - sigS rec)
  refine ⟨?_, ?_, ?_⟩
  · simp only [ByteArray.size, ← Array.length_toList, negS_data, List.length_append, ht, hl]
  · rw [negS_data, List.take_left' ht]
  · rw [negS_data, List.drop_left' ht, Base.ByteOrder.ofBE_toBE_of_lt]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (by decide : Fn.modulus < 256 ^ 32)

/-- A record with a 64-byte signature verifies exactly when its copy with `n - s` does. -/
theorem verifyV4_negS {rec : Enr} (hsize : rec.signature.size = 64) :
    verifyV4 (negS rec) = verifyV4 rec := by
  obtain ⟨hsize', htake, hdrop⟩ := negS_scalars hsize
  have hpk : (negS rec).publicKeyV4 = rec.publicKeyV4 := rfl
  unfold verifyV4
  have hc : (negS rec).content = rec.content := rfl
  rw [hpk, hc]
  split
  · simp only [Cryptography.Ecdsa.read?_eq, Cryptography.Ecdsa.SIGNATURE_LEN, hsize, hsize',
      ↓reduceIte, htake, hdrop]
    by_cases hs : 0 < sigS rec ∧ sigS rec < Fn.modulus
    -- For `s` in `[1, n - 1]`, ECDSA accepts `(r, s)` exactly when it accepts `(r, n - s)`.
    · exact Ecdsa.verify_neg_s _ _ _ hs
    · exact (verify_eq_false_of_s (by omega)).trans (verify_eq_false_of_s hs).symm
  · rfl

/-- A record that verifies differs from its copy with `n - s`. -/
theorem negS_ne_of_verifyV4 {rec : Enr} (h : verifyV4 rec = true) : negS rec ≠ rec := by
  obtain ⟨q, content, -, -, hsize, hv⟩ := verifyV4_eq_true_iff.mp h
  have hs : 0 < sigS rec ∧ sigS rec < Fn.modulus := by
    by_contra hs
    exact Bool.false_ne_true ((verify_eq_false_of_s hs).symm.trans hv)
  intro heq
  have hdrop := (negS_scalars hsize).2.2
  -- Equal records have equal scalars `s`, so `n - s = s`, but `n` is odd.
  have hss : Fn.modulus - sigS rec = sigS rec := by
    rw [← hdrop, heq]
    rfl
  have hodd : Fn.modulus % 2 = 1 := by decide
  omega

/-- The copy with `n - s` has the content of the record. -/
theorem content_negS (rec : Enr) : (negS rec).content = rec.content := rfl

/-! ## Forgeries

A forgery is a record that verifies under a key `Q`, whose content the signer of `Q` never signed.

The forger chooses the sequence number and every pair of that content.

The notion is per key: a record under another key with the same node ID is out of scope.
-/

/-- The messages that a signer signs for a list of contents: their RLP encodings.

A content whose RLP encoding fails is not signed.

Each signed record is one ECDSA signature on its encoding, by the signing lemma of the scheme.

The model assumes that the key signs only records. -/
def signedMessages (log : List Item) : List ByteArray :=
  log.filterMap fun c => (Serialization.Rlp.encode c).toOption

/-- **A forged "v4" record gives an ECDSA forgery on a fresh message.**

The record verifies under the key `q`, and its content is not among those the signer signed.

Its content then has an encoding `b`, and the pair `(r, s)` is read from its signature.

The message `b` with that pair is a forgery of ECDSA with Keccak-256 against the signed messages.
-/
theorem ecdsaForgery_of_forgery {q : Point} {log : List Item} {rec : Enr}
    (hq : rec.publicKeyV4 = .ok q) (hv : verifyV4 rec = true) (hfresh : rec.content ∉ log) :
    ∃ b, Serialization.Rlp.encode rec.content = .ok b ∧
      Ecdsa.IsForgery Hash.Keccak.keccak256 q (signedMessages log) (b, sigR rec, sigS rec) := by
  obtain ⟨q', b, hq', hb, -, hv⟩ := verifyV4_eq_true_iff.mp hv
  have hqq : q' = q := by
    rw [hq] at hq'
    cases hq'
    rfl
  subst hqq
  -- The ECDSA forgery is computed from the record: its RLP encoding `b` and its pair `(r, s)`.
  --
  -- That ECDSA hashes the message with Keccak-256, as the scheme does.
  refine ⟨b, hb, ?_, hv⟩
  -- A signed content with the encoding `b` is the content itself, against freshness.
  intro hmem
  obtain ⟨c', hc'log, hc'⟩ := List.mem_filterMap.mp hmem
  have hb' : Serialization.Rlp.encode c' = .ok b := by
    cases he : Serialization.Rlp.encode c' with
    | error e => rw [he] at hc'; cases hc'
    | ok b' => rw [he] at hc'; cases hc'; rfl
  -- The RLP encoder is injective, so two different contents have two different encodings.
  --
  -- So the signer never signed the encoding `b`.
  exact hfresh (encode_injective _ _ _ hb' hb ▸ hc'log)

end EthLib.Networking.Enr

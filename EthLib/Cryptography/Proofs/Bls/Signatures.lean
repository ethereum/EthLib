module

public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Cryptography.Proofs.Bls.Fr
public import EthLib.Cryptography.Proofs.Bls.HashToCurveValidity
import EthLib.Base.Proofs.MapM

/-!
# Proofs: BLS signing never fails, and the rejected inputs

Source: draft-irtf-cfrg-bls-signature-04, §2.6 to §2.9 and §3.3.

Signing never fails, because the hash to curve never fails.

Each other theorem names an input that an operation rejects.

The decoder of a secret key accepts exactly the 32-byte encodings of the nonzero scalars below `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Signatures

open EthLib.Base EthLib.Cryptography.Bls

/-- The core signature never fails. -/
theorem coreSign_ok (sk : SecretKey) (msg dst : ByteArray) :
    ∃ sig, coreSign sk msg dst = .ok sig := by
  obtain ⟨q, hq, -⟩ := HashToCurve.hashToG2_total msg dst
  refine ⟨pointToSignature (G2.mul q sk.val), ?_⟩
  -- Rewrite the hash first, so the kernel never evaluates it on a variable message.
  unfold coreSign
  rw [hq]
  rfl

/-- Signing never fails. -/
theorem sign_ok (sk : SecretKey) (msg : ByteArray) : ∃ sig, sign sk msg = .ok sig :=
  coreSign_ok sk msg DST

/-- The proof of possession never fails. -/
theorem popProve_ok (sk : SecretKey) : ∃ proof, popProve sk = .ok proof :=
  coreSign_ok sk _ POP_DST

/-- Aggregation rejects an empty list (§2.8). -/
theorem aggregate_empty : aggregate #[] = .error .emptySignatureList := rfl

/-- Aggregation fails exactly on an empty list, or on a signature that does not decode (§2.8). -/
theorem exists_aggregate_eq_error_iff {sigs : Array BLSSignature} :
    (∃ error, aggregate sigs = .error error) ↔
      sigs = #[] ∨ ∃ sig ∈ sigs, ∃ error, G2.uncompress sig = .error error := by
  rcases sigs with ⟨_ | ⟨first, rest⟩⟩
  · exact iff_of_true ⟨_, aggregate_empty⟩ (.inl rfl)
  -- A list with a signature passes the check of its size, so only the sum of the points can fail.
  have nonempty : (first :: rest).toArray ≠ #[] :=
    Array.ne_empty_of_mem (List.mem_toArray.mpr List.mem_cons_self)
  simp only [nonempty, false_or, List.mem_toArray]
  unfold aggregate
  simp only [List.isEmpty_toArray, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    List.foldlM_toArray]
  constructor
  · rintro ⟨error, failed⟩
    rcases bind_eq_error failed with failed | ⟨_, -, failed⟩
    -- When each signature decodes, each step of the sum succeeds, and so does the fold.
    · refine Classical.byContradiction fun decodes => foldlM_ne_error _ _ ?_ failed
      intro agg sig member
      cases decoded : G2.uncompress sig with
      | error error => exact absurd ⟨sig, member, error, decoded⟩ decodes
      | ok point => exact ⟨_, rfl⟩
    · cases failed
  · rintro ⟨sig, member, error, bad⟩
    cases folded : (first :: rest).foldlM
        (fun agg sig => do let point ← G2.uncompress sig; pure (G2.add agg point)) G2.zero with
    | error fault => exact ⟨fault, rfl⟩
    -- A fold that succeeds succeeds at the step of each signature, and this step fails.
    | ok done =>
      obtain ⟨-, -, before, after, -, -, step⟩ := foldlM_ok_of_mem member folded
      rw [bad] at step
      cases step

/-- Aggregating the signatures of a list with a member fails exactly on one that does not decode. -/
theorem exists_aggregate_map_eq_error_iff {α : Type} {entries : List α} {entry : α}
    (member : entry ∈ entries) (signature : α → BLSSignature) :
    (∃ error, aggregate (entries.map signature).toArray = .error error) ↔
      ∃ entry ∈ entries, ∃ error, G2.uncompress (signature entry) = .error error := by
  have nonempty : (entries.map signature).toArray ≠ #[] :=
    Array.ne_empty_of_mem (List.mem_toArray.mpr (List.mem_map_of_mem member))
  rw [exists_aggregate_eq_error_iff]
  simp only [nonempty, false_or, List.mem_toArray, List.mem_map]
  exact ⟨fun ⟨_, ⟨entry, inside, rfl⟩, bad⟩ => ⟨entry, inside, bad⟩,
    fun ⟨entry, inside, bad⟩ => ⟨_, ⟨entry, inside, rfl⟩, bad⟩⟩

/-- The key sum rejects an empty list (§3.3.4). -/
theorem aggregatePubkeyPoint_empty : aggregatePubkeyPoint #[] = .error .emptyPubkeyList := rfl

/-- The fast aggregate verification rejects an empty key list (§3.3.4). -/
theorem fastAggregateVerify_empty (msg : ByteArray) (sig : BLSSignature) :
    fastAggregateVerify #[] msg sig = false := rfl

/-- The Ethereum key aggregation rejects an empty list. -/
theorem ethAggregatePubkeys_empty : ethAggregatePubkeys #[] = .error .emptyPubkeyList := rfl

/-- Adding one key that fails key validation reports its index. -/
theorem addPubkeyPoint_invalidPubkey {pk : BLSPubkey} {e : BlsError}
    (hval : G1.keyValidatePoint pk = .error e) (agg : G1) (i : Nat) :
    addPubkeyPoint agg (pk, i) = .error (.invalidPubkey (some i)) := by
  simp [addPubkeyPoint, hval, throw, throwThe, MonadExceptOf.throw]

/-- The core aggregate verification rejects an empty key list (§2.9). -/
theorem coreAggregateVerify_empty (msgs : Array ByteArray) (sig dst : ByteArray) :
    coreAggregateVerify #[] msgs sig dst = false := rfl

/-- The core aggregate verification rejects lists of two sizes. -/
theorem coreAggregateVerify_size_ne {pks msgs : Array ByteArray} (h : pks.size ≠ msgs.size)
    (sig dst : ByteArray) : coreAggregateVerify pks msgs sig dst = false := by
  unfold coreAggregateVerify
  rw [ite_eq_left_of_eq_true _ _ (by simp [h])]

/-- The core verification rejects a signature that is not 96 bytes. -/
theorem coreVerify_badSignatureSize {sig : ByteArray} (h : sig.size ≠ 96)
    (pk msg dst : ByteArray) :
    coreVerify pk msg sig dst = false := by
  simp [coreVerify, EthLib.Base.exactBytes?_of_size_ne h]

/-- The core aggregate verification rejects a signature that is not 96 bytes. -/
theorem coreAggregateVerify_badSignatureSize {sig : ByteArray} (h : sig.size ≠ 96)
    (pks msgs : Array ByteArray) (dst : ByteArray) :
    coreAggregateVerify pks msgs sig dst = false := by
  simp [coreAggregateVerify, EthLib.Base.exactBytes?_of_size_ne h]

/-- The core verification rejects a public key that is not 48 bytes. -/
theorem coreVerify_badPubkeySize {pk : ByteArray} (h : pk.size ≠ 48) (msg sig dst : ByteArray) :
    coreVerify pk msg sig dst = false := by
  unfold coreVerify
  rw [EthLib.Base.exactBytes?_of_size_ne h]
  -- Every branch of the signature checks ends on the rejected key.
  split
  · simp
  · split <;> simp

/-- The secret key decoder rejects an input that is not 32 bytes long. -/
theorem SecretKey.fromBytes_of_size_ne {bytes : ByteArray} (h : bytes.size ≠ 32) :
    SecretKey.fromBytes bytes = .error .invalidSecretKey := by
  unfold SecretKey.fromBytes
  rw [EthLib.Base.exactBytes?_of_size_ne h]

/-- On 32 bytes, the key decoder gives a key exactly when the scalar decoder gives its value. -/
theorem SecretKey.fromBytes_packBytes_eq_ok_iff {b : Vector UInt8 32} {sk : SecretKey} :
    SecretKey.fromBytes (packBytes b) = .ok sk ↔ Fr.fromBytesBE b = .ok sk.val := by
  obtain ⟨x, hx⟩ := sk
  unfold SecretKey.fromBytes
  simp only [exactBytes?_packBytes]
  cases hd : Fr.fromBytesBE b with
  | error e => simp
  | ok y =>
    by_cases hy : y = 0
    · simp [hy, Ne.symm hx]
    · simp [hy, Subtype.ext_iff, eq_comm]

/-- Decoding the 32 bytes of a secret key gives it back. -/
theorem SecretKey.fromBytes_toBytesBE (sk : SecretKey) :
    SecretKey.fromBytes sk.val.toBytesBE = .ok sk := by
  -- The encoding is the packed vector of its own bytes.
  rw [← packBytes_mk_data sk.val.toBytesBE (Fr.size_data_toBytesBE sk.val)]
  exact SecretKey.fromBytes_packBytes_eq_ok_iff.mpr (Fr.fromBytesBE_toBytesBE sk.val)

/-- The secret key decoder rejects the encoding of zero (§2.3). -/
theorem SecretKey.fromBytes_zero :
    SecretKey.fromBytes (0 : Fr).toBytesBE = .error .invalidSecretKey := by
  rw [← packBytes_mk_data (0 : Fr).toBytesBE (Fr.size_data_toBytesBE 0)]
  unfold SecretKey.fromBytes
  simp only [exactBytes?_packBytes]
  rw [Fr.fromBytesBE_toBytesBE]
  simp

end EthLib.Cryptography.Bls.Signatures

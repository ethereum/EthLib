module

public import EthLib.Cryptography.Proofs.Bls.Security.Refinement

/-!
# Proofs: EthLib's proof-of-possession checks are tests of the scheme

These are the checks of the proof-of-possession scheme of the BLS draft, §3.3.

<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-3.3>

Each check below takes the hash to `G2` as an argument instead of computing it.

With the hash under the key tag, the first is EthLib's proof verification, §3.3.3.

With the hash under the message tag, the second is EthLib's fast aggregate verification, §3.3.4.

An accepted check is a test of the scheme on the decoded group elements.

For fast aggregate verification, the key of that test is the sum of the decoded keys.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security

open EthLib.Cryptography.Bls EthLib.Cryptography.Bls.Signatures

/-! ## Proofs of possession -/

/-- With the hash of the key under the key tag, the check is EthLib's proof verification. -/
theorem byteVerify_eq_popVerify (pk proof : ByteArray) :
    byteVerify pk proof (hashPointWith POP_DST pk) = popVerify pk proof :=
  byteVerify_hashPointWith POP_DST pk pk proof

/-- EthLib's proof of possession compresses a point of `sk • H'(pk)`.

Here `pk` is the public key of `sk`, and `H'` the hash under the key tag. -/
theorem popProve_eq (sk : SecretKey) :
    ∃ proof, popProve sk = .ok proof ∧
      (⟨proof.toArray⟩ : ByteArray) =
        G2Sub.encode (Scalar.ofFr sk.val • hashPointWith POP_DST (pkBytes sk)) := by
  obtain ⟨hQ, hv, -⟩ := hashRepWith_spec POP_DST (pkBytes sk)
  have hs : popProve sk =
      .ok (pointToSignature (G2.mul (hashRepWith POP_DST (pkBytes sk)) sk.val)) :=
    coreSign_eq hQ sk
  refine ⟨_, hs, ?_⟩
  rw [pointToSignature_bytes]
  refine G2.compress_congr (G2.valid_mul hv sk.val) (G2Sub.represents_rep _).1 ?_
  rw [G2.toPoint_mul hv, G2Sub.toPoint_rep, G2Sub.coe_smul, Scalar.val_ofFr]
  rfl

/-! ## Fast aggregate verification -/

/-- Fast aggregate verification with the hash `h` in place of the hash of the message.

It sums the validated keys, then checks the signature under the sum, as §3.3.4 does. -/
noncomputable def byteFastAggregateVerify
    (pubkeys : Array ByteArray) (sigBytes : ByteArray) (h : G2Sub) : Bool :=
  match aggregatePubkeyPoint pubkeys with
  | .error _ => false
  | .ok agg => byteVerify (G1.compress agg) sigBytes h

/-- With the hash of the message under the message tag, it is EthLib's fast aggregate check. -/
theorem byteFastAggregateVerify_hashPoint (pubkeys : Array ByteArray) (msg sig : ByteArray) :
    byteFastAggregateVerify pubkeys sig (hashPoint msg) = fastAggregateVerify pubkeys msg sig := by
  unfold byteFastAggregateVerify fastAggregateVerify
  cases aggregatePubkeyPoint pubkeys with
  | error _ => rfl
  | ok agg => exact byteVerify_hashPoint _ _ _

/-- A fold of the key sum that succeeds decodes every key.

The point it ends with is the starting sum plus the decoded keys. -/
private theorem foldlM_decode (ks : List ByteArray) :
    ∀ (idx : Nat) (acc R : G1) (a : G1Sub), G1.Valid acc →
    G1.toPoint acc = a →
    (ks.zipIdx idx).foldlM addPubkeyPoint acc = .ok R →
    ∃ xs : List G1Sub, ks.mapM decodeKey = some xs ∧ G1.Valid R ∧
      G1.toPoint R = ((a + xs.sum : G1Sub) : G1.curve.toAffine.Point) := by
  induction ks with
  | nil =>
    intro _ acc R a hv ha h
    obtain rfl := Except.ok.inj h.symm
    exact ⟨[], rfl, hv, by simpa using ha⟩
  | cons pk rest ih =>
    intro idx acc R a hv ha h
    simp only [List.zipIdx_cons, List.foldlM_cons, addPubkeyPoint] at h
    by_cases hsize : pk.size ≠ 48
    · simp [hsize, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp only [hsize, ↓reduceIte] at h
      cases hp : G1.keyValidatePoint pk with
      | error _ => simp [hp, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      | ok P =>
        simp only [hp, pure, Except.pure, bind, Except.bind] at h
        obtain ⟨hpu, hPv, -, hord⟩ := G1.keyValidatePoint_eq_ok_iff.mp hp
        obtain ⟨x, hdk, hx⟩ := exists_decodeKey_of_uncompress hpu
          ((G1.inSubgroup_iff_modulus_smul_eq_zero hPv).mpr hord)
        obtain ⟨xs, hxs, hRv, hRe⟩ := ih (idx + 1) (acc.add P) R (a + x) (G1.valid_add hv hPv)
          (by rw [G1.toPoint_add hv hPv, ha, hx, AddSubgroup.coe_add]) h
        refine ⟨x :: xs, ?_, hRv, ?_⟩
        · simp [List.mapM_cons, hdk, hxs]
        · rw [hRe, List.sum_cons, add_assoc]

/-- A key sum that succeeds decodes every key, and is a point of the sum of the decoded keys. -/
private theorem exists_mapM_decodeKey {pubkeys : Array ByteArray} {R : G1}
    (h : aggregatePubkeyPoint pubkeys = .ok R) :
    ∃ xs : List G1Sub, pubkeys.toList.mapM decodeKey = some xs ∧ G1.Valid R ∧
      G1.toPoint R = ((xs.sum : G1Sub) : G1.curve.toAffine.Point) := by
  obtain ⟨l, rfl⟩ : ∃ l, pubkeys = l.toArray := ⟨pubkeys.toList, by simp⟩
  unfold aggregatePubkeyPoint at h
  by_cases he : l.toArray.isEmpty = true
  · simp [he, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [he, Bool.false_eq_true, ↓reduceIte, Array.zipIdx_toArray, List.foldlM_toArray] at h
    obtain ⟨xs, hxs, hRv, hRe⟩ := foldlM_decode l 0 G1.zero R 0 G1.valid_zero
      (by simpa using G1.toPoint_zero) h
    exact ⟨xs, by simpa using hxs, hRv, by rw [hRe, zero_add]⟩

/-- An accepted fast aggregate check decodes every key.

Its signature passes the scheme's test under the sum of the decoded keys. -/
theorem isDh_of_byteFastAggregateVerify {pubkeys : Array ByteArray} {sig : ByteArray}
    {h : G2Sub} (hv : byteFastAggregateVerify pubkeys sig h = true) :
    ∃ xs : List G1Sub, pubkeys.toList.mapM decodeKey = some xs ∧
      blsScheme.isDh xs.sum h ((decodeSignature sig).getD 0) = true := by
  cases ha : aggregatePubkeyPoint pubkeys with
  | error _ => simp [byteFastAggregateVerify, ha] at hv
  | ok R =>
    have hv' : byteVerify (G1.compress R) sig h = true := by
      simpa [byteFastAggregateVerify, ha] using hv
    obtain ⟨xs, hxs, hRv, hRe⟩ := exists_mapM_decodeKey ha
    refine ⟨xs, hxs, ?_⟩
    obtain ⟨x, hdk, hdh⟩ := exists_decodeKey_isDh_of_byteVerify hv'
    have h1 := encode_eq_of_decodeKey hdk
    have h2 : G1Sub.encode xs.sum = G1.compress R := G1Sub.encode_eq_compress hRv hRe
    have h3 := decodeKey_encode x
    rw [h1, ← h2, decodeKey_encode] at h3
    rw [Option.some.inj h3]
    exact hdh

end EthLib.Cryptography.Bls.Security

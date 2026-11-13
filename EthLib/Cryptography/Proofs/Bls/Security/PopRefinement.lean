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

open EthLib.Base EthLib.Cryptography.Bls EthLib.Cryptography.Bls.Signatures

/-! ## Proofs of possession -/

/-- With the hash of the key under the key tag, the check is EthLib's proof verification. -/
theorem byteVerify_eq_popVerify (pk : BLSPubkey) (proof : BLSSignature) :
    byteVerify (packBytes pk) (packBytes proof) (hashPointWith POP_DST (packBytes pk)) =
      popVerify pk proof :=
  byteVerify_hashPointWith POP_DST (packBytes pk) (packBytes pk) (packBytes proof)

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

/-- Add the point of one key in bytes to a running sum, if the key passes key validation. -/
def byteAddKey (agg : G1) (pk : ByteArray) : Except BlsError G1 :=
  G1.add agg <$> G1.keyValidatePoint pk

/-- Fast aggregate verification on keys in bytes, with the hash `h` in place of the message hash.

It sums the validated keys, then checks the signature under the sum, as §3.3.4 does.

It rejects an empty list and a key that fails key validation, which checks its size. -/
noncomputable def byteFastAggregateVerify
    (pubkeys : Array ByteArray) (sigBytes : ByteArray) (h : G2Sub) : Bool :=
  if pubkeys.isEmpty then false
  else
    match pubkeys.foldlM byteAddKey G1.zero with
    | .error _ => false
    | .ok agg => byteVerify (G1.compress agg) sigBytes h

/-- The sum on bytes succeeds exactly when the key sum succeeds, and with the same point. -/
private theorem foldlM_byteAddKey (l : List BLSPubkey) (idx : Nat) (acc R : G1) :
    (l.map packBytes).foldlM byteAddKey acc = .ok R ↔
      (l.zipIdx idx).foldlM addPubkeyPoint acc = .ok R := by
  induction l generalizing idx acc with
  | nil => rfl
  | cons pk l ih =>
    simp only [List.map_cons, List.zipIdx_cons, List.foldlM_cons, byteAddKey, addPubkeyPoint]
    cases G1.keyValidatePoint (packBytes pk) with
    | error _ => simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, Functor.map,
        Except.map]
    | ok P => exact ih (idx + 1) (G1.add acc P)

/-- With keys in bytes and the hash of the message, it is EthLib's fast aggregate check. -/
theorem byteFastAggregateVerify_hashPoint (pubkeys : Array BLSPubkey) (msg : ByteArray)
    (sig : BLSSignature) :
    byteFastAggregateVerify (pubkeys.map packBytes) (packBytes sig) (hashPoint msg) =
      fastAggregateVerify pubkeys msg sig := by
  obtain ⟨l, rfl⟩ : ∃ l, pubkeys = l.toArray := ⟨pubkeys.toList, by simp⟩
  by_cases he : l.toArray.isEmpty = true
  · obtain rfl : l = [] := by simpa using he
    rw [fastAggregateVerify_empty]
    simp [byteFastAggregateVerify]
  · unfold byteFastAggregateVerify fastAggregateVerify aggregatePubkeyPoint
    have he' : (l.map packBytes).toArray.isEmpty = false := by simpa using he
    simp only [List.map_toArray, he', he, Bool.false_eq_true, ↓reduceIte, Array.zipIdx_toArray,
      List.foldlM_toArray, List.map_toArray]
    cases hb : (l.map packBytes).foldlM byteAddKey G1.zero with
    | error _ =>
      cases ha : (l.zipIdx 0).foldlM addPubkeyPoint G1.zero with
      | error _ => rfl
      | ok R => cases hb.symm.trans ((foldlM_byteAddKey l 0 G1.zero R).mpr ha)
    | ok R =>
      rw [(foldlM_byteAddKey l 0 G1.zero R).mp hb]
      dsimp only
      rw [← packBytes_pointToPubkey]
      exact byteVerify_hashPoint _ _ _

/-- A fold of the key sum that succeeds decodes every key.

The point it ends with is the starting sum plus the decoded keys. -/
private theorem foldlM_decode (ks : List ByteArray) :
    ∀ (acc R : G1) (a : G1Sub), G1.Valid acc →
    G1.toPoint acc = a →
    ks.foldlM byteAddKey acc = .ok R →
    ∃ xs : List G1Sub, ks.mapM decodeKey = some xs ∧ G1.Valid R ∧
      G1.toPoint R = ((a + xs.sum : G1Sub) : G1.curve.toAffine.Point) := by
  induction ks with
  | nil =>
    intro acc R a hv ha h
    obtain rfl := Except.ok.inj h.symm
    exact ⟨[], rfl, hv, by simpa using ha⟩
  | cons pk rest ih =>
    intro acc R a hv ha h
    simp only [List.foldlM_cons, byteAddKey] at h
    cases hp : G1.keyValidatePoint pk with
    | error _ => simp [hp, bind, Except.bind, Functor.map, Except.map] at h
    | ok P =>
      simp only [hp, Functor.map, Except.map, bind, Except.bind] at h
      obtain ⟨hpu, hPv, -, hord⟩ := G1.keyValidatePoint_eq_ok_iff.mp hp
      obtain ⟨x, hdk, hx⟩ := exists_decodeKey_of_uncompress hpu
        ((G1.inSubgroup_iff_modulus_smul_eq_zero hPv).mpr hord)
      obtain ⟨xs, hxs, hRv, hRe⟩ := ih (acc.add P) R (a + x) (G1.valid_add hv hPv)
        (by rw [G1.toPoint_add hv hPv, ha, hx, AddSubgroup.coe_add]) h
      refine ⟨x :: xs, ?_, hRv, ?_⟩
      · simp [List.mapM_cons, hdk, hxs]
      · rw [hRe, List.sum_cons, add_assoc]

/-- A key sum that succeeds decodes every key, and is a point of the sum of the decoded keys. -/
private theorem exists_mapM_decodeKey {pubkeys : Array ByteArray} {R : G1}
    (h : pubkeys.foldlM byteAddKey G1.zero = .ok R) :
    ∃ xs : List G1Sub, pubkeys.toList.mapM decodeKey = some xs ∧ G1.Valid R ∧
      G1.toPoint R = ((xs.sum : G1Sub) : G1.curve.toAffine.Point) := by
  obtain ⟨l, rfl⟩ : ∃ l, pubkeys = l.toArray := ⟨pubkeys.toList, by simp⟩
  rw [List.foldlM_toArray] at h
  obtain ⟨xs, hxs, hRv, hRe⟩ := foldlM_decode l G1.zero R 0 G1.valid_zero
    (by simpa using G1.toPoint_zero) h
  exact ⟨xs, by simpa using hxs, hRv, by rw [hRe, zero_add]⟩

/-- An accepted fast aggregate check decodes every key.

Its signature passes the scheme's test under the sum of the decoded keys. -/
theorem isDh_of_byteFastAggregateVerify {pubkeys : Array ByteArray} {sig : ByteArray}
    {h : G2Sub} (hv : byteFastAggregateVerify pubkeys sig h = true) :
    ∃ xs : List G1Sub, pubkeys.toList.mapM decodeKey = some xs ∧
      blsScheme.isDh xs.sum h ((decodeSignature sig).getD 0) = true := by
  by_cases he : pubkeys.isEmpty = true
  · simp [byteFastAggregateVerify, he] at hv
  cases ha : pubkeys.foldlM byteAddKey G1.zero with
  | error _ => simp [byteFastAggregateVerify, he, ha] at hv
  | ok R =>
    have hv' : byteVerify (G1.compress R) sig h = true := by
      simpa [byteFastAggregateVerify, he, ha] using hv
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

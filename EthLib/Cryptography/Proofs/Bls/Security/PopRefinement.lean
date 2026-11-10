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
  | none => false
  | some agg => byteVerify (G1.compress agg) sigBytes h

/-- With the hash of the message under the message tag, it is EthLib's fast aggregate check. -/
theorem byteFastAggregateVerify_hashPoint (pubkeys : Array ByteArray) (msg sig : ByteArray) :
    byteFastAggregateVerify pubkeys sig (hashPoint msg) = fastAggregateVerify pubkeys msg sig := by
  unfold byteFastAggregateVerify fastAggregateVerify
  cases aggregatePubkeyPoint pubkeys with
  | none => rfl
  | some agg => exact byteVerify_hashPoint _ _ _

/-- The loop of the key sum either stops with nothing or decodes every key.

If it does not stop, the sum it ends with is the starting sum plus the decoded keys. -/
private theorem forIn_decode (ks : List ByteArray) :
    ∀ (acc : G1) (a : G1Sub) (o : Option (Option G1)) (R : G1), G1.Valid acc →
    G1.toPoint acc = a →
    forIn (m := Id) ks ((none : Option (Option G1)), acc)
        (fun pk (s : Option (Option G1) × G1) =>
          if (decide (pk.size ≠ 48) || !(G1.keyValidate pk).isOk) = true then
            pure (ForInStep.done (some none, s.2))
          else
            match G1.uncompress pk with
            | .error _ => pure (ForInStep.done (some none, s.2))
            | .ok p => pure (ForInStep.yield (none, s.2.add p))) = (o, R) →
    o = some none ∨ (o = none ∧ ∃ xs : List G1Sub, ks.mapM decodeKey = some xs ∧ G1.Valid R ∧
      G1.toPoint R = ((a + xs.sum : G1Sub) : G1.curve.toAffine.Point)) := by
  induction ks with
  | nil =>
    intro acc a o R hv ha h
    have h' : (none, acc) = (o, R) := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    exact Or.inr ⟨rfl, [], rfl, hv, by simpa using ha⟩
  | cons pk rest ih =>
    intro acc a o R hv ha h
    rw [List.forIn_cons] at h
    by_cases hc : (decide (pk.size ≠ 48) || !(G1.keyValidate pk).isOk) = true
    · simp only [hc, ↓reduceIte] at h
      change (some none, acc) = (o, R) at h
      exact Or.inl (Prod.mk.inj h).1.symm
    · simp only [hc] at h
      have hc' := hc
      simp at hc'
      obtain ⟨P, hp⟩ := G1.exists_keyValidatePoint_of_isOk hc'.2
      obtain ⟨hpu, hPv, -, hord⟩ := G1.keyValidatePoint_eq_ok_iff.mp hp
      obtain ⟨x, hdk, hx⟩ := exists_decodeKey_of_uncompress hpu
        ((G1.inSubgroup_iff_modulus_smul_eq_zero hPv).mpr hord)
      simp only [hpu] at h
      rcases ih (acc.add P) (a + x) o R (G1.valid_add hv hPv)
        (by rw [G1.toPoint_add hv hPv, ha, hx, AddSubgroup.coe_add]) h with
        ho | ⟨ho, xs, hxs, hRv, hRe⟩
      · exact Or.inl ho
      · refine Or.inr ⟨ho, x :: xs, ?_, hRv, ?_⟩
        · simp [List.mapM_cons, hdk, hxs]
        · rw [hRe, List.sum_cons, add_assoc]

/-- A key sum that succeeds decodes every key, and is a point of the sum of the decoded keys. -/
private theorem exists_mapM_decodeKey {pubkeys : Array ByteArray} {R : G1}
    (h : aggregatePubkeyPoint pubkeys = some R) :
    ∃ xs : List G1Sub, pubkeys.toList.mapM decodeKey = some xs ∧ G1.Valid R ∧
      G1.toPoint R = ((xs.sum : G1Sub) : G1.curve.toAffine.Point) := by
  obtain ⟨l, rfl⟩ : ∃ l, pubkeys = l.toArray := ⟨pubkeys.toList, by simp⟩
  unfold aggregatePubkeyPoint at h
  by_cases he : l.toArray.isEmpty = true
  · simp [he] at h
  · simp only [he, Bool.false_eq_true, ↓reduceIte, List.forIn_toArray] at h
    rw [Id.run_bind] at h
    generalize hL : forIn (m := Id) l ((none : Option (Option G1)), (G1.zero : G1)) _ = L at h
    obtain ⟨o, R'⟩ := L
    rcases forIn_decode l G1.zero 0 o R' G1.valid_zero (by simpa using G1.toPoint_zero) hL with
      ho | ⟨ho, xs, hxs, hRv, hRe⟩
    · subst ho
      simp [Id.run] at h
    · subst ho
      have hR : R' = R := Option.some.inj h
      subst hR
      exact ⟨xs, by simpa using hxs, hRv, by rw [hRe, zero_add]⟩

/-- An accepted fast aggregate check decodes every key.

Its signature passes the scheme's test under the sum of the decoded keys. -/
theorem isDh_of_byteFastAggregateVerify {pubkeys : Array ByteArray} {sig : ByteArray}
    {h : G2Sub} (hv : byteFastAggregateVerify pubkeys sig h = true) :
    ∃ xs : List G1Sub, pubkeys.toList.mapM decodeKey = some xs ∧
      blsScheme.isDh xs.sum h ((decodeSignature sig).getD 0) = true := by
  cases ha : aggregatePubkeyPoint pubkeys with
  | none => simp [byteFastAggregateVerify, ha] at hv
  | some R =>
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

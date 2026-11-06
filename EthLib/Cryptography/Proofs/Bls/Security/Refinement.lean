module

public import EthLib.Cryptography.Proofs.Bls.Security.Reduction
public import EthLib.Cryptography.Proofs.Bls.SignaturesUnique
public import Mathlib.Algebra.Module.ZMod

/-!
# Proofs: EthLib's BLS signatures are the scheme of the game

The groups of the game are the multiples of the generators of `G1` and `G2`.

Under the pairing law, EthLib's pairing check is a sound test of co-Diffie-Hellman tuples.

EthLib signs and verifies as the scheme does, with `H(m)` the hash to `G2` of `m`.

With that hash taken as a random oracle, the bound of the game applies to this scheme.

The byte game gives the adversary compressed keys, hashes and signatures.

Decoding its output gives a group forger with at least the same advantage.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security

open OracleComp ENNReal
open EthLib.Cryptography.Bls EthLib.Cryptography.Bls.Signatures
open scoped EthLib.Cryptography.Bls.Fr

/-- The scalars: the integers modulo the group order `r`. -/
abbrev Scalar := ZMod Fr.modulus

instance : NeZero Fr.modulus := ⟨Fr.modulus_prime.ne_zero⟩

/-- A scalar of the specification, read as a scalar of the game.

Both stand for integers below `r`. -/
def Scalar.ofFr (k : Fr) : Scalar := Fr.toZMod k

/-- A scalar of the game, read as a scalar of the specification. -/
instance : Coe Scalar Fr := ⟨Fr.toZMod.symm⟩

/-- A scalar read in the specification and back is itself. -/
theorem Scalar.ofFr_coe (a : Scalar) : Scalar.ofFr (a : Fr) = a :=
  Fr.toZMod.apply_symm_apply a

/-- A scalar of the specification read in the game and back is itself. -/
theorem Scalar.coe_ofFr (k : Fr) : ((Scalar.ofFr k : Scalar) : Fr) = k :=
  Fr.toZMod.symm_apply_apply k

/-- A scalar and its reading in the specification have the same value. -/
theorem Scalar.val_coe (a : Scalar) : (a : Fr).val = a.val := by
  rw [Fr.val_eq]
  exact congrArg ZMod.val (Fr.toZMod.apply_symm_apply a)

/-- A scalar of the specification and its reading in the game have the same value. -/
theorem Scalar.val_ofFr (k : Fr) : (Scalar.ofFr k).val = k.val :=
  (Fr.val_eq k).symm

/-- The multiples of the generator of `G1`, a group of order `r`. -/
noncomputable abbrev G1Sub : AddSubgroup G1.curve.toAffine.Point :=
  AddSubgroup.zmultiples (G1.toPoint G1.generator)

/-- The multiples of the generator of `G2`, a group of order `r`. -/
noncomputable abbrev G2Sub : AddSubgroup G2.curve.toAffine.Point :=
  AddSubgroup.zmultiples (G2.toPoint G2.generator)

/-- `r` times a multiple of a point of order `r` vanishes. -/
theorem modulus_nsmul_of_mem {A : Type} [AddCommGroup A] {g x : A} (hg : Fr.modulus • g = 0)
    (hx : x ∈ AddSubgroup.zmultiples g) : Fr.modulus • x = 0 := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  rw [← natCast_zsmul, smul_comm, natCast_zsmul, hg, zsmul_zero]

noncomputable instance : Module Scalar G1Sub :=
  AddCommGroup.zmodModule fun x => Subtype.ext
    (modulus_nsmul_of_mem G1.modulus_smul_generator x.2)

noncomputable instance : Module Scalar G2Sub :=
  AddCommGroup.zmodModule fun x => Subtype.ext
    (modulus_nsmul_of_mem G2.modulus_smul_generator x.2)

/-- The generator of `G1`, as an element of its multiples. -/
noncomputable def g1 : G1Sub := ⟨G1.toPoint G1.generator, AddSubgroup.mem_zmultiples _⟩

/-- The generator of `G2`, as an element of its multiples. -/
noncomputable def g2 : G2Sub := ⟨G2.toPoint G2.generator, AddSubgroup.mem_zmultiples _⟩

/-- A scalar acts on the multiples of `g1` through its value below `r`. -/
theorem G1Sub.coe_smul (a : Scalar) (x : G1Sub) : ((a • x : G1Sub) : G1.curve.toAffine.Point) =
    a.val • (x : G1.curve.toAffine.Point) :=
  rfl

/-- A scalar acts on the multiples of `g2` through its value below `r`. -/
theorem G2Sub.coe_smul (a : Scalar) (x : G2Sub) : ((a • x : G2Sub) : G2.curve.toAffine.Point) =
    a.val • (x : G2.curve.toAffine.Point) :=
  rfl

/-! ## Points that represent the group elements -/

/-- Every multiple of `g1` is `k • g1` for one scalar `k`. -/
theorem G1Sub.exists_ofFr (x : G1Sub) : ∃ k : Fr, G1.ofFr k = x := by
  have hm := x.2
  rw [mem_zmultiples_iff_mem_range_addOrderOf, G1.addOrderOf_toPoint_generator] at hm
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
  exact ⟨Fr.ofNat i, by rw [G1.ofFr, Fr.val_ofNat_of_lt (Finset.mem_range.mp hi)]; exact he⟩

/-- Every multiple of `g2` is `k • g2` for one scalar `k`. -/
theorem G2Sub.exists_ofFr (x : G2Sub) : ∃ k : Fr, G2.ofFr k = x := by
  have hm := x.2
  rw [mem_zmultiples_iff_mem_range_addOrderOf, G2.addOrderOf_toPoint_generator] at hm
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
  exact ⟨Fr.ofNat i, by rw [G2.ofFr, Fr.val_ofNat_of_lt (Finset.mem_range.mp hi)]; exact he⟩

/-- Distinct scalars give distinct multiples of `g1`, because `g1` has order `r`. -/
theorem G1.ofFr_injective : Function.Injective G1.ofFr := fun k k' h =>
  Fr.ext (Nat.ModEq.eq_of_lt_of_lt (by
    have hk := nsmul_eq_nsmul_iff_modEq.mp h
    rwa [G1.addOrderOf_toPoint_generator] at hk) (Fr.val_lt k) (Fr.val_lt k'))

/-- Distinct scalars give distinct multiples of `g2`, because `g2` has order `r`. -/
theorem G2.ofFr_injective : Function.Injective G2.ofFr := fun k k' h =>
  Fr.ext (Nat.ModEq.eq_of_lt_of_lt (by
    have hk := nsmul_eq_nsmul_iff_modEq.mp h
    rwa [G2.addOrderOf_toPoint_generator] at hk) (Fr.val_lt k) (Fr.val_lt k'))

/-- The scalar `k` of a multiple `k • g1`. -/
noncomputable def G1Sub.dlog (x : G1Sub) : Scalar := Scalar.ofFr (G1Sub.exists_ofFr x).choose

/-- The scalar `k` of a multiple `k • g2`. -/
noncomputable def G2Sub.dlog (x : G2Sub) : Scalar := Scalar.ofFr (G2Sub.exists_ofFr x).choose

/-- The scalar of `a • g1` is `a`. -/
theorem G1Sub.dlog_smul_g1 (a : Scalar) : G1Sub.dlog (a • g1) = a := by
  have h : (G1Sub.exists_ofFr (a • g1)).choose = (a : Fr) := by
    apply G1.ofFr_injective
    rw [(G1Sub.exists_ofFr _).choose_spec, G1Sub.coe_smul, G1.ofFr, Scalar.val_coe]
    rfl
  rw [G1Sub.dlog, h, Scalar.ofFr_coe]

/-- A multiple of `g2` is its scalar times `g2`. -/
theorem G2Sub.ofFr_dlog (x : G2Sub) : G2.ofFr (G2Sub.dlog x) = x := by
  rw [G2Sub.dlog, Scalar.coe_ofFr]
  exact (G2Sub.exists_ofFr x).choose_spec

/-- A valid point of `G2` for a multiple of `g2`. -/
noncomputable def G2Sub.rep (x : G2Sub) : G2 := G2.mul G2.generator (G2Sub.dlog x)

/-- The chosen point of `G2` represents the scalar of the multiple. -/
theorem G2Sub.represents_rep (x : G2Sub) : G2.Represents (G2Sub.rep x) (G2Sub.dlog x) :=
  G2.represents_mul_generator _

/-- A valid point of `G1` for a multiple of `g1`. -/
noncomputable def G1Sub.rep (x : G1Sub) : G1 := G1.mul G1.generator (G1Sub.dlog x)

/-- The chosen point of `G1` represents the scalar of the multiple. -/
theorem G1Sub.represents_rep (x : G1Sub) : G1.Represents (G1Sub.rep x) (G1Sub.dlog x) :=
  G1.represents_mul_generator _

/-! ## The scheme -/

/-- EthLib's BLS scheme over the multiples of the generators.

A signature `σ` on `h` verifies under `P` when the pairing check accepts `(g1, σ)` and `(-P, h)`.

That is the check that EthLib's verification runs on decoded points. -/
noncomputable def blsScheme : Scheme G1Sub G2Sub where
  g₁ := g1
  g₂ := g2
  isDh P h σ := pairingCheck #[(G1.generator, G2Sub.rep σ), (G1.neg (G1Sub.rep P), G2Sub.rep h)]

/-- Over the scalars, the equation of the pairing check fixes the signature's scalar. -/
private theorem check_scalars_iff (c a b : Scalar) :
    1 * (c : Fr) + -(a : Fr) * (b : Fr) = 0 ↔ c = a * b := by
  rw [← map_one Fr.toZMod.symm, ← map_neg, ← map_mul, ← map_mul, ← map_add,
    ← map_zero Fr.toZMod.symm, EmbeddingLike.apply_eq_iff_eq]
  constructor <;> intro h <;> linear_combination h

/-- Under the pairing law, the pairing check is a sound test of co-Diffie-Hellman tuples. -/
theorem blsScheme_sound (laws : PairingLaws) : blsScheme.Sound Scalar := by
  intro a h σ
  have hσ : σ = a • h ↔ G2Sub.dlog σ = a * G2Sub.dlog h := by
    rw [Subtype.ext_iff, G2Sub.coe_smul, ← G2Sub.ofFr_dlog σ, ← G2Sub.ofFr_dlog h]
    -- The action of `a` on `G2` is that of its value, which is multiplication of the scalars.
    rw [show ZMod.val a • G2.ofFr (G2Sub.dlog h) = G2.ofFr ((a * G2Sub.dlog h : Scalar) : Fr) by
      rw [show ((a * G2Sub.dlog h : Scalar) : Fr) = (a : Fr) * (G2Sub.dlog h : Fr) from
        map_mul Fr.toZMod.symm _ _, G2.ofFr_mul, Scalar.val_coe]]
    exact G2.ofFr_injective.eq_iff.trans Fr.toZMod.symm.injective.eq_iff
  change pairingCheck _ = true ↔ _
  rw [show blsScheme.g₁ = g1 from rfl,
    laws.two_pairs G1.represents_generator (G2Sub.represents_rep σ)
    (G1Sub.represents_rep _).neg (G2Sub.represents_rep h), G1Sub.dlog_smul_g1, hσ]
  exact check_scalars_iff _ _ _

/-! ## EthLib's signing and verification -/

/-- The point that the hash to `G2` gives a message under the message tag. -/
noncomputable def hashRep (msg : ByteArray) : G2 :=
  (HashToCurve.hashToG2_total_inSubgroup msg DST).choose

/-- The hash to `G2` never fails, and its point is valid and in the subgroup. -/
theorem hashRep_spec (msg : ByteArray) :
    HashToCurve.hashToG2 msg DST = .ok (hashRep msg) ∧ G2.Valid (hashRep msg) ∧
      G2.inSubgroup (hashRep msg) = true :=
  (HashToCurve.hashToG2_total_inSubgroup msg DST).choose_spec

/-- The hash to `G2` of a message under the message tag, as a multiple of `g2`.

It is the hash `H` of the scheme. -/
noncomputable def hashPoint (msg : ByteArray) : G2Sub :=
  ⟨G2.toPoint (hashRep msg), by
    obtain ⟨-, hv, hs⟩ := hashRep_spec msg
    obtain ⟨k, hk⟩ := G2.exists_mul_generator_of_inSubgroup hv hs
    rw [hk, G2.toPoint_mul_generator]
    exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _⟩

/-- EthLib's public key of `sk` compresses a point of the group element `sk • g1`. -/
theorem toPoint_skToPk (sk : SecretKey) :
    G1.toPoint (G1.mul G1.generator sk.val) = (Scalar.ofFr sk.val • g1 : G1Sub) := by
  rw [G1.toPoint_mul_generator, G1Sub.coe_smul, Scalar.val_ofFr]
  rfl

/-- EthLib signs `msg` with the compression of a point of `sk • H(msg)`. -/
theorem sign_eq (sk : SecretKey) (msg : ByteArray) :
    Signatures.sign sk msg = .ok (pointToSignature (G2.mul (hashRep msg) sk.val)) ∧
      G2.toPoint (G2.mul (hashRep msg) sk.val) = (Scalar.ofFr sk.val • hashPoint msg : G2Sub) := by
  obtain ⟨hQ, hv, -⟩ := hashRep_spec msg
  refine ⟨coreSign_eq hQ sk, ?_⟩
  rw [G2.toPoint_mul hv, G2Sub.coe_smul, Scalar.val_ofFr]
  rfl

/-- Under the pairing law, EthLib accepts exactly the signatures that decode to `sk • H(msg)`. -/
theorem verify_iff (laws : PairingLaws) (sk : SecretKey) (msg sig : ByteArray) :
    verify (pkBytes sk) msg sig = true ↔
      ∃ R, G2.uncompress sig = .ok R ∧
        G2.toPoint R = (Scalar.ofFr sk.val • hashPoint msg : G2Sub) := by
  obtain ⟨P, hP, hPrep⟩ := G1.keyValidatePoint_compress_mul sk.property
  obtain ⟨hQ, hv, hs⟩ := hashRep_spec msg
  obtain ⟨b, hb⟩ := (G2.inSubgroup_iff_exists_represents hv).mp hs
  refine (coreVerify_iff (pk := pkBytes sk) laws ((pkBytes_eq sk).symm ▸ hP) hPrep hQ hb).trans
    (exists_congr fun R => and_congr_right fun hR => ?_)
  have hpt : G2.toPoint (G2.mul G2.generator (sk.val * b)) =
      (Scalar.ofFr sk.val • hashPoint msg : G2Sub) := by
    rw [G2.toPoint_mul_generator, G2.ofFr_mul, ← G2.toPoint_mul_generator, ← hb.2,
      G2Sub.coe_smul, Scalar.val_ofFr]
    rfl
  rw [G2.Represents, hpt]
  exact and_iff_right (G2.valid_of_uncompress hR)

/-- Under the pairing law, EthLib's verification is the test of the scheme on the decoded point.

The key is `sk • g1`, and the hash is `H(msg)`. -/
theorem verify_iff_isDh (laws : PairingLaws) (sk : SecretKey) (msg sig : ByteArray) :
    verify (pkBytes sk) msg sig = true ↔
      ∃ R, G2.uncompress sig = .ok R ∧ ∃ hR : G2.toPoint R ∈ G2Sub,
        blsScheme.isDh (Scalar.ofFr sk.val • g1) (hashPoint msg) ⟨_, hR⟩ = true := by
  rw [verify_iff laws]
  refine exists_congr fun R => and_congr_right fun _ => ⟨fun h => ?_, fun ⟨hR, hd⟩ => ?_⟩
  · exact ⟨h ▸ (Scalar.ofFr sk.val • hashPoint msg).2,
      (blsScheme_sound laws _ _ _).mpr (Subtype.ext h)⟩
  · exact congrArg Subtype.val ((blsScheme_sound laws _ _ _).mp hd)

/-- **EthLib's BLS signatures are unforgeable from co-CDH**, in the random oracle model.

The oracle `H` stands for the hash to `G2` under the message tag.

The bound needs the pairing law. -/
theorem forgeAdvantage_blsScheme_le (laws : PairingLaws)
    (adversary : Adversary G1Sub G2Sub ByteArray) {q : ℕ} (hq0 : 0 < q)
    (hq : HashCallBound Scalar blsScheme adversary q) :
    forgeAdvantage Scalar blsScheme adversary ≤
      q * coCdhAdvantage Scalar g1 g2 (reduction (F := Scalar) g2 adversary q) :=
  forgeAdvantage_le blsScheme (blsScheme_sound laws) adversary hq0 hq

/-! ## The byte interface -/

/-- The canonical bytes of a subgroup element of `G1`.

The BLS draft-04, §1.3, §2.2 and Appendix A require compressed serialization.

The format is ZCash's "BLS12-381 serialization", including its three flag bits.

<https://docs.rs/bls12_381/0.8.0/bls12_381/notes/serialization/index.html>
-/
noncomputable def G1Sub.encode (P : G1Sub) : ByteArray := G1.compress (G1Sub.rep P)

/-- The canonical bytes of a subgroup element of `G2`, in the same ZCash format. -/
noncomputable def G2Sub.encode (Q : G2Sub) : ByteArray := G2.compress (G2Sub.rep Q)

/-- Decode a signature, rejecting malformed bytes and points outside the subgroup.

These are the signature checks of BLS draft-04, §2.7, steps 1 to 3.
-/
noncomputable def decodeSignature (sig : ByteArray) : Option G2Sub :=
  match hu : G2.uncompress sig with
  | .error _ => none
  | .ok R =>
    if hs : G2.inSubgroup R = true then
      some ⟨G2.toPoint R, by
        obtain ⟨k, hk⟩ := G2.exists_mul_generator_of_inSubgroup (G2.valid_of_uncompress hu) hs
        rw [hk, G2.toPoint_mul_generator]
        exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _⟩
    else none

/-- The representative of a subgroup element has that group element. -/
theorem G2Sub.toPoint_rep (Q : G2Sub) : G2.toPoint (G2Sub.rep Q) = Q := by
  rw [(G2Sub.represents_rep Q).2, G2.toPoint_mul_generator, G2Sub.ofFr_dlog]

/-- The encoded challenger key is EthLib's public key for every secret key. -/
theorem encode_publicKey (sk : SecretKey) :
    G1Sub.encode (Scalar.ofFr sk.val • g1) = pkBytes sk := by
  unfold G1Sub.encode G1Sub.rep
  rw [G1Sub.dlog_smul_g1, Scalar.coe_ofFr]
  exact (pkBytes_eq sk).symm

/-- The encoded signing answer compresses the point that `sign_eq` proves EthLib signs. -/
theorem encode_signature (sk : SecretKey) (msg : ByteArray) :
    G2Sub.encode (Scalar.ofFr sk.val • hashPoint msg) =
      G2.compress (G2.mul (hashRep msg) sk.val) := by
  have hp := (sign_eq sk msg).2
  exact G2.compress_congr (G2Sub.represents_rep (Scalar.ofFr sk.val • hashPoint msg)).1
    (G2.valid_mul (hashRep_spec msg).2.1 sk.val)
    ((G2Sub.toPoint_rep (Scalar.ofFr sk.val • hashPoint msg)).trans hp.symm)

/-- Successful decompression and a subgroup check give the decoded group element. -/
theorem decodeSignature_of_uncompress {sig : ByteArray} {R : G2}
    (hu : G2.uncompress sig = .ok R) (hs : G2.inSubgroup R = true)
    (Q : G2Sub) (hp : G2.toPoint R = Q) : decodeSignature sig = some Q := by
  unfold decodeSignature
  split
  · rename_i he'
    rw [hu] at he'
    cases he'
  · rename_i R' he'
    have hRR : R' = R := Except.ok.inj (he'.symm.trans hu)
    subst R'
    simp only [hs, dite_true, Option.some.injEq, Subtype.ext_iff]
    exact hp

/-- Decoding an encoded subgroup element returns that element, including zero. -/
theorem decodeSignature_encode (Q : G2Sub) : decodeSignature (G2Sub.encode Q) = some Q := by
  obtain ⟨R, hu, he⟩ := G2.uncompress_compress
    (G2.isOnTwist_of_valid (G2Sub.represents_rep Q).1)
  have hR := G2.valid_of_uncompress hu
  have hp := (G2.projectiveEq_eq_true_iff_toPoint_eq hR (G2Sub.represents_rep Q).1).mp he
  have hs : G2.inSubgroup R = true :=
    (G2.inSubgroup_iff_exists_represents hR).mpr
      ⟨G2Sub.dlog Q, hR, hp.trans (G2Sub.represents_rep Q).2⟩
  exact decodeSignature_of_uncompress hu hs Q (hp.trans (G2Sub.toPoint_rep Q))

/-- Accepted encodings cannot give two byte strings for the same subgroup element.

This uses the decoder's canonical-encoding theorem, not the pairing law.
-/
theorem encode_eq_of_decodeSignature {sig : ByteArray} {Q : G2Sub}
    (hd : decodeSignature sig = some Q) : G2Sub.encode Q = sig := by
  unfold decodeSignature at hd
  split at hd
  · cases hd
  · rename_i R hu
    split at hd
    · have hp : G2.toPoint R = Q := congrArg Subtype.val (Option.some.inj hd)
      change G2.compress (G2Sub.rep Q) = sig
      apply Eq.trans _ (G2.compress_uncompress hu)
      apply G2.compress_congr (G2Sub.represents_rep Q).1 (G2.valid_of_uncompress hu)
      exact (G2Sub.toPoint_rep Q).trans hp.symm
    · cases hd

/-- A byte forger sees only encodings and returns arbitrary message and signature bytes.

The two message oracles return compressed hashes and compressed signatures.
-/
abbrev ByteAdversary := Adversary ByteArray ByteArray ByteArray

/-- Encode the answers of the group oracles without changing their queries or state. -/
noncomputable def encodingImpl :
    QueryImpl (Spec ByteArray ByteArray) (OracleComp (Spec ByteArray G2Sub))
  | .inl n => query (spec := Spec ByteArray G2Sub) (.inl n)
  | .inr (.inl m) => G2Sub.encode <$> query (spec := Spec ByteArray G2Sub) (.inr (.inl m))
  | .inr (.inr m) => G2Sub.encode <$> query (spec := Spec ByteArray G2Sub) (.inr (.inr m))

/-- Run a byte forger through the encodings of the challenger's public key and oracle answers. -/
noncomputable def byteMain (adversary : ByteAdversary) (pk : G1Sub) :
    OracleComp (Spec ByteArray G2Sub) (ByteArray × ByteArray) :=
  simulateQ encodingImpl (adversary.main (G1Sub.encode pk))

/-- The group forger decodes the byte output.

A decoding failure returns zero, which can only add wins to the group game.
-/
noncomputable def ByteAdversary.toGroup (adversary : ByteAdversary) :
    Adversary G1Sub G2Sub ByteArray where
  main pk := (fun (m, sig) => (m, (decodeSignature sig).getD 0)) <$> byteMain adversary pk

/-- Verification on bytes with the random oracle's hash in place of `hashToG2`.

This is BLS draft-04, §2.7: decode, check the signature subgroup, validate the key, then pair.

The hash representative is valid and lies in the subgroup by construction.
-/
noncomputable def byteVerify (pk sig : ByteArray) (h : G2Sub) : Bool :=
  match G2.uncompress sig with
  | .error _ => false
  | .ok R => signatureSubgroupCheck R &&
    match G1.keyValidatePoint pk with
    | .error _ => false
    | .ok P => pairingCheck #[(G1.generator, R), (G1.neg P, G2Sub.rep h)]

private theorem two_pairs_congr {P : G1} {R Q Q' : G2}
    (hP : G1.Valid P) (hR : G2.Valid R) (hQ : G2.Valid Q) (hQ' : G2.Valid Q')
    (he : G2.toPoint Q = G2.toPoint Q') :
    pairingCheck #[(G1.generator, R), (G1.neg P, Q)] =
      pairingCheck #[(G1.generator, R), (G1.neg P, Q')] := by
  apply pairingCheck_congr
    (ps := #[(G1.generator, R), (G1.neg P, Q)])
    (qs := #[(G1.generator, R), (G1.neg P, Q')]) rfl
  intro i hi
  change i < 2 at hi
  cases i with
  | zero => exact ⟨G1.valid_generator, G1.valid_generator, rfl, hR, hR, rfl⟩
  | succ i =>
    have hi0 : i = 0 := by omega
    subst i
    exact ⟨G1.valid_neg hP, G1.valid_neg hP, rfl, hQ, hQ', he⟩

/-- Replacing the random oracle with EthLib's hash gives EthLib's byte verification.

No pairing law is needed: the pairing check depends only on valid group elements.
-/
theorem byteVerify_hashPoint (pk msg sig : ByteArray) :
    byteVerify pk sig (hashPoint msg) = verify pk msg sig := by
  obtain ⟨hQ, hv, -⟩ := hashRep_spec msg
  unfold byteVerify verify coreVerify
  rw [hQ]
  cases hu : G2.uncompress sig with
  | error e => rfl
  | ok R =>
    cases hp : G1.keyValidatePoint pk with
    | error e => rfl
    | ok P =>
      apply congrArg (fun b => signatureSubgroupCheck R && b)
      exact two_pairs_congr (G1.keyValidatePoint_eq_ok_iff.mp hp).2.1
        (G2.valid_of_uncompress hu) (G2Sub.represents_rep (hashPoint msg)).1 hv
        (G2Sub.toPoint_rep (hashPoint msg))

/-- The byte game keeps the group game's scalar distribution, including zero.

Key validation rejects the zero key, so that run loses in the byte game.

Freshness means a message never submitted to signing, as in BLS01, §3, Definition 3.1.

A signed message loses even with different signature bytes, not just with a repeated pair.
-/
noncomputable def byteExperiment (adversary : ByteAdversary) :
    ProbComp (Bool × State Scalar ByteArray) := by
  classical
  exact do
    let a ← $ᵗ Scalar
    let pk := a • g1
    let ((m, sig, h), st) ← (simulateQ (impl g2 a) (do
      let (m, sig) ← byteMain adversary pk
      let h ← query (spec := Spec ByteArray G2Sub) (.inr (.inl m))
      return (m, sig, h))).run State.init
    return (decide (m ∉ st.signed) && byteVerify (G1Sub.encode pk) sig h, st)

/-- The probability of an accepted byte forgery on a fresh message. -/
noncomputable def byteForgeAdvantage (adversary : ByteAdversary) : ℝ≥0∞ :=
  Pr{let z ← byteExperiment adversary}[z.1 = true]

/-- Every accepted byte signature gives a winning group signature for the same key and hash. -/
theorem isDh_of_byteVerify (laws : PairingLaws) (a : Scalar) (sig : ByteArray) (h : G2Sub)
    (hv : byteVerify (G1Sub.encode (a • g1)) sig h = true) :
    blsScheme.isDh (a • g1) h (decodeSignature sig |>.getD 0) = true := by
  cases hu : G2.uncompress sig with
  | error e => simp [byteVerify, hu] at hv
  | ok R =>
    have hRv := G2.valid_of_uncompress hu
    have hs : G2.inSubgroup R = true := by
      exact (Bool.and_eq_true_iff.mp
        (by simpa only [byteVerify, hu, signatureSubgroupCheck] using hv)).1
    cases hp : G1.keyValidatePoint (G1Sub.encode (a • g1)) with
    | error e => simp [byteVerify, hu, hp] at hv
    | ok P =>
      have hPv := (G1.keyValidatePoint_eq_ok_iff.mp hp).2.1
      have hrep := G1Sub.represents_rep (a • g1)
      obtain ⟨P', hp', he⟩ := G1.uncompress_compress hrep.1
      have hPP : P = P' := Except.ok.inj
        (((G1.keyValidatePoint_eq_ok_iff.mp hp).1).symm.trans hp')
      have hPa : G1.Represents P (a : Fr) := by
        refine ⟨hPv, ?_⟩
        rw [hPP, he, hrep.2, G1Sub.dlog_smul_g1]
      obtain ⟨c, hc⟩ := (G2.inSubgroup_iff_exists_represents hRv).mp hs
      have hv' : pairingCheck #[(G1.generator, R), (G1.neg P, G2Sub.rep h)] = true := by
        simpa [byteVerify, hu, hp, signatureSubgroupCheck, hs] using hv
      -- The pairing equation fixes the decoded signature's scalar.
      have heq := (laws.two_pairs G1.represents_generator hc hPa.neg
        (G2Sub.represents_rep h)).mp hv'
      have hc' := (check_scalars_iff (Scalar.ofFr c) a (G2Sub.dlog h)).mp
        (by simpa only [Scalar.coe_ofFr] using heq)
      have hd : (decodeSignature sig |>.getD 0).val = G2.toPoint R := by
        unfold decodeSignature
        split
        · rename_i he
          rw [hu] at he
          cases he
        · rename_i R' he
          have heR : R' = R := Except.ok.inj (he.symm.trans hu)
          subst R'
          simp [hs]
      apply (blsScheme_sound laws a h _).mpr
      apply Subtype.ext
      rw [hd, hc.2, G2.toPoint_mul_generator, ← Scalar.coe_ofFr c, hc',
        G2Sub.coe_smul, ← G2Sub.ofFr_dlog h]
      rw [show ((a * G2Sub.dlog h : Scalar) : Fr) =
        (a : Fr) * (G2Sub.dlog h : Fr) from map_mul Fr.toZMod.symm _ _,
        G2.ofFr_mul, Scalar.val_coe]

/-- A byte forger's advantage is at most that of its decoded group forger.

The signing transcript is identical, so message freshness is unchanged.
-/
theorem byteForgeAdvantage_le (laws : PairingLaws) (adversary : ByteAdversary) :
    byteForgeAdvantage adversary ≤ forgeAdvantage Scalar blsScheme adversary.toGroup := by
  classical
  unfold byteForgeAdvantage forgeAdvantage byteExperiment experiment
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  apply MeasureTheory.lintegral_mono
  intro a
  simp only [run, ByteAdversary.toGroup, simulateQ_bind, simulateQ_map,
    bind_map_left, StateT.run_bind, StateT.run_map,
    bind_pure_comp, map_bind, Functor.map_map]
  apply prEvent_bind_mono_of_support
  rintro ⟨⟨m, sig⟩, st⟩ _
  apply prEvent_mono
  rintro ⟨h, st'⟩ hw
  obtain ⟨hf, hv⟩ := Bool.and_eq_true_iff.mp hw
  exact Bool.and_eq_true_iff.mpr ⟨by simpa only [decide_eq_true_eq] using hf,
    isDh_of_byteVerify laws a sig h hv⟩

/-- The byte-game bound follows from the same named co-CDH solver as the group-game bound. -/
theorem byteForgeAdvantage_le_coCdhAdvantage (laws : PairingLaws) (adversary : ByteAdversary)
    {q : ℕ} (hq0 : 0 < q) (hq : HashCallBound Scalar blsScheme adversary.toGroup q) :
    byteForgeAdvantage adversary ≤
      q * coCdhAdvantage Scalar g1 g2 (reduction (F := Scalar) g2 adversary.toGroup q) :=
  (byteForgeAdvantage_le laws adversary).trans
    (forgeAdvantage_blsScheme_le laws adversary.toGroup hq0 hq)

end EthLib.Cryptography.Bls.Security

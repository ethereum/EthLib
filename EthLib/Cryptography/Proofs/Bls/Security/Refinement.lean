module

public import EthLib.Cryptography.Proofs.Bls.Security.Reduction
public import EthLib.Cryptography.Proofs.Bls.SignaturesUnique
public import Mathlib.Algebra.Module.ZMod
import EthLib.Cryptography.Proofs.Bls.PairingAte

/-!
# Proofs: EthLib's BLS signatures are the scheme of the game

The groups of the game are the multiples of the generators of `G1` and `G2`.

EthLib's pairing check is a sound test of co-Diffie-Hellman tuples.

EthLib signs and verifies as the scheme does, with `H(m)` the hash to `G2` of `m`.

With that hash taken as a random oracle, the bound of the game applies to this scheme.

The byte game gives the adversary compressed keys, hashes and signatures.

Decoding its output gives a group forger with at least the same advantage.

The soundness of the pairing check and the refinement of verification use the proved pairing law.

The step from bytes to group elements does not use that law.
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

/-- Every multiple of `g1` is a scalar times `g1`. -/
theorem G1Sub.exists_eq_smul_g1 (x : G1Sub) : ∃ sk : Scalar, x = sk • g1 := by
  obtain ⟨k, hk⟩ := G1Sub.exists_ofFr x
  refine ⟨Scalar.ofFr k, Subtype.ext ?_⟩
  rw [G1Sub.coe_smul, Scalar.val_ofFr, ← hk]
  rfl

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

/-- A valid point of `G1` that passes the subgroup check is a multiple of `g1`. -/
theorem G1Sub.toPoint_mem_of_inSubgroup {P : G1} (hP : G1.Valid P)
    (hs : G1.inSubgroup P = true) : G1.toPoint P ∈ G1Sub := by
  obtain ⟨k, hk⟩ := G1.exists_mul_generator_of_inSubgroup hP hs
  rw [hk, G1.toPoint_mul_generator]
  exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _

/-- A valid point of `G2` that passes the subgroup check is a multiple of `g2`. -/
theorem G2Sub.toPoint_mem_of_inSubgroup {Q : G2} (hQ : G2.Valid Q)
    (hs : G2.inSubgroup Q = true) : G2.toPoint Q ∈ G2Sub := by
  obtain ⟨k, hk⟩ := G2.exists_mul_generator_of_inSubgroup hQ hs
  rw [hk, G2.toPoint_mul_generator]
  exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _

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

/-- The pairing check is a sound test of co-Diffie-Hellman tuples. -/
theorem blsScheme_sound : blsScheme.Sound Scalar := by
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
    pairingLaws.two_pairs G1.represents_generator (G2Sub.represents_rep σ)
    (G1Sub.represents_rep _).neg (G2Sub.represents_rep h), G1Sub.dlog_smul_g1, hσ]
  exact check_scalars_iff _ _ _

/-! ## EthLib's signing and verification -/

/-- The point that the hash to `G2` gives a message under the tag `dst`. -/
noncomputable def hashRepWith (dst msg : ByteArray) : G2 :=
  (HashToCurve.hashToG2_total_inSubgroup msg dst).choose

/-- The hash to `G2` never fails, and its point is valid and in the subgroup. -/
theorem hashRepWith_spec (dst msg : ByteArray) :
    HashToCurve.hashToG2 msg dst = .ok (hashRepWith dst msg) ∧ G2.Valid (hashRepWith dst msg) ∧
      G2.inSubgroup (hashRepWith dst msg) = true :=
  (HashToCurve.hashToG2_total_inSubgroup msg dst).choose_spec

/-- The hash to `G2` of a message under the tag `dst`, as a multiple of `g2`. -/
noncomputable def hashPointWith (dst msg : ByteArray) : G2Sub :=
  ⟨G2.toPoint (hashRepWith dst msg),
    G2Sub.toPoint_mem_of_inSubgroup (hashRepWith_spec dst msg).2.1
      (hashRepWith_spec dst msg).2.2⟩

/-- The point that the hash to `G2` gives a message under the message tag. -/
noncomputable def hashRep (msg : ByteArray) : G2 := hashRepWith DST msg

/-- The hash to `G2` never fails, and its point is valid and in the subgroup. -/
theorem hashRep_spec (msg : ByteArray) :
    HashToCurve.hashToG2 msg DST = .ok (hashRep msg) ∧ G2.Valid (hashRep msg) ∧
      G2.inSubgroup (hashRep msg) = true :=
  hashRepWith_spec DST msg

/-- The hash to `G2` of a message under the message tag, as a multiple of `g2`.

It is the hash `H` of the scheme. -/
noncomputable def hashPoint (msg : ByteArray) : G2Sub := hashPointWith DST msg

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

/-- EthLib accepts exactly the signatures that decode to `sk • H(msg)`. -/
theorem verify_iff (sk : SecretKey) (msg sig : ByteArray) :
    verify (pkBytes sk) msg sig = true ↔
      ∃ R, G2.uncompress sig = .ok R ∧
        G2.toPoint R = (Scalar.ofFr sk.val • hashPoint msg : G2Sub) := by
  obtain ⟨P, hP, hPrep⟩ := G1.keyValidatePoint_compress_mul sk.property
  obtain ⟨hQ, hv, hs⟩ := hashRep_spec msg
  obtain ⟨b, hb⟩ := (G2.inSubgroup_iff_exists_represents hv).mp hs
  refine (coreVerify_iff (pk := pkBytes sk) ((pkBytes_eq sk).symm ▸ hP) hPrep hQ hb).trans
    (exists_congr fun R => and_congr_right fun hR => ?_)
  have hpt : G2.toPoint (G2.mul G2.generator (sk.val * b)) =
      (Scalar.ofFr sk.val • hashPoint msg : G2Sub) := by
    rw [G2.toPoint_mul_generator, G2.ofFr_mul, ← G2.toPoint_mul_generator, ← hb.2,
      G2Sub.coe_smul, Scalar.val_ofFr]
    rfl
  rw [G2.Represents, hpt]
  exact and_iff_right (G2.valid_of_uncompress hR)

/-- EthLib's verification is the test of the scheme on the decoded point.

The key is `sk • g1`, and the hash is `H(msg)`. -/
theorem verify_iff_isDh (sk : SecretKey) (msg sig : ByteArray) :
    verify (pkBytes sk) msg sig = true ↔
      ∃ R, G2.uncompress sig = .ok R ∧ ∃ hR : G2.toPoint R ∈ G2Sub,
        blsScheme.isDh (Scalar.ofFr sk.val • g1) (hashPoint msg) ⟨_, hR⟩ = true := by
  rw [verify_iff]
  refine exists_congr fun R => and_congr_right fun _ => ⟨fun h => ?_, fun ⟨hR, hd⟩ => ?_⟩
  · exact ⟨h ▸ (Scalar.ofFr sk.val • hashPoint msg).2,
      (blsScheme_sound _ _ _).mpr (Subtype.ext h)⟩
  · exact congrArg Subtype.val ((blsScheme_sound _ _ _).mp hd)

/-- **EthLib's BLS signatures are unforgeable from co-CDH**, in the random oracle model.

The oracle `H` stands for the hash to `G2` under the message tag. -/
theorem forgeAdvantage_blsScheme_le
    (adversary : Adversary G1Sub G2Sub ByteArray) {q : ℕ} (hq0 : 0 < q)
    (hq : HashCallBound Scalar blsScheme adversary q) :
    forgeAdvantage Scalar blsScheme adversary ≤
      q * coCdhAdvantage Scalar g1 g2 (reduction (F := Scalar) g2 adversary q) :=
  forgeAdvantage_le blsScheme blsScheme_sound adversary hq0 hq

/-! ## The byte interface -/

/-- The canonical bytes of a subgroup element of `G1`.

The BLS draft-04, §1.3, §2.2 and Appendix A require compressed serialization.

The format is Zcash's "BLS12-381 serialization", including its three flag bits.

<https://docs.rs/bls12_381/0.8.0/bls12_381/notes/serialization/index.html>
-/
noncomputable def G1Sub.encode (P : G1Sub) : ByteArray := G1.compress (G1Sub.rep P)

/-- The canonical bytes of a subgroup element of `G2`, in the same Zcash format. -/
noncomputable def G2Sub.encode (Q : G2Sub) : ByteArray := G2.compress (G2Sub.rep Q)

/-- Decode a signature, rejecting malformed bytes and points outside the subgroup.

These are the signature checks of BLS draft-04, §2.7, steps 1 to 3.
-/
noncomputable def decodeSignature (sig : ByteArray) : Option G2Sub :=
  match hu : G2.uncompress sig with
  | .error _ => none
  | .ok R =>
    if hs : G2.inSubgroup R = true then
      some ⟨G2.toPoint R, G2Sub.toPoint_mem_of_inSubgroup (G2.valid_of_uncompress hu) hs⟩
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

/-- The representative of a subgroup element of `G1` has that group element. -/
theorem G1Sub.toPoint_rep (x : G1Sub) : G1.toPoint (G1Sub.rep x) = x := by
  rw [(G1Sub.represents_rep x).2, G1.toPoint_mul_generator, G1Sub.dlog, Scalar.coe_ofFr]
  exact (G1Sub.exists_ofFr x).choose_spec

/-- The encoding of a subgroup element of `G1` compresses any valid point of that element.

So the encoded key is computable from a point, without its discrete logarithm.
-/
theorem G1Sub.encode_eq_compress {P : G1} {x : G1Sub} (hP : G1.Valid P)
    (hx : G1.toPoint P = x) : G1Sub.encode x = G1.compress P :=
  G1.compress_congr (G1Sub.represents_rep x).1 hP ((G1Sub.toPoint_rep x).trans hx.symm)

/-- The encoded signing answer is the compressed point that EthLib signs with. -/
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

/-- Every byte string that decodes to a subgroup element is the encoding of that element.

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

/-- Decode a key: decompress it and require a point of the subgroup of order `r`.

Unlike key validation, it accepts the point at infinity, as the zero of the group. -/
noncomputable def decodeKey (pk : ByteArray) : Option G1Sub :=
  match hu : G1.uncompress pk with
  | .error _ => none
  | .ok P =>
    if hs : G1.inSubgroup P = true then
      some ⟨G1.toPoint P, G1Sub.toPoint_mem_of_inSubgroup (G1.uncompress_valid hu) hs⟩
    else none

/-- Successful decompression and a subgroup check give the decoded group element. -/
private theorem decodeKey_of_uncompress {pk : ByteArray} {P : G1}
    (hu : G1.uncompress pk = .ok P) (hs : G1.inSubgroup P = true)
    (x : G1Sub) (hp : G1.toPoint P = x) : decodeKey pk = some x := by
  unfold decodeKey
  split
  · rename_i he'
    rw [hu] at he'
    cases he'
  · rename_i R' he'
    have hRR : R' = P := Except.ok.inj (he'.symm.trans hu)
    subst R'
    simp only [hs, dite_true, Option.some.injEq, Subtype.ext_iff]
    exact hp

/-- Decoding the encoding of a multiple of `g1` returns it, including zero. -/
theorem decodeKey_encode (x : G1Sub) : decodeKey (G1Sub.encode x) = some x := by
  obtain ⟨R, hu, he⟩ := G1.uncompress_compress (G1Sub.represents_rep x).1
  have hR : G1.Valid R := G1.uncompress_valid hu
  have hs : G1.inSubgroup R = true :=
    (G1.inSubgroup_iff_exists_represents hR).mpr
      ⟨G1Sub.dlog x, hR, he.trans (G1Sub.represents_rep x).2⟩
  exact decodeKey_of_uncompress hu hs x (he.trans (G1Sub.toPoint_rep x))

/-- Bytes that decode are the encoding of the decoded element.

So distinct bytes that both decode give distinct elements. -/
theorem encode_eq_of_decodeKey {pk : ByteArray} {x : G1Sub} (hd : decodeKey pk = some x) :
    G1Sub.encode x = pk := by
  unfold decodeKey at hd
  split at hd
  · cases hd
  · rename_i R hu
    split at hd
    · have hp : G1.toPoint R = x := congrArg Subtype.val (Option.some.inj hd)
      change G1.compress (G1Sub.rep x) = pk
      apply Eq.trans _ (G1.compress_uncompress hu)
      apply G1.compress_congr (G1Sub.represents_rep x).1 (G1.uncompress_valid hu)
      exact (G1Sub.toPoint_rep x).trans hp.symm
    · cases hd

/-- A decoded point in the subgroup is a group element that its bytes decode to. -/
theorem exists_decodeKey_of_uncompress {pk : ByteArray} {P : G1} (hu : G1.uncompress pk = .ok P)
    (hs : G1.inSubgroup P = true) : ∃ x, decodeKey pk = some x ∧ G1.toPoint P = x :=
  ⟨⟨G1.toPoint P, G1Sub.toPoint_mem_of_inSubgroup (G1.uncompress_valid hu) hs⟩,
    decodeKey_of_uncompress hu hs _ rfl, rfl⟩

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

/-- Verification on bytes with the random oracle's hash in place of the hash to G2.

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

/-- The pairing check of verification reads only the group elements of its valid points. -/
theorem two_pairs_congr {P P' : G1} {R R' Q Q' : G2}
    (hP : G1.Valid P) (hP' : G1.Valid P') (hPe : G1.toPoint (G1.neg P) = G1.toPoint (G1.neg P'))
    (hR : G2.Valid R) (hR' : G2.Valid R') (hRe : G2.toPoint R = G2.toPoint R')
    (hQ : G2.Valid Q) (hQ' : G2.Valid Q') (hQe : G2.toPoint Q = G2.toPoint Q') :
    pairingCheck #[(G1.generator, R), (G1.neg P, Q)] =
      pairingCheck #[(G1.generator, R'), (G1.neg P', Q')] := by
  apply pairingCheck_congr
    (ps := #[(G1.generator, R), (G1.neg P, Q)])
    (qs := #[(G1.generator, R'), (G1.neg P', Q')]) rfl
  intro i hi
  change i < 2 at hi
  cases i with
  | zero => exact ⟨G1.valid_generator, G1.valid_generator, rfl, hR, hR', hRe⟩
  | succ i =>
    have hi0 : i = 0 := by omega
    subst i
    exact ⟨G1.valid_neg hP, G1.valid_neg hP', hPe, hQ, hQ', hQe⟩

/-- The check of one signature, with the hash under `dst` in place of the oracle, is EthLib's.

No pairing law is needed: the pairing check depends only on valid group elements.
-/
theorem byteVerify_hashPointWith (dst pk msg sig : ByteArray) :
    byteVerify pk sig (hashPointWith dst msg) = coreVerify pk msg sig dst := by
  obtain ⟨hQ, hv, -⟩ := hashRepWith_spec dst msg
  unfold byteVerify coreVerify
  rw [hQ]
  cases hu : G2.uncompress sig with
  | error e => rfl
  | ok R =>
    cases hp : G1.keyValidatePoint pk with
    | error e => rfl
    | ok P =>
      apply congrArg (fun b => signatureSubgroupCheck R && b)
      have hPv := (G1.keyValidatePoint_eq_ok_iff.mp hp).2.1
      have hRv := G2.valid_of_uncompress hu
      exact two_pairs_congr hPv hPv rfl hRv hRv rfl
        (G2Sub.represents_rep (hashPointWith dst msg)).1 hv
        (G2Sub.toPoint_rep (hashPointWith dst msg))

/-- Replacing the random oracle with EthLib's hash gives EthLib's byte verification. -/
theorem byteVerify_hashPoint (pk msg sig : ByteArray) :
    byteVerify pk sig (hashPoint msg) = verify pk msg sig :=
  byteVerify_hashPointWith DST pk msg sig

/-- The byte game for the secret scalar `a`.

Key validation rejects the zero key, so the run with `a = 0` loses.

Freshness means a message never submitted to signing, as in BLS01, §3, Definition 3.1.

A signed message loses even with different signature bytes, not just with a repeated pair.
-/
noncomputable def byteExperimentAt (adversary : ByteAdversary) (a : Scalar) :
    ProbComp (Bool × State Scalar ByteArray) := by
  classical
  exact do
    let pk := a • g1
    let ((m, sig, h), st) ← (simulateQ (impl g2 a) (do
      let (m, sig) ← byteMain adversary pk
      let h ← query (spec := Spec ByteArray G2Sub) (.inr (.inl m))
      return (m, sig, h))).run State.init
    return (decide (m ∉ st.signed) && byteVerify (G1Sub.encode pk) sig h, st)

/-- The byte game keeps the group game's scalar distribution, including zero. -/
noncomputable def byteExperiment (adversary : ByteAdversary) :
    ProbComp (Bool × State Scalar ByteArray) := do
  let a ← $ᵗ Scalar
  byteExperimentAt adversary a

/-- The probability of an accepted byte forgery on a fresh message. -/
noncomputable def byteForgeAdvantage (adversary : ByteAdversary) : ℝ≥0∞ :=
  Pr{let z ← byteExperiment adversary}[z.1 = true]

/-- A passing pairing check on decoded points is the scheme's test on their group elements. -/
private theorem isDh_of_check {sig : ByteArray} {R : G2} {P : G1} {x : G1Sub} {h : G2Sub}
    (hu : G2.uncompress sig = .ok R) (hs : G2.inSubgroup R = true) (hPv : G1.Valid P)
    (hx : G1.toPoint P = x)
    (hv : pairingCheck #[(G1.generator, R), (G1.neg P, G2Sub.rep h)] = true) :
    blsScheme.isDh x h ((decodeSignature sig).getD 0) = true := by
  have hRv := G2.valid_of_uncompress hu
  have hd : ((decodeSignature sig).getD 0).val = G2.toPoint R := by
    rw [decodeSignature_of_uncompress hu hs
      ⟨G2.toPoint R, G2Sub.toPoint_mem_of_inSubgroup hRv hs⟩ rfl]
    simp only [Option.getD_some]
  -- The group test pairs the same group elements as the byte check.
  refine Eq.trans ?_ hv
  exact two_pairs_congr (G1Sub.represents_rep x).1 hPv
    (by rw [G1.toPoint_neg (G1Sub.represents_rep x).1, G1.toPoint_neg hPv, G1Sub.toPoint_rep, hx])
    (G2Sub.represents_rep _).1 hRv ((G2Sub.toPoint_rep _).trans hd)
    (G2Sub.represents_rep h).1 (G2Sub.represents_rep h).1 rfl

/-- Every key that the signature check accepts decodes, and the check is the scheme's test.

No pairing law is needed: both checks pair the same group elements.
-/
theorem exists_decodeKey_isDh_of_byteVerify {pk sig : ByteArray} {h : G2Sub}
    (hv : byteVerify pk sig h = true) :
    ∃ x, decodeKey pk = some x ∧ blsScheme.isDh x h ((decodeSignature sig).getD 0) = true := by
  cases hu : G2.uncompress sig with
  | error e => simp [byteVerify, hu] at hv
  | ok R =>
    have hs : G2.inSubgroup R = true :=
      (Bool.and_eq_true_iff.mp
        (by simpa only [byteVerify, hu, signatureSubgroupCheck] using hv)).1
    cases hp : G1.keyValidatePoint pk with
    | error e => simp [byteVerify, hu, hp] at hv
    | ok P =>
      obtain ⟨hpu, hPv, -, hord⟩ := G1.keyValidatePoint_eq_ok_iff.mp hp
      have hsP : G1.inSubgroup P = true :=
        (G1.inSubgroup_iff_modulus_smul_eq_zero hPv).mpr hord
      obtain ⟨x, hdk, hx⟩ := exists_decodeKey_of_uncompress hpu hsP
      have hv' : pairingCheck #[(G1.generator, R), (G1.neg P, G2Sub.rep h)] = true := by
        simpa [byteVerify, hu, hp, signatureSubgroupCheck, hs] using hv
      exact ⟨x, hdk, isDh_of_check hu hs hPv hx hv'⟩

/-- Every accepted byte signature gives a winning group signature for the same key and hash. -/
theorem isDh_of_byteVerify (a : Scalar) (sig : ByteArray) (h : G2Sub)
    (hv : byteVerify (G1Sub.encode (a • g1)) sig h = true) :
    blsScheme.isDh (a • g1) h (decodeSignature sig |>.getD 0) = true := by
  obtain ⟨x, hx, hd⟩ := exists_decodeKey_isDh_of_byteVerify hv
  rw [decodeKey_encode, Option.some.injEq] at hx
  rw [hx]
  exact hd

/-- A byte forger's advantage is at most that of its decoded group forger.

The signing transcript is identical, so message freshness is unchanged.
-/
theorem byteForgeAdvantage_le (adversary : ByteAdversary) :
    byteForgeAdvantage adversary ≤ forgeAdvantage Scalar blsScheme adversary.toGroup := by
  classical
  unfold byteForgeAdvantage forgeAdvantage byteExperiment byteExperimentAt experiment
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
    isDh_of_byteVerify a sig h hv⟩

/-- Every run of the byte game makes at most `q` hash calls.

That counts the forger's calls, those of signing, and the one of the final verification.
-/
def ByteHashCallBound (adversary : ByteAdversary) (q : ℕ) : Prop :=
  ∀ z ∈ support (byteExperiment adversary), z.2.calls ≤ q

/-- The byte game and the game of the decoded forger end in the same states.

The encoding forwards each oracle query once, so both games make the same calls.
-/
theorem snd_map_byteExperiment (adversary : ByteAdversary) :
    Prod.snd <$> byteExperiment adversary =
      Prod.snd <$> experiment (F := Scalar) blsScheme adversary.toGroup := by
  unfold byteExperiment byteExperimentAt experiment
  simp only [run, ByteAdversary.toGroup, simulateQ_bind, simulateQ_map,
    bind_map_left, StateT.run_bind, StateT.run_map,
    bind_pure_comp, map_bind, Functor.map_map]
  rfl

/-- Two runs that end in the same states satisfy the same properties of their final states. -/
theorem forall_mem_support_snd_iff {α β γ : Type} {A : ProbComp (α × γ)} {B : ProbComp (β × γ)}
    (h : Prod.snd <$> A = Prod.snd <$> B) (P : γ → Prop) :
    (∀ z ∈ support A, P z.2) ↔ ∀ z ∈ support B, P z.2 := by
  have h' := congrArg support h
  simp only [support_map] at h'
  constructor
  · intro hb z hz
    obtain ⟨y, hy, hyz⟩ := (Set.ext_iff.mp h' z.2).mpr ⟨z, hz, rfl⟩
    exact hyz ▸ hb y hy
  · intro hb z hz
    obtain ⟨y, hy, hyz⟩ := (Set.ext_iff.mp h' z.2).mp ⟨z, hz, rfl⟩
    exact hyz ▸ hb y hy

/-- A byte forger has a hash-call bound exactly when its decoded forger has the same bound. -/
theorem byteHashCallBound_iff (adversary : ByteAdversary) (q : ℕ) :
    ByteHashCallBound adversary q ↔ HashCallBound Scalar blsScheme adversary.toGroup q :=
  forall_mem_support_snd_iff (snd_map_byteExperiment adversary) fun s => s.calls ≤ q

/-- The byte-game bound follows from the same named co-CDH solver as the group-game bound. -/
theorem byteForgeAdvantage_le_coCdhAdvantage (adversary : ByteAdversary)
    {q : ℕ} (hq0 : 0 < q) (hq : HashCallBound Scalar blsScheme adversary.toGroup q) :
    byteForgeAdvantage adversary ≤
      q * coCdhAdvantage Scalar g1 g2 (reduction (F := Scalar) g2 adversary.toGroup q) :=
  (byteForgeAdvantage_le adversary).trans
    (forgeAdvantage_blsScheme_le adversary.toGroup hq0 hq)

/-- **EthLib's BLS signatures on bytes are unforgeable from co-CDH**, in the random oracle model.

The hash-call bound is on the byte forger itself.
-/
theorem byteForgeAdvantage_le_coCdhAdvantage_of_byteHashCallBound
    (adversary : ByteAdversary) {q : ℕ} (hq0 : 0 < q) (hq : ByteHashCallBound adversary q) :
    byteForgeAdvantage adversary ≤
      q * coCdhAdvantage Scalar g1 g2 (reduction (F := Scalar) g2 adversary.toGroup q) :=
  byteForgeAdvantage_le_coCdhAdvantage adversary hq0
    ((byteHashCallBound_iff adversary q).mp hq)

/-! ## Keys with a nonzero scalar -/

/-- The nonzero scalars, the secret keys of EthLib. -/
abbrev NonzeroScalar := { a : Scalar // a ≠ 0 }

instance : Nonempty NonzeroScalar := ⟨⟨1, one_ne_zero⟩⟩

noncomputable instance : SampleableType NonzeroScalar := SampleableType.ofFintype _

/-- The byte game with a uniform nonzero secret scalar. -/
noncomputable def nonzeroByteExperiment (adversary : ByteAdversary) :
    ProbComp (Bool × State Scalar ByteArray) := do
  let a ← $ᵗ NonzeroScalar
  byteExperimentAt adversary a

/-- The probability of an accepted byte forgery on a fresh message under a nonzero key. -/
noncomputable def nonzeroByteForgeAdvantage (adversary : ByteAdversary) : ℝ≥0∞ :=
  Pr{let z ← nonzeroByteExperiment adversary}[z.1 = true]

/-- Every run of the byte game with the zero scalar loses. -/
theorem byteExperimentAt_zero (adversary : ByteAdversary) :
    ∀ z ∈ support (byteExperimentAt adversary 0), z.1 = false := by
  classical
  have hver : ∀ sig h, byteVerify (G1Sub.encode ((0 : Scalar) • g1)) sig h = false := by
    intro sig h
    by_contra hne
    have hv := Bool.eq_true_of_not_eq_false hne
    cases hu : G2.uncompress sig with
    | error e => simp only [byteVerify, hu] at hv; cases hv
    | ok R =>
      cases hp : G1.keyValidatePoint (G1Sub.encode ((0 : Scalar) • g1)) with
      | error e => simp only [byteVerify, hu, hp, Bool.and_false] at hv; cases hv
      | ok P =>
        obtain ⟨hPu, hPv, hne0, -⟩ := G1.keyValidatePoint_eq_ok_iff.mp hp
        have hrep := G1Sub.represents_rep ((0 : Scalar) • g1)
        obtain ⟨P', hp', he⟩ := G1.uncompress_compress hrep.1
        have hPP : P = P' := Except.ok.inj (hPu.symm.trans hp')
        apply hne0
        rw [hPP, he, hrep.2, G1Sub.dlog_smul_g1]
        simp [G1.toPoint_mul G1.valid_generator]
  intro z hz
  unfold byteExperimentAt at hz
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨x, -, rfl⟩ := hz
  simp only [hver, Bool.and_false]

/-- The nonzero residues modulo `n` number `n - 1`. -/
private theorem card_nonzero_zmod (n : ℕ) [NeZero n] :
    Fintype.card { a : ZMod n // a ≠ 0 } = n - 1 := by
  classical
  have h := Fintype.card_subtype_compl (fun a : ZMod n => a = 0)
  rw [Fintype.card_subtype_eq, ZMod.card] at h
  convert h

/-- Under a nonzero key, a byte forger wins `r / (r - 1)` times as often as in the byte game.

The byte game draws zero with probability `1 / r`, and that run always loses.
-/
theorem nonzeroByteForgeAdvantage_eq (adversary : ByteAdversary) :
    nonzeroByteForgeAdvantage adversary =
      (Fr.modulus : ℝ≥0∞) / ((Fr.modulus - 1 : ℕ) : ℝ≥0∞) * byteForgeAdvantage adversary := by
  classical
  have hsum : ∀ (T : Type) [SampleableType T] [Fintype T]
      (f : T → ProbComp (Bool × State Scalar ByteArray)),
      Pr{let z ← ($ᵗ T >>= f)}[z.1 = true] =
        (Fintype.card T : ℝ≥0∞)⁻¹ * ∑ t, Pr{let z ← f t}[z.1 = true] := by
    intro T _ _ f
    rw [prEvent_bind_eq_sum_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [SampleableType.prEvent_uniformSample_eq_singleton]
  have h0 : Pr{let z ← byteExperimentAt adversary 0}[z.1 = true] = 0 :=
    (prEvent_eq_zero_iff _ _).mpr fun z hz => by simp [byteExperimentAt_zero adversary z hz]
  have hcard : (Fintype.card NonzeroScalar : ℝ≥0∞) = ((Fr.modulus - 1 : ℕ) : ℝ≥0∞) := by
    rw [card_nonzero_zmod]
  have hr : (Fr.modulus : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fr.modulus_prime.ne_zero
  have key : ∀ x y S : ℝ≥0∞, x ≠ 0 → x ≠ ⊤ → y⁻¹ * S = x / y * (x⁻¹ * S) := by
    intro x y S hx hx'
    rw [ENNReal.div_eq_inv_mul, ← mul_assoc, mul_assoc y⁻¹, ENNReal.mul_inv_cancel hx hx',
      mul_one]
  unfold nonzeroByteForgeAdvantage byteForgeAdvantage nonzeroByteExperiment byteExperiment
  rewrite [hsum NonzeroScalar, hsum Scalar, Fintype.sum_eq_add_sum_subtype_ne _ (0 : Scalar), h0,
    zero_add, hcard, ZMod.card]
  exact key _ _ _ hr (ENNReal.natCast_ne_top _)

/-- **EthLib's BLS signatures on bytes are unforgeable from co-CDH under nonzero keys.**

This holds in the random oracle model.

The bound is that of the byte game, times `r / (r - 1)`.

The hash-call bound is on the byte game.
-/
theorem nonzeroByteForgeAdvantage_le_coCdhAdvantage
    (adversary : ByteAdversary) {q : ℕ} (hq0 : 0 < q) (hq : ByteHashCallBound adversary q) :
    nonzeroByteForgeAdvantage adversary ≤
      (Fr.modulus : ℝ≥0∞) / ((Fr.modulus - 1 : ℕ) : ℝ≥0∞) *
        (q * coCdhAdvantage Scalar g1 g2 (reduction (F := Scalar) g2 adversary.toGroup q)) := by
  rw [nonzeroByteForgeAdvantage_eq]
  exact mul_le_mul_right
    (byteForgeAdvantage_le_coCdhAdvantage_of_byteHashCallBound adversary hq0 hq) _

end EthLib.Cryptography.Bls.Security

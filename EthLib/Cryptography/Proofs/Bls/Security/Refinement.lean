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

The game's adversary handles group elements, not the bytes that EthLib encodes them in.

Every signature that EthLib accepts decodes to such an element.

No theorem here turns a forger on bytes into a forger on group elements.
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

end EthLib.Cryptography.Bls.Security

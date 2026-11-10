module

public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect
public import EthLib.Cryptography.Proofs.Bls.PairingCongr
import EthLib.Cryptography.Proofs.Bls.PairingAte

/-!
# Proofs: unique signatures, and the rogue-key attack

A key and a message have at most one signature that verifies, byte for byte.

The fast aggregate verification alone does not bind each key to its owner.

Whoever knows a scalar `c` builds a key from a victim's key, and signs for both keys.

So every key of a fast aggregate verification needs a verified proof of possession.

The sources are [draft-04][draft-04], §3.3, and [ePrint 2018/483][2018-483], §1.

[draft-04]: https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04
[2018-483]: https://eprint.iacr.org/2018/483
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open scoped EthLib.Cryptography.Bls.Fr

namespace Signatures

/-- The scalar equation of a verification fixes the signature scalar. -/
private theorem eq_of_verify_scalars (c a b : Fr) (h : 1 * c + -a * b = 0) :
    c = a * b := by
  linear_combination h

/-- The scalars of an honest signature satisfy the verification equation. -/
private theorem verify_scalars (a b : Fr) : 1 * (a * b) + -a * b = 0 := by
  ring

/-- The core verification accepts exactly the signatures that decode to `(a * b) • g2`.

Here the key validates to a representative of `a • g1`, and the message hashes to `b • g2`. -/
theorem coreVerify_iff {pk msg sig dst : ByteArray} {P : G1} {Q : G2}
    {a b : Fr} (hP : G1.keyValidatePoint pk = .ok P) (hPa : G1.Represents P a)
    (hQ : HashToCurve.hashToG2 msg dst = .ok Q) (hb : G2.Represents Q b) :
    coreVerify pk msg sig dst = true ↔
      ∃ R, G2.uncompress sig = .ok R ∧ G2.Represents R (a * b) := by
  unfold coreVerify
  cases hu : G2.uncompress sig with
  | error e => exact iff_of_false (fun h => by cases h) (fun ⟨R, hR, _⟩ => by cases hR)
  | ok R =>
    have hRv := G2.valid_of_uncompress hu
    -- Rewrite every discriminant first, or the kernel evaluates the hash on a variable message.
    rw [hP, hQ]
    dsimp only
    constructor
    · intro h
      rw [Bool.and_eq_true] at h
      obtain ⟨c, hc⟩ := (signatureSubgroupCheck_iff hRv).mp h.1
      have hs := (pairingLaws.two_pairs G1.represents_generator hc hPa.neg hb).mp h.2
      exact ⟨R, rfl, eq_of_verify_scalars c a b hs ▸ hc⟩
    · rintro ⟨R', hR', hrep⟩
      obtain rfl : R = R' := Except.ok.inj hR'
      rw [show signatureSubgroupCheck R = true from (signatureSubgroupCheck_iff hRv).mpr ⟨_, hrep⟩,
        Bool.true_and]
      exact (pairingLaws.two_pairs G1.represents_generator hrep hPa.neg hb).mpr (verify_scalars a b)

/-- A key that passes the core verification passes key validation. -/
private theorem keyValidatePoint_of_coreVerify {pk msg sig dst : ByteArray}
    (h : coreVerify pk msg sig dst = true) : ∃ P, G1.keyValidatePoint pk = .ok P := by
  cases hk : G1.keyValidatePoint pk with
  | ok P => exact ⟨P, rfl⟩
  | error e =>
    exfalso
    unfold coreVerify at h
    rw [hk] at h
    split at h
    · cases h
    · simp at h

/-- A key and a message have at most one signature that verifies, byte for byte. -/
theorem coreVerify_unique {pk msg sig sig' dst : ByteArray}
    (h : coreVerify pk msg sig dst = true) (h' : coreVerify pk msg sig' dst = true) :
    sig = sig' := by
  obtain ⟨P, hP⟩ := keyValidatePoint_of_coreVerify h
  obtain ⟨-, hPv, -, hPr⟩ := G1.keyValidatePoint_eq_ok_iff.mp hP
  obtain ⟨a, ha⟩ := (G1.inSubgroup_iff_exists_represents hPv).mp
    ((G1.inSubgroup_iff_modulus_smul_eq_zero hPv).mpr hPr)
  obtain ⟨Q, hQ, hQv, hQs⟩ := HashToCurve.hashToG2_total_inSubgroup msg dst
  obtain ⟨b, hb⟩ := (G2.inSubgroup_iff_exists_represents hQv).mp hQs
  obtain ⟨R, hR, hRrep⟩ := (coreVerify_iff hP ha hQ hb).mp h
  obtain ⟨R', hR', hR'rep⟩ := (coreVerify_iff hP ha hQ hb).mp h'
  rw [← G2.compress_uncompress hR, ← G2.compress_uncompress hR']
  exact G2.compress_congr hRrep.1 hR'rep.1 (hRrep.2.trans hR'rep.2.symm)

/-- A key and a message have at most one signature that verifies, byte for byte. -/
theorem verify_unique {pk msg sig sig' : ByteArray}
    (h : verify pk msg sig = true) (h' : verify pk msg sig' = true) : sig = sig' :=
  coreVerify_unique h h'

/-- The rogue key cancels the victim's key in the key sum. -/
private theorem rogue_sum (a c : Fr) : [a, c + -a].sum = c := by
  simp only [List.sum_cons, List.sum_nil]
  ring

/-- The rogue scalar is nonzero when `c` differs from the victim's key. -/
private theorem rogue_ne_zero {a c : Fr} (h : c ≠ a) : c + -a ≠ 0 :=
  fun h0 => h (by linear_combination h0)

/-- The rogue-key attack on the fast aggregate verification.

The attacker picks `c` and publishes the key `c • g1 - PK`, from the victim's key `PK` alone.

The signature `c • H(msg)` then passes for the victim's key together with the rogue key.

The attacker never learns the victim's secret key. -/
theorem fastAggregateVerify_rogue (sk : SecretKey) {c : Fr} (hc0 : c ≠ 0)
    (hc : c ≠ sk.val) (msg : ByteArray) :
    ∃ P Q, G1.keyValidatePoint (pkBytes sk) = .ok P ∧ HashToCurve.hashToG2 msg DST = .ok Q ∧
      fastAggregateVerify
        #[pkBytes sk, G1.compress (G1.add (G1.mul G1.generator c) (G1.neg P))] msg
        (G2.compress (G2.mul Q c)) = true := by
  obtain ⟨P, hP, hPrep⟩ := G1.keyValidatePoint_compress_mul sk.property
  obtain ⟨Q, hQ, hQv, hQs⟩ := HashToCurve.hashToG2_total_inSubgroup msg DST
  obtain ⟨b, hb⟩ := (G2.inSubgroup_iff_exists_represents hQv).mp hQs
  refine ⟨P, Q, (pkBytes_eq sk).symm ▸ hP, hQ, ?_⟩
  -- The rogue key is the public key of the scalar `c - sk`, which the attacker does not know.
  let rogue : SecretKey := ⟨c + -sk.val, rogue_ne_zero hc⟩
  have hrep : G1.Represents (G1.add (G1.mul G1.generator c) (G1.neg P)) rogue.val :=
    (G1.represents_mul_generator c).add hPrep.neg
  have hrogue : G1.compress (G1.add (G1.mul G1.generator c) (G1.neg P)) = pkBytes rogue :=
    (G1.compress_congr hrep.1 (G1.represents_mul_generator rogue.val).1 hrep.2).trans
      (pkBytes_eq rogue).symm
  have hkeys : #[pkBytes sk, pkBytes rogue] = ([sk, rogue].map pkBytes).toArray := rfl
  have hsum : ([sk, rogue].map (·.val)).sum = c := rogue_sum sk.val c
  rw [hrogue, hkeys]
  have h1 : ([sk, rogue].map (·.val)).sum ≠ 0 := by rw [hsum]; exact hc0
  have h2 : G2.Represents (G2.mul Q c) (([sk, rogue].map (·.val)).sum * b) := by
    rw [hsum]
    exact hb.mul c
  exact fastAggregateVerify_of_represents (List.cons_ne_nil _ _) h1 hQ hb h2

end Signatures

end EthLib.Cryptography.Bls

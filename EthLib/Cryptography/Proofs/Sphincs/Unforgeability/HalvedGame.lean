module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.SeedHops
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Halves

/-!
# Proofs: the game of leanSPHINCS, asked half by half

Every hash of leanSPHINCS that feeds another hash keeps only half of its 32-byte answer.

A tweakable hash keeps its first 16 bytes, and a derivation gives two secrets, one per half.

So the game is restated with an oracle whose answers are 16-byte halves.

A 32-byte answer at a point is the two halves at that point, with half 0 first.

The game where every query asks both of its halves has the same chance of a forgery.

The bound of the two seed hops then holds for the game of halves.

In that game, a value that feeds a hash is one answer of the oracle, not a part of one.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open EthLib.Cryptography.Xmss.Unforgeability (ofOutput)
open OracleSpec OracleComp

/-! ## A 32-byte answer is two halves -/

/-- Two 32-byte values with the same halves are equal. -/
theorem eq_of_halfOf_eq {v w : Vector UInt8 32} (h0 : halfOf 0 v = halfOf 0 w)
    (h1 : halfOf 1 v = halfOf 1 w) : v = w := by
  rw [← halfOf_append v, ← halfOf_append w, h0, h1]

/-- There are `2^128` digests. -/
theorem natCard_digest : Nat.card Digest = 2 ^ 128 := by
  change Nat.card (Vector UInt8 16) = 2 ^ 128
  rw [Nat.card_congr (arrayVectorEquivFin UInt8 16), Nat.card_fun, Nat.card_eq_fintype_card,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, Nat.card_eq_fintype_card,
    Fintype.card_fin, ← pow_mul]

/-- The halves of an answer of the oracle. -/
def halvesOf (x : XmssSecurity.HashOutput) : Digest × Digest :=
  (halfOf 0 (ofOutput x), halfOf 1 (ofOutput x))

/-- An answer of the oracle is fixed by its halves. -/
theorem halvesOf_injective : Function.Injective halvesOf := fun x y h =>
  Xmss.Unforgeability.ofBV_inj (by decide)
    (eq_of_halfOf_eq (Prod.ext_iff.1 h).1 (Prod.ext_iff.1 h).2)

/-- Every pair of halves is the halves of one answer: both sides have `2^256` elements. -/
theorem halvesOf_bijective : Function.Bijective halvesOf := by
  refine halvesOf_injective.bijective_of_nat_card_le ?_
  rw [Nat.card_prod, natCard_digest, natCard_hashOutput, ← pow_add]

/-- An answer of the oracle as its two halves. -/
noncomputable def hashHalves : XmssSecurity.HashOutput ≃ Digest × Digest :=
  Equiv.ofBijective halvesOf halvesOf_bijective

/-- The first half of the answer joined from two halves is the first. -/
@[simp] theorem halfOf_zero_hashHalves_symm (u v : Digest) :
    halfOf 0 (ofOutput (hashHalves.symm (u, v))) = u :=
  congrArg Prod.fst (hashHalves.apply_symm_apply (u, v))

/-- The second half of the answer joined from two halves is the second. -/
@[simp] theorem halfOf_one_hashHalves_symm (u v : Digest) :
    halfOf 1 (ofOutput (hashHalves.symm (u, v))) = v :=
  congrArg Prod.snd (hashHalves.apply_symm_apply (u, v))

/-! ## The game of halves -/

/-- A uniform digest. -/
noncomputable instance : SampleableType Digest :=
  SampleableType.ofFintype Digest

/-- The world of halves: public points and derivations, each with two 16-byte halves. -/
abbrev HalvedWorld :=
  HalfWorld (List UInt8) DerivationInput Digest

/-- Ask every query of the world with derivations half by half. -/
noncomputable abbrev halves :
    QueryImpl (World DerivationInput) (OracleComp HalvedWorld) :=
  halvesImpl hashHalves

/-- leanSPHINCS with every derivation a derivation query, asked half by half. -/
noncomputable def halvedScheme :
    SignatureAlg (OracleComp HalvedWorld) Message PublicKey Unit (Option Signature) :=
  hiddenSeedScheme.map (simulateQ' halves)

/-- The adversary in the world of halves: each of its queries asks both halves. -/
noncomputable def halvedAdversary (adversary : Adversary) :
    SignatureAlg.UnforgeableAdversary halvedScheme :=
  (liftAdversary DerivationInput (A := hiddenSeedScheme) adversary).mapOracles halves

/-- `H` in the world of halves: both halves of the input's point, joined. -/
theorem simulateQ_halves_liftH (x : ByteArray) :
    simulateQ halves (liftH DerivationInput x) = (do
      let u ← HalvedWorld.query (.inl (.inr (x.data.toList, 0)))
      let v ← HalvedWorld.query (.inl (.inr (x.data.toList, 1)))
      return ofOutput (hashHalves.symm (u, v))) := by
  rw [liftH_eq, simulateQ_map, simulateQ_spec_query]
  simp [halvesImpl]

/-- **The game of halves.**

The forging advantage is at most the chance of a forgery in the ideal game of halves.

To it are added `qH / 2^256` for each of the two seeds.

In that game, every public point and every derivation has two independent uniform halves. -/
theorem forgeAdvantage_le_halved (adversary : Adversary) {qH qS : Nat}
    (hadversary : adversary.RomQueryBound qH qS) :
    forgeAdvantage adversary ≤
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl (List UInt8 × Fin 2 →ₒ Digest)
          (DerivationInput × Fin 2) Digest) (SignatureAlg.unforgeableTranscriptExperiment
            (halvedAdversary adversary))).run (∅, ∅)}[z.1.strongWins = true] +
        qH * ((2 : ENNReal) ^ 256)⁻¹ + qH * ((2 : ENNReal) ^ 256)⁻¹ := by
  have h := prEvent_idealImpl_halvesImpl hashHalves (SignatureAlg.unforgeableTranscriptExperiment
    (liftAdversary DerivationInput (A := hiddenSeedScheme) adversary)) fun z => z.strongWins = true
  rw [SignatureAlg.simulateQ_unforgeableTranscriptExperiment] at h
  exact (forgeAdvantage_le_hiddenSeed adversary hadversary).trans_eq
    (congrArg (fun p => p + _ + _) h.symm)

end EthLib.Cryptography.Sphincs.Unforgeability

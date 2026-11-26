module

public import EthLib.Base.Proofs.Bytes.Equiv
public import EthLib.Cryptography.Proofs.HashSig.Lanes
public import EthLib.Cryptography.Proofs.Hash.Keccak.Sponge
public import EthLib.Cryptography.Proofs.Hash.Keccak.QueryBound
public import EthLib.Cryptography.Proofs.OneCallPermutation
public import EthLib.Cryptography.Proofs.SufCma.Indifferentiability

/-!
# Proofs: the hash-based signatures in the random-permutation model of Keccak-f[1600]

Keccak-256 is KECCAK[512] of FIPS 202 §5.2, a sponge over the permutation Keccak-f[1600] of §3.4.

The security proofs of the hash-based signatures model it as a random oracle on byte strings.

Keccak-256 over a uniform permutation is indifferentiable from that oracle.

This is Theorem 2 of [Bertoni, Daemen, Peeters, Van Assche, Eurocrypt 2008][sponge], §4.3.

The adversary may then call the permutation and its inverse, and the bound loses one unit `2^-bits`.

At a cost of at most `2^129` permutation calls, the sponge's term is at most `2^-128`.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open OracleComp OracleSpec ENNReal PFunctor.FreeM EthLib.Base
open EthLib.Cryptography.Hash.Keccak EthLib.Cryptography.LazyPermutation
  EthLib.Cryptography.Indifferentiability EthLib.Cryptography.Sponge EthLib.Cryptography.SufCma

/-! ## Keccak-256 on byte strings, as the oracle answers -/

/-- The 32 bytes of Keccak-256 are the bytes of an oracle answer. -/
theorem digestEquiv_eq_ofOutput (x : HashOutput) : digestEquiv x = ofOutput x := by
  rw [← bytes_ofOutputLanes]
  rfl

/-- Keccak-256 over `π` on a byte string, with its 32-byte digest read as an oracle answer. -/
def keccakOutput (π : State → State) (input : HashInput) : HashOutput :=
  digestEquiv.symm (Id.run (keccak256With (fun S => pure (π S)) (listEquivByteArray input)))

/-- The cost of a hash call on `input`: one permutation call per block of the padded input. -/
def blockCost (input : HashInput) : ℕ :=
  keccak256Cost (listEquivByteArray input)

/-- **Keccak-256 on byte strings is indifferentiable from a random oracle.** -/
theorem keccakOutput_indifferentiable :
    Indifferentiable keccakOutput blockCost (spongeIndiffBound (2 ^ 1600) (2 ^ 512)) :=
  keccak256_indifferentiable.relabel listEquivByteArray digestEquiv.symm

/-! ## The scheme over the permutation -/

/-- Each hash query as Keccak-256 over the forward query of the permutation.

Coins pass through. -/
def keccakImpl : QueryImpl (unifSpec + HashSpec) (OracleComp (unifSpec + PermSpec State))
  | .inl n => liftM ((unifSpec + PermSpec State).query (.inl n))
  | .inr input => digestEquiv.symm <$> keccak256With forward (listEquivByteArray input)

/-- Over a fixed permutation, a hash query run as Keccak-256 returns Keccak-256 at once. -/
theorem simulateQ_permImpl_keccakImpl (π : Equiv.Perm State) (input : HashInput) :
    simulateQ (permImpl π) (keccakImpl (.inr input)) = pure (keccakOutput π input) := by
  change simulateQ (permImpl π)
    (digestEquiv.symm <$> keccak256With forward (listEquivByteArray input)) = _
  rw [simulateQ_map, simulateQ_keccak256With_of_pure (permImpl π) forward π
    (fun S => simulateQ_forward _ S)]
  exact LawfulApplicative.map_pure _ _

/-- Over a fixed permutation, lifted to the same oracles, Keccak-256 of lanes is the pure one. -/
theorem simulateQ_liftTarget_keccak256LanesWith (π : Equiv.Perm State) (input : Array UInt64) :
    simulateQ ((permImpl π).liftTarget (PermComp State)) (keccak256LanesWith forward input) =
      pure (keccak256LanesWith (pureHash π) input).run :=
  simulateQ_keccak256LanesWith_of_pure _ forward π (fun S => by
    rw [simulateQ_forward, QueryImpl.liftTarget_apply]
    exact liftM_pure _) input

/-- Coins pass through the run of the hash queries. -/
theorem simulateQ_keccakImpl_liftM_prob {α : Type} (oa : ProbComp α) :
    simulateQ keccakImpl (liftM oa : OracleComp OracleWorld α) =
      (liftM oa : OracleComp (unifSpec + PermSpec State) α) := by
  rw [QueryImpl.simulateQ_liftM_eq_of_query _ (fun t => liftM (unifSpec.query t)) fun _ => rfl]
  rfl

/-- `H` with its query run as Keccak-256 is Keccak-256 of the lanes over the permutation. -/
theorem simulateQ_keccakImpl_queryLanes (input : Array UInt64) :
    simulateQ keccakImpl (liftM (queryLanes input : OracleComp HashSpec Lanes4) :
      OracleComp OracleWorld Lanes4) = keccak256LanesWith forward input := by
  -- The answer read back as lanes is the lanes the bytes came from.
  have hlanes : ∀ L : Lanes4, ofOutputLanes (digestEquiv.symm L.bytes) = L := fun L =>
    Lanes4.bytes_injective ((bytes_ofOutputLanes _).trans
      ((digestEquiv_eq_ofOutput _).symm.trans (Equiv.apply_symm_apply _ _)))
  simp only [queryLanes, oracleHash, _root_.liftM_map]
  change simulateQ keccakImpl (ofOutputLanes <$>
    (liftM (OracleSpec.query (spec := OracleWorld) (Sum.inr (lanesBytes input))) :
      OracleComp OracleWorld _)) = _
  rw [simulateQ_map, simulateQ_spec_query]
  change ofOutputLanes <$> (digestEquiv.symm <$>
    keccak256With forward (listEquivByteArray (lanesBytes input))) = _
  -- The byte array of a list of bytes is the array of that list.
  have hbytes : listEquivByteArray (lanesBytes input) = ⟨(lanesBytes input).toArray⟩ :=
    ByteArray.ext (by simp [listEquivByteArray])
  rw [hbytes, ← keccak256LanesWith_lanesBytes]
  refine ((comp_map _ _ _).symm.trans (comp_map _ _ _).symm).trans ?_
  exact (congrArg (· <$> keccak256LanesWith forward input) (funext hlanes : _ = id)).trans
    (LawfulFunctor.id_map _)

/-- A call of `H` on lanes is charged at most one per block of its input. -/
theorem isChargeBound_queryLanes (input : Array UInt64) :
    IsChargeBound (liftM (queryLanes input : OracleComp HashSpec Lanes4) :
      OracleComp OracleWorld Lanes4) (hashCharge (hs := HashSpec) blockCost)
        (hashBlocks input.size) := by
  simp only [queryLanes, oracleHash, _root_.liftM_map, isChargeBound_map_iff']
  change IsChargeBound (liftM (OracleSpec.query (spec := OracleWorld)
    (Sum.inr (lanesBytes input))) : OracleComp OracleWorld _) _ _
  -- The query is on the bytes of the lanes, eight per lane.
  have hcost : blockCost (lanesBytes input) ≤ hashBlocks input.size := by
    simp [blockCost, listEquivByteArray, keccak256Cost, hashBlocks]
  exact ⟨(zero_add _).trans_le hcost, fun _ => (zero_add _).trans_le hcost⟩

/-- A forward call of the permutation is one call of it. -/
theorem isChargeBound_forward {A : Type} (a : A) :
    IsChargeBound (forward a) (hashCost (hs := PermSpec A)) 1 := by
  change IsChargeBound (liftM (OracleSpec.query (spec := unifSpec + PermSpec A)
    (Sum.inr (Sum.inl a))) : OracleComp (unifSpec + PermSpec A) _) _ _
  have h : 0 + hashCost (hs := PermSpec A) (Sum.inr (Sum.inl a)) ≤ 1 := le_rfl
  exact ⟨h, fun _ => h⟩

/-- Keccak-256 of lanes over the permutation makes one call of it per block of its input. -/
theorem isChargeBound_keccak256LanesWith_forward (input : Array UInt64) :
    IsChargeBound (keccak256LanesWith forward input) (hashCost (hs := PermSpec State))
      (hashBlocks input.size) := by
  have h := isChargeBound_keccak256LanesWith isChargeBound_forward input
  rwa [one_mul] at h

variable {Request Message PublicKey SecretKey Signature : Type}
  [DecidableEq Message] [DecidableEq Signature]

/-- **A random-oracle bound of strong unforgeability holds in the random-permutation model.**

The scheme's hash calls become Keccak-256 over the permutation.

Key generation, each request and verification are charged at most `K`, `S` and `V` blocks.

With `K + maxSignings * S + V ≤ 2^128` and `bits` at most 128, the slack grows by one. -/
theorem stronglyUnforgeable_randomPermutationModel_of_randomOracleModel
    (scheme : SufCma.Scheme HashSpec Request Message PublicKey SecretKey Signature)
    {maxSignings slack bits K S V : ℕ} (hbits : bits ≤ 128)
    (hrom : SufCma.StronglyUnforgeable scheme (randomOracleModel HashSpec) maxSignings slack bits)
    (hK : IsChargeBound scheme.keyGen (hashCharge (hs := HashSpec) blockCost) K)
    (hS : ∀ sk request,
      IsChargeBound (scheme.sign sk request) (hashCharge (hs := HashSpec) blockCost) S)
    (hV : ∀ pk message signature,
      IsChargeBound (scheme.verify pk message signature) (hashCharge (hs := HashSpec) blockCost) V)
    (hsmall : K + maxSignings * S + V ≤ 2 ^ 128) :
    SufCma.StronglyUnforgeable (scheme.mapOracles keccakImpl) (randomPermutationModel State)
      maxSignings (slack + 1) bits := by
  intro q adversary hq hn
  rcases le_or_gt q (2 ^ 128) with hcap | hcap
  · have h := advantage_randomPermutationModel_le keccakOutput_indifferentiable keccakImpl
      (fun _ => rfl) simulateQ_permImpl_keccakImpl scheme hrom hK hS hV adversary hq hn
    -- The game costs at most `2^129`: the scheme at most `2^128`, the adversary at most `2^128`.
    have hN : K + (q + maxSignings * S) + V ≤ 2 ^ 129 := by
      rw [show 129 = 128 + 1 from rfl, pow_succ]
      generalize (2 : ℕ) ^ 128 = M at hcap hsmall ⊢
      omega
    refine h.trans ((add_le_add le_rfl (spongeIndiffBound_le hN hbits)).trans_eq ?_)
    push_cast
    ring
  · -- Past `2^128` calls the bound is at least 1, which bounds every chance.
    refine (prEvent_le_one _).trans ?_
    have hq1 : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
      have h2 : ((2 ^ bits : ℕ) : ℝ≥0∞) ≤ q := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hbits).trans hcap.le
      calc (1 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ bits * (2 : ℝ≥0∞)⁻¹ ^ bits := by
            rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
        _ ≤ (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
            gcongr
            exact_mod_cast h2
    exact hq1.trans (by gcongr; exact le_self_add)

end EthLib.Cryptography.HashSig

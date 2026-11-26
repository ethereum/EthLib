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

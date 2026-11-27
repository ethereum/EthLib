module

public import EthLib.Cryptography.Proofs.SufCma.MultiKey
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.AdversaryBudget

/-!
# Proofs: leanXMSS with many keys

The game extends the one-key game of the leanXMSS specification draft, section "Security".

It has `N` keys, and the adversary forges under one of its choice, with no key revealed.

With `qH` calls of `H` and `r` requests in all, it forges with chance at most `N * Q / 2^127`.

`Q = N * (205 * 2^16 + 1) + qH + r * (2^33 + 205 * 2^16 + 407) + 172` bounds each reduction's game.

The key-generation term grows as `N^2`: with `N = 2^20` keys and no request, the bound is `2^-63.3`.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open XmssSecurity (HashSpec)

/-- An adaptive adversary against `N` leanXMSS keys. -/
abbrev MultiAdversary (N : ℕ) :=
  SufCma.MultiAdversary HashSpec N SignRequest Message PublicKey Signature

/-- The hash calls of the game of each reduction, for `N` keys, `qH` calls of `H` and `r` requests.

It counts `N` key generations, the adversary's calls, each request at worst, and verification. -/
def multiGameQueries (N qH r : ℕ) : ℕ :=
  N * keyGenQueries + (qH + r * requestQueries) + verifyQueries

/-- The game of each reduction makes at most `N * K + qH + r * S + V` hash calls on every run.

`K`, `S` and `V` bound key generation, one request and verification. -/
theorem isQueryBoundP_game_reduction {N : ℕ} (adversary : MultiAdversary N) (j : Fin N)
    {qH r : ℕ}
    (hh : ∀ pks, IsQueryBoundP (adversary.main pks)
      (SufCma.IsAdversaryHash HashSpec (Fin N × SignRequest) Signature) qH)
    (hr : ∀ pks, IsQueryBoundP (adversary.main pks)
      (SufCma.IsAdversaryRequest HashSpec (Fin N × SignRequest) Signature) r) :
    IsQueryBoundP (SufCma.game scheme (SufCma.reduction scheme adversary j))
      (SufCma.IsHashCall HashSpec) (multiGameQueries N qH r) := by
  rw [SufCma.isQueryBoundP_isHashCall_iff]
  refine SufCma.isChargeBound_game_reduction scheme SufCma.hashCost adversary j
    ((SufCma.isQueryBoundP_isHashCall_iff _ _).1 ?_)
    (fun sk request => (SufCma.isQueryBoundP_isHashCall_iff _ _).1 ?_)
    (fun pk message signature => (SufCma.isQueryBoundP_isHashCall_iff _ _).1 ?_)
    (fun pks => ((isQueryBoundP_iff_isChargeBound _ _ _).1 (hh pks)).mono_charge ?_) hr
  -- Key generation: the seed's coins, then the key.
  · exact (isQueryBoundP_bind (isQueryBoundP_liftM_prob sampleSeed) fun seed _ =>
      isQueryBoundP_liftM_hash _ (isQueryBoundP_keyGenWith_keyGenQueries seed)).mono (by omega)
  · exact (isQueryBoundP_map_iff _ _ _).2
      (isQueryBoundP_liftM_hash _ (isQueryBoundP_signWith_requestQueries sk _ _))
  · exact isQueryBoundP_liftM_hash _ (isQueryBoundP_verifyWith isQueryBoundP_H _ _ _)
  -- An adversary's query costs one exactly when it is a hash call.
  · exact fun t => (SufCma.adversaryCharge_hashCost t).le

/-- **leanXMSS with `N` keys is strongly unforgeable in the random oracle model.**

Take an adversary that makes at most `qH` calls of `H` and `r` requests in all, on every run.

It forges under some key with probability at most `N * Q / 2^127`.

`Q` bounds the hash calls of each reduction's game, which makes all `N` key generations.

So the loss is a factor `N`, and a key-generation term in `N^2 * (205 * 2^16 + 1)`.

With `N = 2^20` keys and `2^32` requests in all, the bound is about `2^-42`.

With `2^32` requests per key, it is about `2^-22`. -/
theorem multiAdvantage_le {N : ℕ} (adversary : MultiAdversary N) {qH r : ℕ}
    (hh : ∀ pks, IsQueryBoundP (adversary.main pks)
      (SufCma.IsAdversaryHash HashSpec (Fin N × SignRequest) Signature) qH)
    (hr : ∀ pks, IsQueryBoundP (adversary.main pks)
      (SufCma.IsAdversaryRequest HashSpec (Fin N × SignRequest) Signature) r) :
    SufCma.multiAdvantage scheme (SufCma.randomOracleModel HashSpec) adversary ≤
      N * ((multiGameQueries N qH r : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 127) :=
  SufCma.multiAdvantage_le_card_mul scheme adversary fun j =>
    unforgeable _ (by simp only [multiGameQueries, verifyQueries]; omega) _
      ((hashQueryBound_iff_counted _).1 (XmssSecurity.hashQueryBound_of_isQueryBoundP _
        (isQueryBoundP_game_reduction adversary j hh hr) ∅))

end EthLib.Cryptography.Xmss.Unforgeability

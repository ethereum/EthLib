module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.AdversaryBudget
public import EthLib.Cryptography.Proofs.Xmss.Cost
public import EthLib.Cryptography.Proofs.Xmss.MapMonad
public import EthLib.Cryptography.Proofs.HashSig.Permutation

/-!
# Proofs: leanXMSS in the random-permutation model

Source: the leanXMSS specification draft, section "Security".

`H` is Keccak-256 over a random permutation of the Keccak state, whose inverse is an oracle too.

The adversary is charged for its own calls of the permutation and its inverse only.

The bound is that of the random-oracle model plus one unit `2^-127`.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal PFunctor.FreeM
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants (LOG_LIFETIME)
open EthLib.Cryptography.Hash.Keccak (State keccak256LanesWith)
open EthLib.Cryptography.LazyPermutation (PermSpec forward)
open EthLib.Cryptography.HashSig (HashSpec keccakImpl blockCost simulateQ_keccakImpl_liftM_prob
  isChargeBound_keccak256LanesWith_forward)

/-- The algorithms lift to the game's oracles with `H`, since lifting keeps `pure` and `bind`. -/
private theorem liftM_keyGenWith_signWith_verifyWith :
    (∀ seed, (liftM (keyGenWith H seed) : OracleComp XmssSecurity.OracleWorld _) =
      keyGenWith (fun x => liftM (H x)) seed) ∧
    (∀ sk idx msg, (liftM (signWith H sk idx msg) : OracleComp XmssSecurity.OracleWorld _) =
      signWith (fun x => liftM (H x)) sk idx msg) ∧
    (∀ pk msg sig, (liftM (verifyWith H pk msg sig) : OracleComp XmssSecurity.OracleWorld _) =
      verifyWith (fun x => liftM (H x)) pk msg sig) :=
  have map_pure := fun {β : Type} (b : β) =>
    (_root_.liftM_pure b : (liftM (pure b : OracleComp XmssSecurity.HashSpec β) :
      OracleComp XmssSecurity.OracleWorld β) = pure b)
  have map_bind := fun {β γ : Type} (x : OracleComp XmssSecurity.HashSpec β)
      (f : β → OracleComp XmssSecurity.HashSpec γ) =>
    (_root_.liftM_bind x f : (liftM (x >>= f) : OracleComp XmssSecurity.OracleWorld γ) = _)
  ⟨keyGenWith_map_monad _ map_pure map_bind H, signWith_map_monad _ map_pure map_bind H,
    verifyWith_map_monad _ map_pure map_bind H⟩

/-- leanXMSS with `H` Keccak-256 over a random permutation of the Keccak state.

`H` makes one forward call of the permutation per block of its input.

The rule of use is the scheme's: no leaf index is requested twice. -/
noncomputable def schemeRpm :
    SufCma.Scheme (PermSpec State) SignRequest Message PublicKey SecretKey Signature :=
  { scheme with
    keyGen := liftM sampleSeed >>= fun seed => keyGenWith (keccak256LanesWith forward) seed
    sign := fun sk request => (fun result => (result.1.toOption, result.2)) <$>
      signWith (keccak256LanesWith forward) sk request.leafIndex request.message
    verify := fun pk message signature =>
      verifyWith (keccak256LanesWith forward) pk message signature }

/-- `H` with its query run as Keccak-256 is Keccak-256 of the lanes over the permutation. -/
theorem simulateQ_keccakImpl_queryH (input : Array UInt64) :
    simulateQ keccakImpl (liftM (H input) : OracleComp XmssSecurity.OracleWorld Lanes4) =
      keccak256LanesWith forward input :=
  HashSig.simulateQ_keccakImpl_queryLanes input

/-- The scheme over the permutation is the scheme with each hash query run as Keccak-256. -/
theorem schemeRpm_eq_mapOracles : schemeRpm = scheme.mapOracles keccakImpl := by
  -- Running the hash queries keeps `pure` and `bind`, and sends `H` to Keccak-256.
  let φ : ∀ {β : Type}, OracleComp XmssSecurity.HashSpec β →
      OracleComp (unifSpec + PermSpec State) β :=
    fun x => simulateQ keccakImpl (liftM x : OracleComp XmssSecurity.OracleWorld _)
  have map_pure : ∀ {β : Type} (b : β), φ (pure b) = pure b := fun b => by
    simp only [φ, _root_.liftM_pure, simulateQ_pure]
  have map_bind : ∀ {β γ : Type} (x : OracleComp XmssSecurity.HashSpec β)
      (f : β → OracleComp XmssSecurity.HashSpec γ), φ (x >>= f) = φ x >>= fun b => φ (f b) :=
    fun x f => by simp only [φ, _root_.liftM_bind, simulateQ_bind]
  have hH : (fun x => φ (H x)) = keccak256LanesWith forward := funext simulateQ_keccakImpl_queryH
  -- Key generation: the seed passes through, and `H` becomes Keccak-256.
  have hK : simulateQ keccakImpl scheme.keyGen =
      liftM sampleSeed >>= fun seed => keyGenWith (keccak256LanesWith forward) seed := by
    change simulateQ keccakImpl (liftM sampleSeed >>= fun seed =>
      (liftM (keyGenWith H seed) : OracleComp XmssSecurity.OracleWorld _)) = _
    rw [simulateQ_bind, simulateQ_keccakImpl_liftM_prob]
    refine bind_congr fun seed => ?_
    exact (keyGenWith_map_monad φ map_pure map_bind H seed).trans (by rw [hH])
  -- Signing and verification: `H` becomes Keccak-256.
  have hS : ∀ sk request, simulateQ keccakImpl (scheme.sign sk request) =
      (fun result => (result.1.toOption, result.2)) <$>
        signWith (keccak256LanesWith forward) sk request.leafIndex request.message :=
    fun sk request => by
      change simulateQ keccakImpl ((fun result => (result.1.toOption, result.2)) <$>
        (liftM (signWith H sk request.leafIndex request.message) :
          OracleComp XmssSecurity.OracleWorld _)) = _
      rw [simulateQ_map]
      exact congrArg _ ((signWith_map_monad φ map_pure map_bind H sk _ _).trans (by rw [hH]))
  have hV : ∀ pk message signature, simulateQ keccakImpl (scheme.verify pk message signature) =
      verifyWith (keccak256LanesWith forward) pk message signature := fun pk message signature =>
    (verifyWith_map_monad φ map_pure map_bind H pk message signature).trans (by rw [hH])
  unfold schemeRpm SufCma.Scheme.mapOracles
  simp only [hK, hS, hV]

/-! ## The permutation calls of the algorithms -/

/-- A call of `H` among the game's oracles is charged at most one per block of its input. -/
theorem isChargeBound_liftM_H (input : Array UInt64) :
    IsChargeBound (liftM (H input) : OracleComp XmssSecurity.OracleWorld Lanes4)
      (SufCma.hashCharge (hs := HashSpec) blockCost) (Hash.Keccak.hashBlocks input.size) :=
  HashSig.isChargeBound_queryLanes input

/-- Key generation is charged at most `13893633` blocks. -/
theorem isChargeBound_scheme_keyGen :
    IsChargeBound scheme.keyGen (SufCma.hashCharge (hs := HashSpec) blockCost) 13893633 := by
  have hk : ∀ seed, IsChargeBound (liftM (keyGenWith H seed) :
      OracleComp XmssSecurity.OracleWorld _) (SufCma.hashCharge (hs := HashSpec) blockCost)
        13893633 := fun seed => by
    rw [liftM_keyGenWith_signWith_verifyWith.1 seed]
    exact Cost.isChargeBound_keyGenWith_hashBlocks isChargeBound_liftM_H seed
  have h := (SufCma.isChargeBound_hashCharge_liftM blockCost sampleSeed).bind hk
  rw [zero_add] at h
  exact h

/-- A request is charged at most `8603828495` blocks, whatever the key. -/
theorem isChargeBound_scheme_sign (sk : SecretKey) (request : SignRequest) :
    IsChargeBound (scheme.sign sk request) (SufCma.hashCharge (hs := HashSpec) blockCost)
      8603828495 := by
  refine (isChargeBound_map_iff' _ _).2 ?_
  rw [liftM_keyGenWith_signWith_verifyWith.2.1]
  exact Cost.isChargeBound_signWith_hashBlocks isChargeBound_liftM_H sk _ _

/-- Verification is charged at most `186` blocks. -/
theorem isChargeBound_scheme_verify (pk : PublicKey) (message : Message)
    (signature : Signature) :
    IsChargeBound (scheme.verify pk message signature)
      (SufCma.hashCharge (hs := HashSpec) blockCost) 186 := by
  change IsChargeBound (liftM (verifyWith H pk message signature) :
    OracleComp XmssSecurity.OracleWorld _) _ _
  rw [liftM_keyGenWith_signWith_verifyWith.2.2]
  exact Cost.isChargeBound_verifyWith_hashBlocks isChargeBound_liftM_H pk message signature

/-! ## The permutation calls of the scheme over the permutation -/

/-- Key generation over the permutation makes at most `13893633` calls of it. -/
theorem isChargeBound_schemeRpm_keyGen :
    IsChargeBound schemeRpm.keyGen (SufCma.hashCost (hs := PermSpec State)) 13893633 := by
  have h := (SufCma.isChargeBound_hashCharge_liftM _ sampleSeed).bind fun seed =>
    Cost.isChargeBound_keyGenWith_hashBlocks isChargeBound_keccak256LanesWith_forward seed
  rw [zero_add] at h
  exact h

/-- A request over the permutation makes at most `8603828495` calls of it, whatever the key. -/
theorem isChargeBound_schemeRpm_sign (sk : SecretKey) (request : SignRequest) :
    IsChargeBound (schemeRpm.sign sk request) (SufCma.hashCost (hs := PermSpec State))
      8603828495 :=
  (isChargeBound_map_iff' _ _).2
    (Cost.isChargeBound_signWith_hashBlocks isChargeBound_keccak256LanesWith_forward sk _ _)

/-- Verification over the permutation makes at most `186` calls of it. -/
theorem isChargeBound_schemeRpm_verify (pk : PublicKey) (message : Message)
    (signature : Signature) :
    IsChargeBound (schemeRpm.verify pk message signature)
      (SufCma.hashCost (hs := PermSpec State)) 186 :=
  Cost.isChargeBound_verifyWith_hashBlocks isChargeBound_keccak256LanesWith_forward pk message
    signature

/-! ## The theorem -/

/-- **leanXMSS is strongly unforgeable in the random-permutation model.**

The adversary itself makes at most `q` calls of the permutation or its inverse.

It makes at most `2^32` requests, and forges with probability at most `(q + 531) * 2^-127`.

Key generation, the signer and the final verification are not charged to `q`. -/
theorem stronglyUnforgeable_randomPermutationModel :
    SufCma.StronglyUnforgeable schemeRpm (SufCma.randomPermutationModel State)
      (2 ^ LOG_LIFETIME) 531 127 := by
  rw [schemeRpm_eq_mapOracles]
  have hsmall : 13893633 + 2 ^ LOG_LIFETIME * 8603828495 + 186 ≤ 2 ^ 128 := by
    norm_num [LOG_LIFETIME, Constants.LAYER_HEIGHT]
  have h := HashSig.stronglyUnforgeable_randomPermutationModel_of_randomOracleModel scheme
    (by norm_num) stronglyUnforgeable isChargeBound_scheme_keyGen isChargeBound_scheme_sign
    isChargeBound_scheme_verify hsmall
  exact h

/-- **leanXMSS is strongly unforgeable in the random-permutation model, with slack `2^10`.**

The adversary itself makes at most `q` calls of the permutation or its inverse and `2^32` requests.

It forges with probability at most `(q + 2^10) * 2^-127`. -/
theorem stronglyUnforgeable_randomPermutationModel_two_pow_ten :
    SufCma.StronglyUnforgeable schemeRpm (SufCma.randomPermutationModel State)
      (2 ^ LOG_LIFETIME) (2 ^ 10) 127 :=
  SufCma.StronglyUnforgeable.of_slack_le _ stronglyUnforgeable_randomPermutationModel
    (by norm_num)

end EthLib.Cryptography.Xmss.Unforgeability

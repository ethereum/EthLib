module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.CachedSelectionBound
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CappedUnifiedExpectedDigest
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.LossDecomposition

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def WinningSecondLaneBadEventOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  WinningCachedSelectionOccurs execution ∨
    WinningStructuralCollisionOccurs execution.2.1.1 execution.1

def HasSecondLaneBound
    (q : Nat) (adversary : Adversary) : Prop :=
  Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningSecondLaneBadEventOccurs x] ≤
    q /
      ((2 ^ digestBits : Nat) : ENNReal)

/-- Lane 2's structural term, by the source game's expected structural queries. -/
theorem winningStructuralCollision_le_expectedStructural (adversary : Adversary) :
    Pr{let execution ← cappedDetailedGameWithEncodingTrace adversary}[
        WinningStructuralCollisionOccurs execution.2.1.1 execution.1] ≤
      expectedPostKeygenStructuralQueries adversary / ((2 ^ digestBits : Nat) : ENNReal) :=
  calc
    _ = Pr{let execution ← detailedGameWithCache Concrete.scheme adversary}[
          WinningStructuralCollisionOccurs execution.2 execution.1] := by
      rw [← cappedDetailedGameWithEncodingTrace_cache_projection, prEvent_map]
    _ ≤ _ :=
      winningStructuralCollision_probability_le_expectedPostKeygenStructuralQueries adversary

theorem hasSecondLaneBound_of_hashQueryBound
    (q : Nat) (adversary : Adversary)
    (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q) (hq : q < 2 ^ 127) :
    HasSecondLaneBound q adversary := by
  let encoding := CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary
  let structural := expectedPostKeygenStructuralQueries adversary
  have hstructural :
      Pr{let execution ← cappedDetailedGameWithEncodingTrace adversary}[WinningStructuralCollisionOccurs execution.2.1.1 execution.1] ≤
      structural / ((2 ^ digestBits : Nat) : ENNReal) :=
    winningStructuralCollision_le_expectedStructural adversary
  unfold HasSecondLaneBound WinningSecondLaneBadEventOccurs
  calc
    Pr{let execution ← cappedDetailedGameWithEncodingTrace adversary}[WinningCachedSelectionOccurs execution ∨
          WinningStructuralCollisionOccurs execution.2.1.1 execution.1] ≤
      Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningCachedSelectionOccurs x] +
        Pr{let execution ← cappedDetailedGameWithEncodingTrace adversary}[WinningStructuralCollisionOccurs execution.2.1.1 execution.1] :=
      prEvent_or_le _ _ _
    _ ≤ encoding / ((2 ^ digestBits : Nat) : ENNReal) +
        structural / ((2 ^ digestBits : Nat) : ENNReal) :=
      add_le_add
        (capped_cachedSelection_probability_le_expectedDigest q adversary hbound hq)
        hstructural
    _ = (encoding + structural) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
      simp only [div_eq_mul_inv, add_mul]
    _ ≤ q /
        ((2 ^ digestBits : Nat) : ENNReal) := by
      gcongr
      exact postKeygenEncoding_add_structural_expected_le q adversary hbound

/-- Coins, lifted to the game, make no query in a class that holds no coin. -/
theorem isQueryBoundP_liftM_coins {R : OracleWorld.Domain → Prop} [DecidablePred R]
    (hcoin : ∀ n, ¬R (.inl n)) (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp OracleWorld α) R 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind n k ih =>
    simp only [liftM_bind]
    exact isQueryBoundP_bind_zero _ _
      ((isQueryBoundP_query_iff (spec := OracleWorld) _ (.inl n) 0).2 fun h => (hcoin n h).elim) ih

/-- The signer makes no query in a class that holds no coin and no encoding input of its index.

Each attempt hashes one encoding input, and the randomizer base is drawn from coins. -/
theorem sign_isQueryBoundP_zero {R : OracleWorld.Domain → Prop} [DecidablePred R]
    (hcoin : ∀ n, ¬R (.inl n)) (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message)
    (hencoding : ∀ payload,
      ¬R (.inr (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload))) :
    IsQueryBoundP (Concrete.scheme.sign secretKey leafIndex message) R 0 := by
  -- One attempt queries only its encoding input.
  have hattempt : ∀ randomness, IsQueryBoundP
      (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld _) R 0 := fun randomness =>
    isQueryBoundP_liftM_hashSpec _ <| isQueryBoundP_bind (m := 0)
      (by simp [Concrete.encodingHash_eq, Concrete.tweakableHash, Concrete.oracleHash,
        show ¬R (.inr (tweakableHashInput secretKey.parameter (.encoding leafIndex)
          (Concrete.encodingPayload message randomness))) by
            simpa only [Concrete.CacheView.encodingInput] using hencoding (message, randomness)])
      fun digest _ => by
        cases TargetSum.decodeDigest digest <;> exact isQueryBoundP_pure _ _ _
  -- The attempts, one after another, from any trial.
  have hattempts : ∀ base attempts trial, IsQueryBoundP
      (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base attempts trial)
        R 0 := by
    intro base attempts
    induction attempts with
    | zero => intro trial; exact isQueryBoundP_pure _ _ _
    | succ attempts ih =>
      intro trial
      rw [Concrete.precomputedSignBoundedAttempts]
      refine isQueryBoundP_bind (m := 0) (hattempt _) fun result _ => ?_
      cases result with
      | some signature => exact isQueryBoundP_pure _ _ _
      | none => exact ih (trial + 1)
  rw [Concrete.scheme_sign, Concrete.precomputedCappedSign]
  exact isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_liftM_coins hcoin _) fun base _ =>
    isQueryBoundP_bind (m := 0) (hattempts base _ 0) fun _ _ => isQueryBoundP_pure _ _ 0

open Ghost in
/-- Per key, the source game's structural queries are at most the adversary's and the verifier's.

The verification's structural queries are kept as their expectation over the adversary's run. -/
theorem structuralQueries_le_adversary (adversary : Adversary) (publicKey : PublicKey)
    (secretKey : SecretKey) (cache0 : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput secretKey cache0 input ≠ input)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey) cache0 ≤
      expectedSimulatedCost (impl publicKey secretKey)
          (fun input _ => if IsAdvQuery (Rom.IsRelevantHashQuery fun x =>
            keygenStructuralTargetInput secretKey cache0 x ≠ x) input then 1 else 0)
          (adversary.main publicKey) ((cache0, []), 0) +
        ∑' y, Pr{let x ← ((simulateQ romImpl (simulateQ
            (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
            (adversary.main publicKey))).run cache0)}[x = y] *
          expectedSimulatedQueryCount romImpl
            (Rom.IsRelevantHashQuery fun input =>
              keygenStructuralTargetInput secretKey cache0 input ≠ input)
            (verifyCont publicKey y.1) y.2 := by
  -- The game is the adversary phase, then the verification.
  change expectedSimulatedQueryCount romImpl _
    (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey) >>= verifyCont publicKey) cache0 ≤ _
  rw [expectedSimulatedQueryCount_bind]
  -- The signer hashes only encoding inputs, which the structural targets leave in place.
  refine add_le_add (expectedSimulatedQueryCount_source_le_adv publicKey secretKey _
    (fun request => sign_isQueryBoundP_zero (fun _ => id) _ _ _ fun payload h => h ?_)
    _ _ _ _) le_rfl
  exact keygenStructuralTargetInput_encodingInput _ _ _ _

open Ghost in
/-- With at most `q` hash queries, the adversary makes at most `q` encoding and structural ones.

The two kinds are disjoint. -/
theorem adversaryEncoding_add_structural_le (q : Nat) (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (cache0 : QueryCache HashSpec)
    (hadv : IsQueryBoundP (adversary.main publicKey) IsAdvHash q) :
    expectedSimulatedCost (impl publicKey secretKey)
        (fun input _ => if IsAdvEncoding secretKey.parameter input then 1 else 0)
        (adversary.main publicKey) ((cache0, []), 0) +
      expectedSimulatedCost (impl publicKey secretKey)
        (fun input _ => if IsAdvQuery (Rom.IsRelevantHashQuery fun x =>
          keygenStructuralTargetInput secretKey cache0 x ≠ x) input then 1 else 0)
        (adversary.main publicKey) ((cache0, []), 0) ≤ q := by
  refine (expectedSimulatedCost_add _ _ _ _ _).symm.trans_le
    (expectedSimulatedCost_le_of_isQueryBoundP _ (p := IsAdvHash) (fun input _ => ?_) _ q _
      hadv)
  rcases input with (_ | x) | request
  · simp [IsAdvEncoding, IsAdvQuery, CappedEncodingMonitor.IsEncodingHashQuery,
      Rom.IsRelevantHashQuery]
  · have hdisjoint := encodingHashQuery_structuralQuery_disjoint secretKey cache0 (.inr x)
    rw [ite_eq_left (show IsAdvHash (.inl (.inr x)) from trivial)]
    by_cases he : IsAdvEncoding secretKey.parameter (.inl (.inr x))
    · rw [ite_eq_left he, ite_eq_right (show ¬IsAdvQuery (Rom.IsRelevantHashQuery fun y =>
        keygenStructuralTargetInput secretKey cache0 y ≠ y) (.inl (.inr x))
        from fun hs => hdisjoint ⟨he, hs⟩), add_zero]
    · rw [ite_eq_right he, zero_add]
      split_ifs <;> simp
  · simp [IsAdvEncoding, IsAdvQuery]

open Ghost in
/-- Lane 2's bound, charging only the adversary's own hash queries and the verification's.

The adversary makes at most `q` hash queries, and the verification at most `384`.

The verification is counted once: its two kinds of query are disjoint, as the adversary's are. -/
theorem hasSecondLaneBound_of_adversaryBound (q : Nat) (adversary : Adversary)
    (hadv : ∀ publicKey, IsQueryBoundP (adversary.main publicKey) IsAdvHash q)
    (hq : q < 2 ^ 127) :
    HasSecondLaneBound (q + 384) adversary := by
  -- The structural class of a key result.
  let structural := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    Rom.IsRelevantHashQuery fun input =>
      keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input
  -- The adversary's expected queries of a class, for one key result.
  let adv := fun (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
      (P : (OracleWorld + SigningSpec).Domain → Prop) [DecidablePred P] =>
    expectedSimulatedCost (impl keyResult.1.1 keyResult.1.2)
      (fun input _ => if P input then 1 else 0) (adversary.main keyResult.1.1)
      ((keyResult.2, []), 0)
  let enc := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    adv keyResult (IsAdvEncoding keyResult.1.2.parameter)
  let str := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    adv keyResult (IsAdvQuery (structural keyResult))
  -- The verification's expected queries of a class, after the adversary's run on one key result.
  let ver := fun (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
      (R : OracleWorld.Domain → Prop) [DecidablePred R] =>
    ∑' y, Pr{let x ← ((simulateQ romImpl (simulateQ
        (cappedSourceUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
        (adversary.main keyResult.1.1))).run keyResult.2)}[x = y] *
      expectedSimulatedQueryCount romImpl R (verifyCont keyResult.1.1 y.1) y.2
  let venc := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    ver keyResult (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
  let vstr := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    ver keyResult (structural keyResult)
  -- The source game's structural queries are the adversary's and the verification's.
  have hstr : ∀ keyResult : (PublicKey × SecretKey) × QueryCache HashSpec,
      expectedSimulatedQueryCount romImpl (structural keyResult)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2)
        keyResult.2 ≤ str keyResult + vstr keyResult := fun keyResult =>
    structuralQueries_le_adversary adversary keyResult.1.1 keyResult.1.2 keyResult.2
  -- The two kinds are disjoint hash queries of the adversary, at most `q` of them.
  have hsum : ∀ keyResult : (PublicKey × SecretKey) × QueryCache HashSpec,
      enc keyResult + str keyResult ≤ q := fun keyResult =>
    adversaryEncoding_add_structural_le q adversary keyResult.1.1 keyResult.1.2 keyResult.2
      (hadv keyResult.1.1)
  -- The verification's two kinds are disjoint too, at most `384` of them.
  have hver : ∀ keyResult : (PublicKey × SecretKey) × QueryCache HashSpec,
      venc keyResult + vstr keyResult ≤ 384 := fun keyResult =>
    tsum_expectedVerifyQueries_add_le_of_disjoint _ _
      (encodingHashQuery_structuralQuery_disjoint keyResult.1.2 keyResult.2) _ _
  unfold HasSecondLaneBound WinningSecondLaneBadEventOccurs
  refine (prEvent_or_le _ _ _).trans ?_
  -- Each key's cached selection is at most its share of the adversary's encoding queries.
  have hA : Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[
        WinningCachedSelectionOccurs x] ≤
      (∑' keyResult, Pr{let x ← (simulateQ romImpl Concrete.scheme.keygen).run ∅}[
        x = keyResult] * (enc keyResult + venc keyResult)) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
    rw [prEvent_winningCachedSelection_eq_tsum, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
    refine tsum_le_tsum fun keyResult => ?_
    -- Name the parts of the key result: the kernel would run key generation to match two forms.
    obtain ⟨⟨publicKey, secretKey⟩, cache0⟩ := keyResult
    by_cases hkey : ((publicKey, secretKey), cache0) ∈
        support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
    · rw [mul_assoc, ← div_eq_mul_inv]
      refine mul_le_mul' le_rfl ?_
      dsimp only [enc, venc, adv, ver]
      -- Pass the key's parts by name, not as projections from the goal.
      exact cachedSelection_afterKeygen_le_adversaryDigest (publicKey := publicKey)
        (secretKey := secretKey) (cache0 := cache0) q adversary hadv hq hkey
    · simp [(prEvent_eq_zero_of_not_mem_support _) hkey]
  -- The structural collisions are at most the adversary's structural queries, per key.
  have hB : Pr{let execution ← cappedDetailedGameWithEncodingTrace adversary}[
        WinningStructuralCollisionOccurs execution.2.1.1 execution.1] ≤
      (∑' keyResult, Pr{let x ← (simulateQ romImpl Concrete.scheme.keygen).run ∅}[
        x = keyResult] * (str keyResult + vstr keyResult)) /
        ((2 ^ digestBits : Nat) : ENNReal) :=
    (winningStructuralCollision_le_expectedStructural adversary).trans
      (ENNReal.div_le_div_right (tsum_le_tsum fun keyResult => mul_le_mul' le_rfl
        (hstr keyResult)) _)
  refine (add_le_add hA hB).trans ?_
  rw [ENNReal.div_add_div_same, ← tsum_add]
  refine ENNReal.div_le_div_right ?_ _
  calc _ ≤ ∑' keyResult, Pr{let x ← (simulateQ romImpl Concrete.scheme.keygen).run ∅}[
          x = keyResult] * ((q + 384 : Nat) : ENNReal) := tsum_le_tsum fun keyResult => by
        rw [← mul_add]
        refine mul_le_mul' le_rfl ?_
        calc enc keyResult + venc keyResult + (str keyResult + vstr keyResult) =
              enc keyResult + str keyResult + (venc keyResult + vstr keyResult) := by ring
          _ ≤ q + 384 := add_le_add (hsum keyResult) (hver keyResult)
          _ = _ := by norm_cast
    _ ≤ _ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)

/-- Lane 1's constant, the verification's queries and the encoding monitor's. -/
def firstLaneSlack : Nat := 2 ^ 19

theorem capped_two_lane_loss_budget (q : Nat) :
    ((q + firstLaneSlack : Nat) : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) ≤
      ((2 * q + lowerOrderSlack : Nat) : ENNReal) / ((2 ^ 128 : Nat) : ENNReal) := by
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div _ (by norm_num [digestBits])
  exact_mod_cast (show q + firstLaneSlack + q ≤ 2 * q + lowerOrderSlack by
    simp only [firstLaneSlack, lowerOrderSlack]; omega)

end XmssSecurity

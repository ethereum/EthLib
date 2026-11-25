module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.IdealSearch
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.AdversaryBudget
public import EthLib.Cryptography.Proofs.HashSig.FailedSearch
import EthLib.Cryptography.Proofs.HashSig.Interchange

/-!
# Proofs: signing inside the game rarely fails, over the key's lifetime

Take an adversary with at most `qH` hash queries and `r` signing requests in every run.

Some request of its game fails with probability at most `Q (1 - p)^(2^31) <= Q exp(-2000)`.

`Q` bounds the game's hash calls, and `p` is the chance that one trial gives a codeword.

A failed request leaves in the cache an aligned block of `2^31` trials that all missed.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open XmssSecurity (OracleWorld HashSpec HashOutput HashInput)

-- A concrete height or trial count lets Lean unfold a whole tree or search, so both stay opaque.
attribute [local irreducible] LAYER_HEIGHT MAX_RANDOMIZER_TRIALS

/-! ## Aligned blocks of trials -/

/-- The hash input of trial `j` of a block, whose randomizer is `b 2^31 + j`.

A block is a public parameter, an address, a message and a block number `b < 2^97`. -/
def blockPoint (block : PublicParam × Address × Array UInt64 × Fin (2 ^ 97)) (j : ℕ) :
    HashInput :=
  Hash.Keccak.lanesBytes (thInput block.1 block.2.1
    (block.2.2.1 ++ (trialRandomizer ⟨0, 0⟩ (block.2.2.2.val * 2 ^ 31 + j)).toArray))

/-- An answer misses the code: the first half of its digest is not a codeword. -/
def TrialMiss (u : HashOutput) : Prop :=
  codeword? (halfOf 0 (ofOutput u)) = none

instance : DecidablePred TrialMiss := fun u =>
  inferInstanceAs (Decidable (codeword? (halfOf 0 (ofOutput u)) = none))

/-- One uniform answer misses the code with probability `1 - |C| / 2^128`. -/
theorem prEvent_trialMiss :
    Pr{let u ← $ᵗ HashOutput}[TrialMiss u] = ((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128 :=
  prEvent_not_codeword

/-- The randomizer with two zero lanes is the integer `0`. -/
theorem toNat_zero_randomizer : (⟨0, 0⟩ : Randomizer).toNat = 0 := by
  simp [Hash.Keccak.Lanes2.toNat]

/-- Two trials below `2^31` hash one input only when they are one trial of one block. -/
theorem blockPoint_inj (block block' : PublicParam × Address × Array UInt64 × Fin (2 ^ 97))
    (j j' : ℕ) (hj : j < 2 ^ 31) (hj' : j' < 2 ^ 31)
    (h : blockPoint block j = blockPoint block' j') : block = block' ∧ j = j' := by
  obtain ⟨P, A, m, b⟩ := block
  obtain ⟨P', A', m', b'⟩ := block'
  simp only [blockPoint] at h
  obtain ⟨rfl, rfl, hin⟩ := thInput_inj (Hash.Keccak.lanesBytes_injective h)
  -- A randomizer has two lanes, so the two messages have one length.
  have hsize : m.size = m'.size := by
    have h2 := congrArg Array.size hin
    simp [Hash.Keccak.Lanes2.toArray] at h2
    omega
  obtain ⟨rfl, hr⟩ := Array.append_inj hin hsize
  simp only [Hash.Keccak.Lanes2.toArray, List.toArray, Array.mk.injEq, List.cons.injEq,
    and_true] at hr
  have hrho := congrArg Hash.Keccak.Lanes2.toNat (Hash.Keccak.Lanes2.ext hr.1 hr.2)
  simp only [toNat_trialRandomizer, toNat_zero_randomizer] at hrho
  have hb := b.isLt
  have hb' := b'.isLt
  have hbb : b = b' := Fin.ext (by omega)
  subst hbb
  exact ⟨rfl, by omega⟩

/-- **Every window of `2^32` trials holds an aligned block of `2^31`.**

The trials from a base `R_0` take the randomizers `R_0 + c` modulo `2^128`, for `c < 2^32`.

Since `2^31` divides `2^128`, some `2^31` consecutive ones are `b 2^31 + j` for `j < 2^31`. -/
theorem exists_block_of_window (base : Randomizer) :
    ∃ b < 2 ^ 97, ∃ c, c + 2 ^ 31 ≤ 2 ^ 32 ∧ ∀ j < 2 ^ 31,
      trialRandomizer base (c + j) = trialRandomizer ⟨0, 0⟩ (b * 2 ^ 31 + j) := by
  -- The block starts at the first multiple `(d + 1) 2^31` above the base, modulo `2^128`.
  obtain ⟨d, m, hdm, hm⟩ : ∃ d m, 2 ^ 31 * d + m = base.toNat ∧ m < 2 ^ 31 :=
    ⟨_, _, Nat.div_add_mod base.toNat (2 ^ 31), Nat.mod_lt _ (by norm_num)⟩
  refine ⟨(d + 1) % 2 ^ 97, Nat.mod_lt _ (by norm_num), (d + 1) * 2 ^ 31 - base.toNat,
    by omega, fun j hj => ?_⟩
  apply Hash.Keccak.Lanes2.toNat_injective
  have hsum : base.toNat + ((d + 1) * 2 ^ 31 - base.toNat + j) = (d + 1) * 2 ^ 31 + j := by
    omega
  have hwrap : (d + 1) % 2 ^ 97 * 2 ^ 31 = (d + 1) * 2 ^ 31 % 2 ^ 128 := by
    rw [← Nat.mul_mod_mul_right]
    norm_num
  rw [toNat_trialRandomizer, toNat_trialRandomizer, toNat_zero_randomizer, hsum, hwrap,
    Nat.zero_add, Nat.mod_add_mod]

/-! ## A failed search leaves a failed block -/

/-- **A search that finds nothing caches every trial of its window, with a failing answer.**

It needs the test of each trial to query one point and to read its answer through one map. -/
theorem cached_of_mem_support_findFirst_none {ι R κ β : Type} [DecidableEq ι]
    [SampleableType R] (trial : ℕ → κ) (key : κ → ι) (f : R → Option β)
    (test : κ → OracleComp (unifSpec + (ι →ₒ R)) (Option β))
    (htest : ∀ k, test k = f <$> liftM ((ι →ₒ R).query (key k))) :
    ∀ (n c : ℕ) (cache : (ι →ₒ R).QueryCache),
      ∀ z ∈ support ((simulateQ (ι →ₒ R).romImpl (Wots.findFirst trial test c n)).run cache),
        z.1 = none → ∀ j, c ≤ j → j < c + n →
          ∃ y : R, z.2 (key (trial j)) = some y ∧ f y = none := by
  intro n
  induction n with
  | zero => intro c cache z _ _ j h₁ h₂; omega
  | succ n ih =>
    intro c cache z hz hnone j h₁ h₂
    rw [Wots.run_findFirst_succ_romImpl trial key f test htest, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hcached : w.2 (key (trial c)) = some w.1 := by
      rw [randomOracle.run_eq] at hw
      cases hc : cache (key (trial c)) with
      | some y₀ =>
        rw [hc, support_pure, Set.mem_singleton_iff] at hw
        subst hw
        exact hc
      | none =>
        rw [hc, mem_support_bind_iff] at hw
        obtain ⟨u, -, hw⟩ := hw
        rw [support_pure, Set.mem_singleton_iff] at hw
        subst hw
        exact QueryCache.cacheQuery_self _ _ _
    cases hf : f w.1 with
    | some x =>
      rw [hf, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp at hnone
    | none =>
      rw [hf] at hz
      rcases Nat.eq_or_lt_of_le h₁ with rfl | h
      · exact ⟨w.1, HashSig.le_snd_of_mem_support_run_romImpl _ hz hcached, hf⟩
      · exact ih (c + 1) w.2 z hz hnone j (by omega) (by omega)

/-- A codeword search that finds nothing caches every trial of its window, with a missed answer. -/
theorem cached_of_findCodeword_none (publicParam : PublicParam) (layer : Layer) (e : UInt32)
    (msg : Array UInt64) (base : Randomizer) (C : HashSpec.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (Internal.findCodeword queryH publicParam layer e msg base 0 MAX_RANDOMIZER_TRIALS)).run C))
    (hnone : z.1 = none) (j : ℕ) (hj : j < MAX_RANDOMIZER_TRIALS) :
    -- The answer's type names no trial input, so the kernel never compares two trial inputs.
    ∃ y : HashOutput, z.2 (trialInput publicParam layer e msg base j) = some y ∧ TrialMiss y := by
  rw [Internal.findCodeword_eq] at hz
  exact cached_of_mem_support_findFirst_none (trialRandomizer base) _ _ _
    (codeword_messageDigest_queryH publicParam layer e msg) _ 0 C z hz hnone j (Nat.zero_le _)
    (by omega)

/-- Trial `j` of a block is the trial input of its randomizer `b 2^31 + j`. -/
theorem blockPoint_eq_trialInput (publicParam : PublicParam) (layer : Layer) (e : UInt32)
    (msg : Array UInt64) {b : ℕ} (hb : b < 2 ^ 97) (j : ℕ) :
    blockPoint (publicParam, Address.msg layer e, msg, ⟨b, hb⟩) j =
      trialInput publicParam layer e msg ⟨0, 0⟩ (b * 2 ^ 31 + j) := by
  simp only [blockPoint, trialInput]

/-- Two trials with one randomizer hash one input. -/
theorem trialInput_congr (publicParam : PublicParam) (layer : Layer) (e : UInt32)
    (msg : Array UInt64) {base base' : Randomizer} {c c' : ℕ}
    (h : trialRandomizer base c = trialRandomizer base' c') :
    trialInput publicParam layer e msg base c = trialInput publicParam layer e msg base' c' := by
  simp only [trialInput, h]

/-- A trial of the first `2^31` after `c` is in the window of `2^32`, when `c + 2^31 <= 2^32`. -/
theorem add_lt_max_randomizer_trials {c j : ℕ} (hc : c + 2 ^ 31 ≤ 2 ^ 32) (hj : j < 2 ^ 31) :
    c + j < MAX_RANDOMIZER_TRIALS := by
  have hmax : MAX_RANDOMIZER_TRIALS = 2 ^ 32 := by simp only [MAX_RANDOMIZER_TRIALS]
  omega

/-- A search that finds nothing leaves the block of its window in the cache, all missed. -/
theorem missedBlock_of_findCodeword_none (publicParam : PublicParam) (layer : Layer)
    (e : UInt32) (msg : Array UInt64) (base : Randomizer) (C : HashSpec.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (Internal.findCodeword queryH publicParam layer e msg base 0 MAX_RANDOMIZER_TRIALS)).run C))
    (hnone : z.1 = none) {b c : ℕ} (hb : b < 2 ^ 97) (hc : c + 2 ^ 31 ≤ 2 ^ 32)
    (hwin : ∀ j < 2 ^ 31,
      trialRandomizer base (c + j) = trialRandomizer ⟨0, 0⟩ (b * 2 ^ 31 + j)) :
    ∀ j < 2 ^ 31, ∃ u : HashOutput,
      z.2 (blockPoint (publicParam, Address.msg layer e, msg, ⟨b, hb⟩) j) = some u ∧
        TrialMiss u := by
  intro j hj
  obtain ⟨y, hy, hmiss⟩ := cached_of_findCodeword_none publicParam layer e msg base C hz hnone
    (c + j) (add_lt_max_randomizer_trials hc hj)
  rw [trialInput_congr publicParam layer e msg (hwin j hj)] at hy
  rw [blockPoint_eq_trialInput publicParam layer e msg hb j]
  exact ⟨y, hy, hmiss⟩

/-- A codeword search that finds nothing leaves a block of `2^31` missed trials in the cache. -/
theorem failedSearch_of_findCodeword_none (publicParam : PublicParam) (layer : Layer)
    (e : UInt32) (msg : Array UInt64) (base : Randomizer) (C : HashSpec.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (Internal.findCodeword queryH publicParam layer e msg base 0 MAX_RANDOMIZER_TRIALS)).run C))
    (hnone : z.1 = none) :
    HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) z.2 := by
  obtain ⟨b, hb, c, hc, hwin⟩ := exists_block_of_window base
  exact ⟨(publicParam, Address.msg layer e, msg, ⟨b, hb⟩),
    missedBlock_of_findCodeword_none publicParam layer e msg base C hz hnone hb hc hwin⟩

section Signing

variable (prf : SeedPrf (OracleComp OracleWorld))

/-- A one-time signature that finds no codeword leaves a failed block in the cache. -/
theorem failedSearch_of_otsSignTrials_none (publicParam : PublicParam) (layer : Layer)
    (e : UInt32) (msg : Array UInt64) (C : HashSpec.QueryCache)
    {z : Option (Randomizer × Vector Digest V) × HashSpec.QueryCache}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (Internal.otsSignTrials queryH publicParam prf layer e msg (hashTrials queryH))).run C))
    (hnone : z.1 = none) :
    HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) z.2 := by
  unfold Internal.otsSignTrials at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w, -, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨_ | ⟨rho, x⟩, C'⟩, hv, hz⟩ := hz
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact failedSearch_of_findCodeword_none publicParam layer e msg w.1 w.2 hv rfl
  · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨_, _, _, _, rfl⟩ := hz
    simp at hnone

/-- The top key's signature of a root holds a signature, or leaves a failed block. -/
theorem failedSearch_of_signRootWith (sk : SecretKey) (b : ℕ) (root : Digest)
    (C : HashSpec.QueryCache) {z : Except XmssError LayerSignature × HashSpec.QueryCache}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (Internal.signRootWith queryH prf sk b root (hashTrials queryH))).run C)) :
    z.1.isOk = true ∨ HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) z.2 := by
  unfold Internal.signRootWith at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨_ | ⟨rho, y⟩, C'⟩, hv, hz⟩ := hz
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inr (failedSearch_of_otsSignTrials_none prf _ _ _ _ _ hv rfl)
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl

/-- A built tree holds a top signature, or leaves a failed block. -/
theorem failedSearch_of_cacheTreeWith (sk : SecretKey) (b : ℕ) (C : HashSpec.QueryCache)
    {z : CachedTree × HashSpec.QueryCache}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (Internal.cacheTreeWith queryH prf sk b (hashTrials queryH))).run C)) :
    z.1.top.isOk = true ∨ HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) z.2 := by
  unfold Internal.cacheTreeWith at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w, -, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨v, hv, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact failedSearch_of_signRootWith prf sk b _ _ hv

/-- A fetched tree holds a top signature and the key keeps only such trees, or a block failed.

The key must keep only trees that hold top signatures. -/
theorem failedSearch_of_fetchTreeWith (sk : SecretKey) (hsk : KeptOk sk) (b : ℕ)
    (C : HashSpec.QueryCache) {z : (CachedTree × SecretKey) × HashSpec.QueryCache}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (Internal.fetchTreeWith queryH prf sk b (hashTrials queryH))).run C)) :
    (z.1.1.top.isOk = true ∧ KeptOk z.1.2) ∨
      HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) z.2 := by
  unfold Internal.fetchTreeWith at hz
  split at hz
  · next t ht =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine Or.inl ⟨hsk t (List.mem_of_find?_eq_some ht), fun u hu => ?_⟩
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hsk _ (List.mem_of_find?_eq_some ht)
    · exact hsk u (List.mem_filter.1 hu).1
  · rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨v, hv, hz⟩ := hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rcases failedSearch_of_cacheTreeWith prf sk b C hv with h | h
    · refine Or.inl ⟨h, fun u hu => ?_⟩
      rcases List.mem_cons.1 (List.mem_of_mem_take hu) with rfl | hu
      · exact h
      · exact hsk u hu
    · exact Or.inr h

/-- **A signature succeeds and the key keeps only good trees, or a block of trials failed.**

The key must keep only trees that hold top signatures. -/
theorem failedSearch_of_signWithTrials (sk : SecretKey) (hsk : KeptOk sk) (idx : LeafIndex)
    (msg : Message) (C : HashSpec.QueryCache)
    {z : (Except XmssError Signature × SecretKey) × HashSpec.QueryCache}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (Internal.signWithTrials queryH prf sk idx msg (hashTrials queryH))).run C)) :
    (z.1.1.toOption.isSome = true ∧ KeptOk z.1.2) ∨
      HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) z.2 := by
  unfold Internal.signWithTrials at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨_ | ⟨rho, y⟩, C'⟩, hv, hz⟩ := hz
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inr (failedSearch_of_otsSignTrials_none prf _ _ _ _ _ hv rfl)
  · dsimp only at hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨⟨t, sk'⟩, C''⟩, hw, hz⟩ := hz
    rcases failedSearch_of_fetchTreeWith prf sk hsk _ _ hw with ⟨htop, hkept⟩ | hfs
    · dsimp only at hz htop hkept
      split at hz
      · next top htt =>
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact Or.inl ⟨rfl, hkept⟩
      · next err htt =>
        rw [htt] at htop
        cases htop
    · exact Or.inr (hfs.mono _ _ _ (HashSig.le_snd_of_mem_support_run_romImpl _ hz))

end Signing

/-! ## The game -/

/-- The game's hash over the identity handler is the query of `H`. -/
theorem hashOf_id_eq_queryH : hashOf (QueryImpl.id' OracleWorld) = queryH := by
  funext x
  simp only [hashOf, QueryImpl.id'_apply, queryH, HashSig.queryLanes, HashSig.oracleHash]
  rfl

variable (prf : SeedPrf (OracleComp OracleWorld))

/-- The game's oracles answer a coin or hash query of the adversary by that query. -/
theorem run_failSignerOf_inl {α : Type} (t : OracleWorld.Domain)
    (k : OracleWorld.Range t → OracleComp (OracleWorld + ReasonSigningSpec) α) (sk : SecretKey) :
    ((simulateQ (failSignerOf (QueryImpl.id' OracleWorld) prf)
      (liftM ((OracleWorld + ReasonSigningSpec).query (.inl t)) >>= k)).run sk).run =
      liftM (OracleWorld.query t) >>= fun u =>
        ((simulateQ (failSignerOf (QueryImpl.id' OracleWorld) prf) (k u)).run sk).run := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind',
    failSignerOf, StateT.run_mk, WriterT.run_mk, QueryImpl.id'_apply, bind_map_left]
  simp only [List.nil_append]
  exact bind_congr fun _ => id_map _

/-- The game's oracles answer a signing request by the signer, and log it first. -/
theorem run_failSignerOf_inr {α : Type} (request : SignRequest)
    (k : Except XmssError Signature → OracleComp (OracleWorld + ReasonSigningSpec) α)
    (sk : SecretKey) :
    ((simulateQ (failSignerOf (QueryImpl.id' OracleWorld) prf)
      (liftM ((OracleWorld + ReasonSigningSpec).query (.inr request)) >>= k)).run sk).run =
      Internal.signWithTrials queryH prf sk request.leafIndex request.message
          (hashTrials queryH) >>= fun r =>
        Prod.map id ([⟨request, r.1.toOption⟩] ++ ·) <$>
          ((simulateQ (failSignerOf (QueryImpl.id' OracleWorld) prf) (k r.1)).run r.2).run := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind',
    failSignerOf, StateT.run_mk, WriterT.run_mk, bind_map_left, hashOf_id_eq_queryH]

/-- **A run in which some request fails leaves a failed block in its final cache.**

The key at the start must keep only trees that hold top signatures, and the cache can be any. -/
theorem failedSearch_of_mem_support_run {α : Type}
    (oa : OracleComp (OracleWorld + ReasonSigningSpec) α) (sk : SecretKey)
    (C : HashSpec.QueryCache)
    (x : ((α × SecretKey) × QueryLog SigningSpec) × HashSpec.QueryCache) (hsk : KeptOk sk)
    (hx : x ∈ support ((simulateQ HashSpec.romImpl
      ((simulateQ (failSignerOf (QueryImpl.id' OracleWorld) prf) oa).run sk).run).run C))
    (hfail : ∃ entry ∈ x.1.2, entry.2 = none) :
    HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) x.2 := by
  induction oa using OracleComp.inductionOn generalizing sk C x with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure', support_pure,
      Set.mem_singleton_iff] at hx
    subst hx
    simp at hfail
  | query_bind t k ih =>
    rcases t with t | request
    · rw [run_failSignerOf_inl, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx
      obtain ⟨w, -, hx⟩ := hx
      exact ih w.1 sk w.2 x hsk hx hfail
    · rw [run_failSignerOf_inr, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx
      obtain ⟨w, hw, hx⟩ := hx
      simp only [simulateQ_map, StateT.run_map, support_map] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      rcases failedSearch_of_signWithTrials prf sk hsk _ _ _ hw with ⟨hok, hkept⟩ | hfs
      · obtain ⟨entry, hmem, hnone⟩ := hfail
        have hmem' : entry = ⟨request, w.1.1.toOption⟩ ∨ entry ∈ x'.1.2 := by
          simpa using hmem
        rcases hmem' with rfl | hmem'
        · have hn : w.1.1.toOption = none := hnone
          simp [hn] at hok
        · exact ih w.1.1 w.1.2 w.2 x' hkept hx' ⟨entry, hmem', hnone⟩
      · exact hfs.mono _ _ _ (HashSig.le_snd_of_mem_support_run_romImpl _ hx' : w.2 ≤ x'.2)

/-- Key generation keeps no bottom tree. -/
theorem cache_eq_nil_of_mem_support_keyGenFrom (H : Array UInt64 → OracleComp OracleWorld Lanes4)
    (s : Seed) (C : HashSpec.QueryCache) {z : (PublicKey × SecretKey) × HashSpec.QueryCache}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl (Internal.keyGenFrom H prf s)).run C)) :
    z.1.2.cache = [] := by
  unfold Internal.keyGenFrom at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w, -, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨v, -, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rfl

/-- **A game in which some request fails leaves a failed block in its final cache.**

It holds for any source of the scheme seed and any derivations, from any cache. -/
theorem failedSearch_of_mem_support_failGameOf (seedSrc : OracleComp OracleWorld Seed)
    (prfOf : Seed → SeedPrf (OracleComp OracleWorld)) (adversary : ReasonAdversary)
    (C : HashSpec.QueryCache) (z : FailOutput × HashSpec.QueryCache)
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (failGameOf (QueryImpl.id' OracleWorld) seedSrc prfOf adversary :
        OracleComp OracleWorld FailOutput)).run C))
    (h : SomeFailure z.1) :
    HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) z.2 := by
  unfold failGameOf at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨s, -, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨keys, hkeys, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨⟨⟨forgery, sk'⟩, log⟩, C'⟩, hv, hz⟩ := hz
  dsimp only at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨x, hx, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  -- Key generation keeps no bottom tree, so no error either.
  have hkept : KeptOk keys.1.2 := fun t ht => by
    rw [cache_eq_nil_of_mem_support_keyGenFrom (prfOf s.1) _ _ _ hkeys] at ht
    cases ht
  -- The verification only adds entries to the cache, so the block stays failed.
  exact (failedSearch_of_mem_support_run (prfOf s.1) (adversary.main keys.1.1) keys.1.2 keys.2
    _ hkept hv h).mono _ _ _ (HashSig.le_snd_of_mem_support_run_romImpl _ hx : C' ≤ x.2)

/-- **A game after any draw of the master seed leaves a failed block when some request fails.**

The draw and the hash that derives the scheme seed and the secrets can be any. -/
theorem failedSearch_of_mem_support_sampled
    (sample : OracleComp OracleWorld XmssSecurity.MasterSeed)
    (H : Array UInt64 → OracleComp OracleWorld Lanes4) (adversary : ReasonAdversary)
    (z : FailOutput × HashSpec.QueryCache)
    (hz : z ∈ support ((simulateQ (α := Forgery × QueryLog SigningSpec × Bool) HashSpec.romImpl
      (sample >>= fun s0 => failGameOf (QueryImpl.id' OracleWorld) (schemeSeed H (ofSeed s0))
        (seedPrf H) adversary : OracleComp OracleWorld FailOutput)).run ∅))
    (h : SomeFailure z.1) :
    HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) z.2 := by
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w, -, hz⟩ := hz
  exact failedSearch_of_mem_support_failGameOf _ _ adversary w.2 z hz h

/-- A run of the game in which some request fails leaves a failed block in its final cache. -/
theorem failedSearch_of_mem_support_reasonRun (adversary : ReasonAdversary)
    (z : FailOutput × HashSpec.QueryCache)
    (hz : z ∈ support ((simulateQ HashSpec.romImpl (reasonRun adversary)).run ∅))
    (h : SomeFailure z.1) :
    HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) z.2 := by
  -- The run must match the next lemma's hypothesis term for term, or the kernel replays the game.
  rw [reasonRun_eq_failGameOf] at hz
  exact failedSearch_of_mem_support_sampled _ _ adversary z hz h

/-- The game makes at most `Q` hash calls, for `qH` hash queries and `r` requests. -/
theorem isQueryBoundP_reasonRun (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    IsQueryBoundP (reasonRun adversary) (SufCma.IsHashCall HashSpec) (gameQueries qH r) := by
  have hhash : ∀ x,
      IsQueryBoundP (QueryImpl.id' OracleWorld (.inr x)) (SufCma.IsHashCall HashSpec) 1 :=
    fun x => by simp [SufCma.IsHashCall]
  have hH := isQueryBoundP_hashOf hhash
  rw [reasonRun_eq_failGameOf]
  exact (isQueryBoundP_bind (isQueryBoundP_liftM_prob _) fun _ _ =>
    isQueryBoundP_failGameOf (fun n => by simp [SufCma.IsHashCall]) hhash
      (Cost.isQueryBoundP_schemeSeed hH _) (Cost.isQueryBoundP_seedPrf hH)
      adversary hh hr).mono (le_of_eq (Nat.zero_add _))

/-! ## The bounds -/

/-- **A run of at most `n` hash calls leaves a failed block with chance `<= n (1 - p)^(2^31)`.**

The run starts from an empty cache.

A failed block is one whose `2^31` trials all missed the code in the final cache.

`p = |C| / 2^128` is the chance that one trial gives a codeword. -/
theorem prEvent_failedBlock_le {α : Type} (oa : OracleComp OracleWorld α) {n : ℕ}
    (hn : IsQueryBoundP oa (SufCma.IsHashCall HashSpec) n) :
    Pr{let z ← (simulateQ HashSpec.romImpl oa).run ∅}[
        HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) z.2] ≤
      (n : ℝ≥0∞) * (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128) ^ (2 ^ 31) := by
  have hcalls := (hashQueryBound_iff_counted oa).1
    (XmssSecurity.hashQueryBound_of_isQueryBoundP oa hn ∅)
  simp only [SufCma.countedRunIn, SufCma.randomOracleModel] at hcalls
  rw [← prEvent_trialMiss]
  refine HashSig.prEvent_failedSearch_le blockPoint TrialMiss (2 ^ 31) (by norm_num)
    (fun p p' j j' hj hj' h => blockPoint_inj p p' j j' hj hj' h) _ ?_ oa n hcalls
  exact fun _ => le_rfl

/-- `2^31` trials all miss the code with probability at most `exp(-2000)`, if one trial is uniform.

All `2^32` trials miss with probability at most `exp(-4000)`, and this is its square root. -/
theorem block_trials_fail_probability :
    (1 - (CODE_SIZE : ℝ) / 2 ^ 128) ^ (2 ^ 31) ≤ Real.exp (-2000) := by
  have hp : 0 ≤ 1 - (CODE_SIZE : ℝ) / 2 ^ 128 := by norm_num [CODE_SIZE]
  have hall := all_trials_fail_probability
  -- The `2^32` trials are two runs of `2^31`, and `exp(-4000)` is `exp(-2000)` squared.
  have hmax : MAX_RANDOMIZER_TRIALS = 2 ^ 31 * 2 := by
    simp only [MAX_RANDOMIZER_TRIALS]
    norm_num
  have hexp : Real.exp (-4000) = Real.exp (-2000) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hmax, pow_mul, hexp] at hall
  exact (pow_le_pow_iff_left₀ (pow_nonneg hp _) (Real.exp_pos _).le two_ne_zero).1 hall

/-- All `2^31` uniform trials of a block miss the code with probability at most `exp(-2000)`. -/
theorem trialMiss_pow_le_exp :
    (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128) ^ (2 ^ 31) ≤
      ENNReal.ofReal (Real.exp (-2000)) := by
  rw [HashSig.ofReal_one_sub_div _ _ (by simp [CODE_SIZE]),
    ← ENNReal.ofReal_pow (by norm_num [CODE_SIZE])]
  exact ENNReal.ofReal_le_ofReal block_trials_fail_probability

/-- **Some request of the game fails with probability `<= Q (1 - p)^(2^31)`.**

It needs an adversary that makes at most `qH` hash queries and `r` signing requests.

Let `Q` be the bound on the hash calls of the game, for `qH` and `r`.

`p = |C| / 2^128` is the chance that one trial gives a codeword, about `2^-20.0045`. -/
theorem signingFailure_le_pow (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    signingFailure adversary ≤
      (gameQueries qH r : ℝ≥0∞) * (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128) ^ (2 ^ 31) := by
  have hrom : XmssSecurity.romImpl = HashSpec.romImpl := rfl
  calc signingFailure adversary
      = Pr{let x ← (simulateQ HashSpec.romImpl (reasonRun adversary)).run' ∅}[
          SomeFailure x] := by
        -- Rewrite with the model's lemma on any game, or the kernel replay runs the game.
        refine (SufCma.prEvent_countedRunIn _ (reasonRun adversary) SomeFailure).trans ?_
        rw [run_randomOracleModel, hrom]
    _ = Pr{let z ← (simulateQ HashSpec.romImpl (reasonRun adversary)).run ∅}[
          SomeFailure z.1] := by
        rw [StateT.run'_eq, prEvent_map]
    -- A run with a failed request ends with a failed block in its cache.
    _ ≤ Pr{let z ← (simulateQ HashSpec.romImpl (reasonRun adversary)).run ∅}[
          HashSig.FailedSearch blockPoint TrialMiss (2 ^ 31) z.2] :=
        prEvent_mono_of_support _ _ _ fun z hz h =>
          failedSearch_of_mem_support_reasonRun adversary z hz h
    -- The game makes at most `Q` hash calls.
    _ ≤ _ := prEvent_failedBlock_le _ (isQueryBoundP_reasonRun adversary hh hr)

/-- Some request of the game fails with probability at most `Q exp(-2000)`.

It needs an adversary that makes at most `qH` hash queries and `r` signing requests.

Let `Q` be the bound on the hash calls of the game, for `qH` and `r`. -/
theorem signingFailure_le_exp (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    signingFailure adversary ≤ (gameQueries qH r : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2000)) := by
  refine (signingFailure_le_pow adversary hh hr).trans ?_
  gcongr
  exact trialMiss_pow_le_exp

/-- **leanXMSS with a signer that reveals its reasons, with a failure term linear in `Q`.**

It needs the adversary's reduction to the unforgeability game to make at most `q >= 1` hash calls.

It also needs at most `qH` hash queries and `r` requests, which bound the game's hash calls by `Q`.

The adversary then forges with probability at most `q / 2^127 + Q exp(-2000)`. -/
theorem reasonForgeAdvantage_le_exp (q : ℕ) (hq : 1 ≤ q) (adversary : ReasonAdversary)
    (hbound : SufCma.IsGameQueryBound scheme (SufCma.randomOracleModel HashSpec)
      (hideReasons adversary) q) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    reasonForgeAdvantage adversary ≤
      q / ((2 ^ 127 : ℕ) : ℝ≥0∞) + (gameQueries qH r : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2000)) :=
  (reasonForgeAdvantage_le_add q hq adversary hbound).trans
    (add_le_add_right (signingFailure_le_exp adversary hh hr) _)

end EthLib.Cryptography.Xmss.Unforgeability

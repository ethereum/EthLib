module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.SeedHops
public import EthLib.Cryptography.Proofs.Xmss.CodewordSearch
public import EthLib.Cryptography.Proofs.Xmss.Address
public import EthLib.Cryptography.Proofs.QueryAvoidance
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.IdealBase

/-!
# Proofs: one signing request in the ideal game of the derivations

In the second hop's ideal game, each derivation is drawn from a lazy table on its first use.

A request runs two codeword searches, one per layer.

A search reads its randomizer base from the table, at the parameter, its address and the message.

- A new search draws its base when it runs.
  A cached input is a trial input of at most `2^32` of the `2^128` bases.
  So with at most `Q` cached inputs, some trial is already cached with chance `<= Q / 2^96`.
  The count takes the whole cache, not only the inputs at the key's message address.
  Otherwise every trial is fresh, and all fail with probability at most `exp(-4000)`.
- A repeated search reads the base of an earlier search.
  When that search succeeded, the cache holds a trial with a codeword digest.
  So the repeat succeeds too.

When every earlier search succeeded, a request fails with chance `<= Q / 2^95 + 2 exp(-4000)`.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open XmssSecurity (OracleWorld HashSpec HashOutput HashInput)

/-- The state of the ideal game: the hash cache and the table of derivations. -/
abbrev IdealState := SecretEncoding.SplitCache HashSpec PrfInput HashOutput

/-- The hash of the second hop's game. -/
abbrev hashD : ByteArray → OracleComp PrfSpec (Vector UInt8 32) :=
  hashOf (HashSpec.withDerivationsLift PrfInput HashOutput)

/-- One signing request of the second hop's game: the parameter, then the signature. -/
def requestD (request : SignRequest) : OracleComp PrfSpec (Except XmssError Signature) := do
  let pp ← publicParamOf prfD
  signDerived hashD prfD pp request.leafIndex request.message

/-- The hash input of trial `j` of a search of key `e` on `layer`, from the base `base`. -/
def trialInput (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (j : ℕ) : HashInput :=
  (thInput pp (addrMsg layer e) (msg ++ packBytes (trialRandomizer base j))).data.toList

/-- Every search with a base in the table found a codeword.

Some trial in its window is cached, and its digest is a codeword. -/
def SearchesFound (st : IdealState) : Prop :=
  ∀ pp layer e msg u, st.2 (pp, addrRnd layer e, msg) = some u →
    ∃ j < MAX_RANDOMIZER_TRIALS, ∃ y,
      st.1 (trialInput pp layer e msg (halfOf 0 (ofOutput u)) j) = some y ∧
        (codeword? (halfOf 0 (ofOutput y))).isSome

/-! ## Steps that keep every search found -/

/-- A derivation query at the address of a randomizer base. -/
def IsRndQuery : PrfSpec.Domain → Prop
  | .inr x => ∃ layer e, x.2.1 = addrRnd layer e
  | _ => False

noncomputable instance : DecidablePred IsRndQuery := Classical.decPred _

/-- A state whose cache grows and whose bases stay keeps every search found. -/
theorem SearchesFound.mono {st st' : IdealState} (hst : SearchesFound st) (hC : st.1 ≤ st'.1)
    (hT : ∀ pp layer e msg, st'.2 (pp, addrRnd layer e, msg) = st.2 (pp, addrRnd layer e, msg)) :
    SearchesFound st' := by
  intro pp layer e msg u hu
  rw [hT] at hu
  obtain ⟨j, hj, y, hy, hcw⟩ := hst pp layer e msg u hu
  exact ⟨j, hj, y, hC hy, hcw⟩

/-- A step that draws no base keeps every search found. -/
theorem SearchesFound.of_mem_support_idealImpl {t : PrfSpec.Domain} (ht : ¬IsRndQuery t)
    {st : IdealState} (hst : SearchesFound st)
    {w : PrfSpec.Range t × IdealState}
    (hw : w ∈ support ((SecretEncoding.idealImpl HashSpec PrfInput HashOutput t).run st)) :
    SearchesFound w.2 := by
  obtain ⟨hC, hT⟩ := le_of_mem_support_idealImpl hw
  refine hst.mono hC fun pp layer e msg => ?_
  cases h : st.2 (pp, addrRnd layer e, msg) with
  | some v => exact hT h
  | none =>
    have hiff :=
      SecretEncoding.isSome_snd_apply_iff_of_mem_support_idealImpl hw (pp, addrRnd layer e, msg)
    rw [h] at hiff
    refine Option.not_isSome_iff_eq_none.mp fun hs => ?_
    rcases hiff.mp hs with hs | rfl
    · exact Bool.false_ne_true hs
    · exact ht ⟨layer, e, rfl⟩

/-- A run that draws no base keeps every search found. -/
theorem SearchesFound.of_mem_support_run {α : Type} {oa : OracleComp PrfSpec α}
    (h : oa.AllQueriesSatisfy fun t => ¬IsRndQuery t) {st : IdealState} (hst : SearchesFound st)
    {z : α × IdealState}
    (hz : z ∈ support ((simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput) oa).run
      st)) :
    SearchesFound z.2 :=
  h.holds_of_mem_support_run_simulateQ SearchesFound
    (fun _ ht _ hs _ hw => hs.of_mem_support_idealImpl ht hw) hst hz

/-! ## Bounds on the failures of a run -/

/-- From every state whose searches found codewords, a run fails with probability at most `ε`.

A run fails when its output fails, or when it leaves a search that found none.

Only the runs whose cache ends with at most `Q` entries count. -/
def FailsAtMost {α : Type} (fail : α → Prop) (Q : ℕ) (ε : ℝ≥0∞)
    (oa : OracleComp PrfSpec α) : Prop :=
  ∀ st, SearchesFound st →
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput) oa).run st}[
      (fail z.1 ∨ ¬SearchesFound z.2) ∧ z.2.1.enncard ≤ Q] ≤ ε

namespace FailsAtMost

variable {α β : Type} {fail : α → Prop} {Q : ℕ} {ε ε' : ℝ≥0∞} {oa : OracleComp PrfSpec α}

/-- A larger bound still holds. -/
theorem mono_bound (h : FailsAtMost fail Q ε oa) (hε : ε ≤ ε') : FailsAtMost fail Q ε' oa :=
  fun st hst => (h st hst).trans hε

/-- A smaller failure still has the bound. -/
theorem mono_fail {fail' : α → Prop} (h : FailsAtMost fail Q ε oa)
    (hf : ∀ a, fail' a → fail a) : FailsAtMost fail' Q ε oa :=
  fun st hst => (prEvent_mono _ _ _ fun _ hz => ⟨hz.1.imp_left (hf _), hz.2⟩).trans (h st hst)

/-- **The failures of two steps add up.**

The first step fails with probability at most `ε₁`.

After every output where it does not fail, the second fails with probability at most `ε₂`. -/
theorem bind {failA : α → Prop} {failB : β → Prop} {ε₁ ε₂ : ℝ≥0∞}
    {f : α → OracleComp PrfSpec β} (hA : FailsAtMost failA Q ε₁ oa)
    (hB : ∀ a, ¬failA a → FailsAtMost failB Q ε₂ (f a)) :
    FailsAtMost failB Q (ε₁ + ε₂) (oa >>= f) := by
  intro st hst
  rw [simulateQ_bind, StateT.run_bind]
  refine (prEvent_bind_le_prEvent_add_of_support _ _ _ _ fun z _ hz => ?_).trans
    (add_le_add (hA st hst) le_rfl)
  by_cases hQ : z.2.1.enncard ≤ Q
  · have hz' : ¬failA z.1 ∧ SearchesFound z.2 := by tauto
    exact hB z.1 hz'.1 z.2 hz'.2
  · refine le_of_eq_of_le ?_ zero_le
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun y hy hE => hQ ?_
    exact (QueryCache.enncard_mono (le_of_mem_support_run_idealImpl _ hy).1).trans hE.2

/-- A run that draws no base never fails, when no output counts as a failure. -/
theorem of_allQueriesSatisfy (h : oa.AllQueriesSatisfy fun t => ¬IsRndQuery t) :
    FailsAtMost (fun _ => False) Q 0 oa := by
  intro st hst
  refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hE => ?_)
  rcases hE.1 with hf | hs
  · exact hf
  · exact hs (SearchesFound.of_mem_support_run h hst hz)

/-- Returning an output that does not fail never fails. -/
theorem pure {a : α} (ha : ¬fail a) : FailsAtMost fail Q 0 (pure a) := by
  intro st hst
  refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hE => ?_)
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rcases hE.1 with hf | hs
  · exact ha hf
  · exact hs hst

end FailsAtMost

/-! ## The search, over the public hash -/

/-- The hash of the second hop's game is the query of `H`, lifted. -/
theorem simulateQ_queryH (x : ByteArray) :
    simulateQ (HashSpec.withDerivationsLift PrfInput HashOutput)
      (queryH x : OracleComp OracleWorld (Vector UInt8 32)) = hashD x := by
  simp [queryH, hashOf, HashSig.oracleHash]
  rfl

/-- The search of the second hop's game is the search over `H`, lifted. -/
theorem simulateQ_findCodeword (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : ℕ) :
    simulateQ (HashSpec.withDerivationsLift PrfInput HashOutput)
      (Internal.findCodeword queryH pp layer e msg base c fuel :
        OracleComp OracleWorld _) =
      Internal.findCodeword hashD pp layer e msg base c fuel := by
  rw [findCodeword_map_monad (simulateQ (HashSpec.withDerivationsLift PrfInput HashOutput))
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f) _
    (fun f x => simulateQ_map _ x f)]
  simp only [simulateQ_queryH]

/-- In the ideal game, the search runs as over the random oracle, and keeps the table. -/
theorem run_findCodeword_idealImpl (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (c fuel : ℕ) (C : HashSpec.QueryCache)
    (T : (PrfInput →ₒ HashOutput).QueryCache) :
    (simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput)
        (Internal.findCodeword hashD pp layer e msg base c fuel)).run (C, T) =
      (fun z => (z.1, (z.2, T))) <$> (simulateQ HashSpec.romImpl
        (Internal.findCodeword queryH pp layer e msg base c fuel)).run C := by
  rw [← simulateQ_findCodeword, run_simulateQ_idealImpl_withDerivationsLift]

/-- A trial of the search over `H` is one query, whose answer's digest is tested. -/
theorem codeword_messageDigest_queryH (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (rho : Randomizer) :
    (codeword? <$> messageDigest queryH pp layer e msg rho : OracleComp OracleWorld _) =
      (fun u => codeword? (halfOf 0 (ofOutput u))) <$>
        liftM (HashSpec.query
          (thInput pp (addrMsg layer e) (msg ++ packBytes rho)).data.toList) := by
  simp only [messageDigest, th, queryH, XmssSecurity.Concrete.oracleHash,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rfl

/-- A search whose window holds a cached trial with a codeword digest finds a trial. -/
theorem isSome_of_mem_support_findCodeword (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (C : HashSpec.QueryCache)
    (h : ∃ j < MAX_RANDOMIZER_TRIALS, ∃ y,
      C (trialInput pp layer e msg base j) = some y ∧ (codeword? (halfOf 0 (ofOutput y))).isSome)
    {z} (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (Internal.findCodeword queryH pp layer e msg base 0 MAX_RANDOMIZER_TRIALS)).run C)) :
    z.1.isSome := by
  obtain ⟨j, hj, y, hy, hcw⟩ := h
  exact Wots.isSome_of_mem_support_findFirst_romImpl (trialRandomizer base) _ _ _
    (codeword_messageDigest_queryH pp layer e msg) _ 0 C
    ⟨j, Nat.zero_le _, by omega, y, hy, hcw⟩ z hz

/-- The trial a search finds is in its window, and cached with a codeword digest. -/
theorem exists_cached_of_mem_support_findCodeword (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (C : HashSpec.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (Internal.findCodeword queryH pp layer e msg base 0 MAX_RANDOMIZER_TRIALS)).run C))
    {rho x} (hx : z.1 = some (rho, x)) :
    ∃ j < MAX_RANDOMIZER_TRIALS, ∃ y,
      z.2 (trialInput pp layer e msg base j) = some y ∧
        codeword? (halfOf 0 (ofOutput y)) = some x := by
  obtain ⟨j, -, hj, rfl, y, hy, hcw⟩ := Wots.exists_cached_of_mem_support_findFirst_romImpl
    (trialRandomizer base) _ _ _ (codeword_messageDigest_queryH pp layer e msg) _ 0 C z hz rho x hx
  exact ⟨j, by omega, y, hy, hcw⟩

/-! ## A new base rarely meets the cache -/

/-- A trial and its randomizer fix the base. -/
theorem trialRandomizer_inj_base {base base' : Randomizer} {j : ℕ}
    (h : trialRandomizer base j = trialRandomizer base' j) : base = base' := by
  have hb : bytesToUint base < 2 ^ 128 :=
    lt_of_lt_of_eq (Base.bytesToUint_lt base) (by simp [RANDOMIZER_LEN])
  have hb' : bytesToUint base' < 2 ^ 128 :=
    lt_of_lt_of_eq (Base.bytesToUint_lt base') (by simp [RANDOMIZER_LEN])
  have hmod := Base.uintToBytes_inj (k := RANDOMIZER_LEN)
    (lt_of_lt_of_eq (Nat.mod_lt _ (by norm_num)) (by simp [RANDOMIZER_LEN]))
    (lt_of_lt_of_eq (Nat.mod_lt _ (by norm_num)) (by simp [RANDOMIZER_LEN])) h
  have heq : bytesToUint base = bytesToUint base' := by omega
  rw [← Base.uintToBytes_bytesToUint base, ← Base.uintToBytes_bytesToUint base', heq]

/-- The hash input of a trial fixes the base. -/
theorem trialInput_injective_base (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (j : ℕ) : Function.Injective fun base => trialInput pp layer e msg base j := by
  intro base base' h
  have hin := (thInput_inj (ByteArray.ext (Array.toList_inj.mp h))).2.2
  exact trialRandomizer_inj_base (packBytes_injective (HashSig.byteArray_append_inj hin rfl).2)

/-- The digests whose image under an injective map is cached are at most the cache's size. -/
theorem natCard_isSome_le_enncard (C : HashSpec.QueryCache) {g : Digest → HashInput}
    (hg : Function.Injective g) : (Nat.card {d // (C (g d)).isSome} : ℝ≥0∞) ≤ C.enncard := by
  set S : Set Digest := {d | (C (g d)).isSome}
  have hcard : (Nat.card {d // (C (g d)).isSome} : ℝ≥0∞) = ((g '' S).encard : ℝ≥0∞) := by
    rw [hg.injOn.encard_image, ← (Set.toFinite S).cast_ncard_eq, ← Nat.card_coe_set_eq]
    rfl
  rw [hcard]
  exact QueryCache.encard_le_enncard _ fun _ ⟨_, hd, h⟩ => h ▸ hd

/-- **A uniform base puts some trial in the cache with probability at most `2^32 |C| / 2^128`.** -/
theorem prEvent_trial_cached_le (C : HashSpec.QueryCache) (pp : PublicParam) (layer : Layer)
    (e : UInt32) (msg : ByteArray) :
    Pr{let u ← $ᵗ HashOutput}[∃ j < MAX_RANDOMIZER_TRIALS,
      (C (trialInput pp layer e msg (halfOf 0 (ofOutput u)) j)).isSome] ≤
      2 ^ 32 * (C.enncard / 2 ^ 128) := by
  have h := prEvent_exists_finset_le_card_mul (Finset.range MAX_RANDOMIZER_TRIALS)
    ($ᵗ HashOutput) (fun j u => (C (trialInput pp layer e msg (halfOf 0 (ofOutput u)) j)).isSome)
    (ε := C.enncard / 2 ^ 128) fun j _ => by
      rw [prEvent_halfOf_ofOutput (fun d => (C (trialInput pp layer e msg d j)).isSome)]
      exact ENNReal.div_le_div_right
        (natCard_isSome_le_enncard C (trialInput_injective_base pp layer e msg j)) _
  refine (le_trans (prEvent_mono _ _ _ fun u ⟨j, hj, hc⟩ => ⟨j, Finset.mem_range.2 hj, hc⟩) h).trans
    (le_of_eq ?_)
  rw [Finset.card_range, MAX_RANDOMIZER_TRIALS, Nat.cast_pow, Nat.cast_ofNat]

/-! ## One search -/

/-- A derivation already in the table is read from it. -/
theorem run_prfD_of_some {pp : PublicParam} {a : Address} {s : ByteArray} {st : IdealState}
    {u : HashOutput} (h : st.2 (pp, a, s) = some u) :
    (simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput) (prfD pp a s)).run st =
      pure (ofOutput u, st) := by
  simp [prfD, SecretEncoding.idealImpl_run_derive_some h]

/-- A derivation not yet in the table is drawn uniformly and stored. -/
theorem run_prfD_of_none {pp : PublicParam} {a : Address} {s : ByteArray} {st : IdealState}
    (h : st.2 (pp, a, s) = none) :
    (simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput) (prfD pp a s)).run st =
      (fun u => (ofOutput u, (st.1, st.2.cacheQuery (pp, a, s) u))) <$> ($ᵗ HashOutput) := by
  simp [prfD, SecretEncoding.idealImpl_run_derive_none h]

/-- A search draws or reads its base, then runs the codeword search from it. -/
theorem run_search (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (st : IdealState) :
    (simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput)
        (randomizerBase pp prfD layer e msg >>= fun base =>
          Internal.findCodeword hashD pp layer e msg base 0 MAX_RANDOMIZER_TRIALS)).run st =
      (simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput)
          (prfD pp (addrRnd layer e) msg)).run st >>= fun w =>
        (simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput)
          (Internal.findCodeword hashD pp layer e msg (id (halfOf 0 w.1)) 0
            MAX_RANDOMIZER_TRIALS)).run w.2 := by
  -- `id` types the digest as a randomizer, so the rewritten term stays well typed.
  have h : randomizerBase pp prfD layer e msg =
      prfD pp (addrRnd layer e) msg >>= fun u => pure (id (halfOf 0 u) : Randomizer) := rfl
  rw [h, bind_assoc]
  simp only [pure_bind, simulateQ_bind, StateT.run_bind]

/-- `2^a` times `Q / 2^(a + b)` is `Q / 2^b`. -/
theorem two_pow_mul_div_two_pow (a b : ℕ) (Q : ℝ≥0∞) : 2 ^ a * (Q / 2 ^ (a + b)) = Q / 2 ^ b := by
  rw [pow_add, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), ← mul_assoc, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-- **One search fails with probability at most `Q / 2^96 + exp(-4000)`.**

A repeated search finds the cached trial of the earlier one, so it never fails.

A new search meets the cache with probability at most `Q / 2^96`.

Otherwise its trials are fresh, and all fail with probability at most `exp(-4000)`. -/
theorem failsAtMost_search (Q : ℕ) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) :
    FailsAtMost (fun r => r = none) Q ((Q : ℝ≥0∞) / 2 ^ 96 + ENNReal.ofReal (Real.exp (-4000)))
      (randomizerBase pp prfD layer e msg >>= fun base =>
        Internal.findCodeword hashD pp layer e msg base 0 MAX_RANDOMIZER_TRIALS) := by
  rintro ⟨C, T⟩ hst
  rw [run_search]
  cases hT : T (pp, addrRnd layer e, msg) with
  | some u =>
    rw [run_prfD_of_some hT, pure_bind]
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hE => ?_) zero_le
    have hC := (le_of_mem_support_run_idealImpl _ hz).1
    rw [run_findCodeword_idealImpl, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rcases hE.1 with hnone | hs
    · obtain ⟨j, hj, y, hy, hcw⟩ := hst pp layer e msg u hT
      have hsome := isSome_of_mem_support_findCodeword pp layer e msg _ C ⟨j, hj, y, hy, hcw⟩ hw
      simp only at hnone
      simp [hnone] at hsome
    · exact hs (hst.mono hC fun _ _ _ _ => rfl)
  | none =>
    rw [run_prfD_of_none hT, bind_map_left]
    by_cases hQ : C.enncard ≤ Q
    · refine (prEvent_bind_le_prEvent_add _ _ (fun u => ∃ j < MAX_RANDOMIZER_TRIALS,
        (C (trialInput pp layer e msg (halfOf 0 (ofOutput u)) j)).isSome) _
        fun u hu => ?_).trans (add_le_add ?_ le_rfl)
      · -- A search that finds a trial leaves it cached, so a failure returns nothing.
        refine (prEvent_mono_of_support _ _ (fun z => z.1 = none) fun z hz hE => ?_).trans ?_
        · have hC := (le_of_mem_support_run_idealImpl _ hz).1
          rw [run_findCodeword_idealImpl, support_map] at hz
          obtain ⟨w, hw, rfl⟩ := hz
          cases hw1 : w.1 with
          | none => rfl
          | some r =>
            exfalso
            rcases hE.1 with hnone | hs
            · simp [hw1] at hnone
            refine hs fun pp' layer' e' msg' u' hu' => ?_
            by_cases hx : (pp', addrRnd layer' e', msg') = (pp, addrRnd layer e, msg)
            · simp only [Prod.mk.injEq, addrRnd_inj] at hx
              obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hx
              subst h1 h2 h3 h4
              simp only [QueryCache.cacheQuery_self, Option.some_inj] at hu'
              subst hu'
              obtain ⟨j, hj, y, hy, hcw⟩ :=
                exists_cached_of_mem_support_findCodeword pp' layer' e' msg' _ C hw hw1
              exact ⟨j, hj, y, hy, by simp [hcw]⟩
            · rw [QueryCache.cacheQuery_of_ne _ _ hx] at hu'
              obtain ⟨j, hj, y, hy, hcw⟩ := hst pp' layer' e' msg' u' hu'
              exact ⟨j, hj, y, hC hy, hcw⟩
        · rw [run_findCodeword_idealImpl, prEvent_map]
          refine le_of_eq_of_le ?_ (prEvent_findCodeword_none_le pp layer e msg _ C fun j hj =>
            Option.not_isSome_iff_eq_none.mp fun hs => hu ⟨j, hj, hs⟩)
          rw [StateT.run'_eq, prEvent_map]
          rfl
      · exact (prEvent_trial_cached_le C pp layer e msg).trans (by
          rw [← two_pow_mul_div_two_pow 32 96]
          exact mul_le_mul_right (ENNReal.div_le_div_right hQ _) _)
    · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hE => hQ ?_)
        zero_le
      rw [mem_support_bind_iff] at hz
      obtain ⟨u, -, hz⟩ := hz
      exact (QueryCache.enncard_mono (le_of_mem_support_run_idealImpl _ hz).1).trans hE.2

/-! ## The steps that draw no base -/

section NoBase

/-- A run that makes no query at a base's address draws no base. -/
theorem allQueriesSatisfy_of_isQueryBoundP {α : Type} {oa : OracleComp PrfSpec α}
    (h : IsQueryBoundP oa IsRndQuery 0) : oa.AllQueriesSatisfy fun t => ¬IsRndQuery t :=
  (isQueryBoundP_zero_iff oa _).1 ((isQueryBoundP_congr_pred fun _ => not_not.symm).1 h)

/-- A hash call draws no base. -/
theorem isQueryBoundP_hashD (x : ByteArray) : IsQueryBoundP (hashD x) IsRndQuery 0 :=
  (isQueryBoundP_map_iff _ _ _).2 (by simp [IsRndQuery, OracleSpec.withDerivationsLift])

/-- A derivation away from every base's address draws no base. -/
theorem isQueryBoundP_prfD {pp : PublicParam} {a : Address} {s : ByteArray}
    (ha : ∀ layer e, a ≠ addrRnd layer e) : IsQueryBoundP (prfD pp a s) IsRndQuery 0 :=
  (isQueryBoundP_map_iff _ _ _).2 (by
    simp only [isQueryBoundP_query_iff, IsRndQuery]
    simp [ha])

/-- A chain start's address is not a base's address. -/
theorem addrPrf_ne_addrRnd (layer : Layer) (e : UInt32) (j : Fin (V / 2)) (layer' : Layer)
    (e' : UInt32) : addrPrf layer e j ≠ addrRnd layer' e' :=
  encodeAddress_ne_of_type_ne _ _ _ _ _ _ (by decide)

/-- The parameter's address is not a base's address. -/
theorem addrParam_ne_addrRnd (layer : Layer) (e : UInt32) : addrParam ≠ addrRnd layer e :=
  encodeAddress_ne_of_type_ne _ _ _ _ _ _ (by decide)

/-- A tweakable hash call draws no base. -/
theorem isQueryBoundP_th (pp : PublicParam) (a : Address) (payload : ByteArray) :
    IsQueryBoundP (th hashD pp a payload) IsRndQuery 0 :=
  isQueryBoundP_bind_zero _ _ (isQueryBoundP_hashD _) fun _ => isQueryBoundP_pure _ _ _

/-- The chain starts of a key draw no base. -/
theorem isQueryBoundP_chainStarts (pp : PublicParam) (layer : Layer) (e : UInt32) :
    IsQueryBoundP (chainStarts pp prfD layer e) IsRndQuery 0 :=
  isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun j =>
    isQueryBoundP_prfD (addrPrf_ne_addrRnd layer e j)) fun _ => isQueryBoundP_pure _ _ _

/-- A walk on a chain draws no base. -/
theorem isQueryBoundP_chain (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (start steps : ℕ) (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    IsQueryBoundP (chain hashD pp layer e i start steps h value) IsRndQuery 0 :=
  chain_isQueryBoundP_zero _ (fun _ _ => isQueryBoundP_th _ _ _) _ _ _ _

/-- The leaf of a key draws no base. -/
theorem isQueryBoundP_otsPublicLeaf (pp : PublicParam) (layer : Layer) (e : UInt32) :
    IsQueryBoundP (otsPublicLeaf hashD pp prfD layer e) IsRndQuery 0 :=
  isQueryBoundP_bind_zero _ _ (isQueryBoundP_chainStarts pp layer e) fun _ =>
    isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
      isQueryBoundP_chain _ _ _ _ _ _ _ _) fun _ => isQueryBoundP_th _ _ _

/-- A node of a tree draws no base. -/
theorem isQueryBoundP_node (pp : PublicParam) (layer : Layer) (level j : ℕ) :
    IsQueryBoundP (node hashD pp prfD layer level j) IsRndQuery 0 :=
  merkleNode_isQueryBoundP_zero _ _ (fun _ => isQueryBoundP_otsPublicLeaf _ _ _)
    (fun _ _ _ _ => isQueryBoundP_th _ _ _) level j

/-- The path of a key draws no base. -/
theorem isQueryBoundP_path (pp : PublicParam) (layer : Layer) (e : ℕ) :
    IsQueryBoundP (path hashD pp prfD layer e) IsRndQuery 0 :=
  merkleSiblings_isQueryBoundP_zero _ _ (fun _ => isQueryBoundP_otsPublicLeaf _ _ _)
    (fun _ _ _ _ => isQueryBoundP_th _ _ _) _ _ _

/-- The public parameter draws no base. -/
theorem isQueryBoundP_publicParamOf : IsQueryBoundP (publicParamOf prfD) IsRndQuery 0 :=
  isQueryBoundP_bind_zero _ _ (isQueryBoundP_prfD (addrParam_ne_addrRnd)) fun _ =>
    isQueryBoundP_pure _ _ _

end NoBase

/-! ## The layers and the request -/

section Request

-- Unfolding the tree height would build the whole tree when a bound is checked.
attribute [local irreducible] LAYER_HEIGHT

/-- A prefix that draws no base adds nothing to the bound. -/
theorem FailsAtMost.bind_of_noBase {α β : Type} {fail : β → Prop} {Q : ℕ} {ε : ℝ≥0∞}
    {oa : OracleComp PrfSpec α} {f : α → OracleComp PrfSpec β}
    (h : IsQueryBoundP oa IsRndQuery 0) (hf : ∀ a, FailsAtMost fail Q ε (f a)) :
    FailsAtMost fail Q ε (oa >>= f) := by
  simpa using FailsAtMost.bind
    (FailsAtMost.of_allQueriesSatisfy (Q := Q) (allQueriesSatisfy_of_isQueryBoundP h))
    fun a _ => hf a

/-- A one-time signature fails as its search does. -/
theorem failsAtMost_otsSign (Q : ℕ) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) :
    FailsAtMost (fun r => r = none) Q ((Q : ℝ≥0∞) / 2 ^ 96 + ENNReal.ofReal (Real.exp (-4000)))
      (otsSign hashD pp prfD layer e msg) := by
  unfold otsSign
  rw [← bind_assoc]
  refine (FailsAtMost.bind (ε₂ := 0) (failsAtMost_search Q pp layer e msg)
    fun r hr => ?_).mono_bound (add_zero _).le
  rcases r with _ | ⟨rho, x⟩
  · exact absurd rfl hr
  · exact FailsAtMost.bind_of_noBase (isQueryBoundP_chainStarts pp layer e) fun starts =>
      FailsAtMost.bind_of_noBase (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
        isQueryBoundP_chain _ _ _ _ _ _ _ _) fun _ => FailsAtMost.pure (by simp)

/-- One layer's signature fails as its one-time signature does. -/
theorem failsAtMost_signLayer (Q : ℕ) (pp : PublicParam) (layer : Layer) (e : ℕ)
    (msg : ByteArray) :
    FailsAtMost (fun r => r.toOption = none) Q
      ((Q : ℝ≥0∞) / 2 ^ 96 + ENNReal.ofReal (Real.exp (-4000)))
      (signLayer hashD pp prfD layer e msg) := by
  unfold signLayer
  refine (FailsAtMost.bind (ε₂ := 0) (failsAtMost_otsSign Q pp layer _ msg)
    fun r hr => ?_).mono_bound (add_zero _).le
  rcases r with _ | ⟨rho, y⟩
  · exact absurd rfl hr
  · exact FailsAtMost.bind_of_noBase (isQueryBoundP_path pp layer e) fun _ =>
      FailsAtMost.pure (by simp [Except.toOption])

/-- A signature fails at most as often as its two layers do. -/
theorem failsAtMost_signDerived (Q : ℕ) (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    FailsAtMost (fun r => r.toOption = none) Q
      (2 * ((Q : ℝ≥0∞) / 2 ^ 96 + ENNReal.ofReal (Real.exp (-4000))))
      (signDerived hashD prfD pp idx msg) := by
  unfold signDerived
  rw [two_mul]
  refine FailsAtMost.bind (failsAtMost_signLayer Q pp .bottom _ _) fun r hr => ?_
  rcases r with err | bottom
  · exact absurd rfl hr
  refine FailsAtMost.bind_of_noBase (isQueryBoundP_pure _ _ _) fun bottom => ?_
  refine FailsAtMost.bind_of_noBase (isQueryBoundP_node pp .bottom _ _) fun root => ?_
  refine (FailsAtMost.bind (ε₂ := 0) (failsAtMost_signLayer Q pp .top _ _)
    fun r hr => ?_).mono_bound (add_zero _).le
  rcases r with err | top
  · exact absurd rfl hr
  exact FailsAtMost.bind_of_noBase (isQueryBoundP_pure _ _ _) fun _ =>
    FailsAtMost.pure (by simp [Except.toOption])

/-- A request fails at most as often as the two layers of its signature do. -/
theorem failsAtMost_requestD (Q : ℕ) (request : SignRequest) :
    FailsAtMost (fun r => r.toOption = none) Q
      ((Q : ℝ≥0∞) / 2 ^ 95 + 2 * ENNReal.ofReal (Real.exp (-4000))) (requestD request) := by
  refine (FailsAtMost.bind_of_noBase isQueryBoundP_publicParamOf fun pp =>
    failsAtMost_signDerived Q pp _ _).mono_bound (le_of_eq ?_)
  rw [mul_add, ← two_pow_mul_div_two_pow 1 95, pow_one]

end Request

/-- **One request in the ideal game.**

Every search with a base in the table found a codeword.

Count only the runs whose cache ends with at most `Q` entries.

Then the request fails, or leaves a search without a codeword, with chance `<= Q / 2^95 + 2 e`.

Here `e = exp(-4000)`. -/
theorem prEvent_requestD_le (request : SignRequest) (st : IdealState) (hst : SearchesFound st)
    (Q : ℕ) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput)
        (requestD request)).run st}[
      (z.1.toOption = none ∨ ¬SearchesFound z.2) ∧ z.2.1.enncard ≤ Q] ≤
      (Q : ℝ≥0∞) / 2 ^ 95 + 2 * ENNReal.ofReal (Real.exp (-4000)) := by
  exact failsAtMost_requestD Q request st hst

end EthLib.Cryptography.Xmss.Unforgeability

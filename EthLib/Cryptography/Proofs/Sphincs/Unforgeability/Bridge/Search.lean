module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.AdversaryCalls
public import EthLib.Cryptography.Proofs.Sphincs.CodewordSearch
public import EthLib.Cryptography.Proofs.HashSig.FailedSearch

/-!
# Proofs: a signing request with short counter searches is cheap, and a long one leaves a trace

Each of the three one-time signatures of a request searches its counter from 0.

Counter `c` hashes `PK.seed | ADRS_enc(K) | M | BE_32(c)`, and passes when its digest is a codeword.

Take a bound `T <= 2^32` on the searches.

Fix one answer function.

A request whose three counters are below `T` then makes at most `470595 + 3 T` calls.

The other answers are nothing, or a signature with a counter of at least `T`.

In the random-oracle model, such an answer leaves a failed search of `T` trials in the cache.

That is a key, a message and the address of the key, whose first `T` counters all miss the code.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec OracleWorld HashInput)
open SphincsSecurity.Security.Prefix (hashCalls)

/-- The oracle input of counter `c` of a search: `PK.seed | ADRS | M | BE_32(c)`.

A search is the `PK.seed`, the address `ADRS_enc(K)` of its key and the message `M`. -/
def searchPoint (search : PkSeed × Adrs × Digest) (c : Nat) : HashInput :=
  (thInput search.1 search.2.1
    (packBytes search.2.2 ++ packBytes (toByte COUNTER_LEN c))).data.toList

/-- An answer misses the code: its 16-byte digest is not a codeword. -/
def SearchMiss (u : HashSig.HashOutput) : Prop :=
  codeword? (trunc N (HashSig.ofOutput u)) = none

instance : DecidablePred SearchMiss := fun u =>
  inferInstanceAs (Decidable (codeword? (trunc N (HashSig.ofOutput u)) = none))

/-- An answer of the signing oracle is a signature whose three counters are below `T`. -/
def SearchesBelow (T : Nat) : Option Signature → Prop
  | some sig => sig.bottom.counter.toNat < T ∧ sig.middle.counter.toNat < T ∧
      sig.top.counter.toNat < T
  | none => False

instance (T : Nat) : DecidablePred (SearchesBelow T)
  | some _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | none => inferInstanceAs (Decidable False)

/-- The counters below `2^32` of all searches hash distinct inputs. -/
theorem searchPoint_inj (search search' : PkSeed × Adrs × Digest) (c c' : Nat)
    (hc : c < MAX_COUNTER_TRIALS) (hc' : c' < MAX_COUNTER_TRIALS)
    (h : searchPoint search c = searchPoint search' c') : search = search' ∧ c = c' := by
  obtain ⟨s, a, m⟩ := search
  obtain ⟨s', a', m'⟩ := search'
  -- The fixed-size prefixes and the 16-byte message split the input one way.
  obtain ⟨rfl, rfl, hp⟩ := thInput_inj (ByteArray.ext (Array.toList_inj.mp h))
  obtain ⟨hm, hw⟩ := HashSig.byteArray_append_inj hp (by simp)
  have hword : MAX_COUNTER_TRIALS = 256 ^ COUNTER_LEN := by decide
  refine ⟨by rw [show m = m' from Base.packBytes_injective hm], ?_⟩
  exact toByte_inj (hword ▸ hc) (hword ▸ hc') (Base.packBytes_injective hw)

/-- One uniform answer misses the code with probability `1 - CODE_SIZE / 2^128`. -/
theorem prEvent_searchMiss :
    Pr{let u ← $ᵗ HashSig.HashOutput}[SearchMiss u] =
      ((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128 :=
  prEvent_not_codeword

variable (f : QueryImpl HashSpec Id)

/-! ## Searches under one answer function -/

/-- A search that returns a trial returns the first trial that passes, within its fuel. -/
theorem eval_findFirst_eq_some {κ β : Type} (trial : Nat → κ)
    (test : κ → OracleComp HashSpec (Option β)) :
    ∀ (c fuel : Nat) (k : κ) (x : β),
      evalWithAnswerFn f (Wots.findFirst trial test c fuel) = some (k, x) →
        ∃ i < fuel, k = trial (c + i) ∧ evalWithAnswerFn f (test (trial (c + i))) = some x ∧
          ∀ j < i, evalWithAnswerFn f (test (trial (c + j))) = none
  | _, 0, _, _, h => by simp [Wots.findFirst] at h
  | c, fuel + 1, k, x, h => by
    rw [Wots.findFirst, evalWithAnswerFn_bind] at h
    cases ht : evalWithAnswerFn f (test (trial c)) with
    | none =>
      rw [ht] at h
      obtain ⟨i, hi, hk, hx, hlt⟩ := eval_findFirst_eq_some trial test (c + 1) fuel k x h
      have hshift : c + 1 + i = c + (i + 1) := by omega
      refine ⟨i + 1, by omega, by rw [hk, hshift], by rw [← hshift]; exact hx, fun j hj => ?_⟩
      cases j with
      | zero => exact ht
      | succ j =>
        have hj' : c + 1 + j = c + (j + 1) := by omega
        rw [← hj']
        exact hlt j (by omega)
    | some y =>
      rw [ht, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, by omega, rfl, ht, fun j hj => absurd hj (Nat.not_lt_zero _)⟩

/-- A search queries the test of each trial that it reaches, after all earlier trials fail. -/
theorem queriesWith_test_subset_findFirst {κ β : Type} (trial : Nat → κ)
    (test : κ → OracleComp HashSpec (Option β)) :
    ∀ (c fuel j : Nat), j < fuel → (∀ i < j, evalWithAnswerFn f (test (trial (c + i))) = none) →
      HashSig.queriesWith f (test (trial (c + j))) ⊆
        HashSig.queriesWith f (Wots.findFirst trial test c fuel)
  | _, 0, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | c, fuel + 1, j, hj, hlt => by
    rw [Wots.findFirst, HashSig.queriesWith_bind]
    cases j with
    | zero => exact List.subset_append_left _ _
    | succ j =>
      have h0 : evalWithAnswerFn f (test (trial c)) = none := hlt 0 (by omega)
      rw [h0]
      refine List.subset_append_of_subset_right _ ?_
      have h := queriesWith_test_subset_findFirst trial test (c + 1) fuel j (by omega)
        fun i hi => by
          rw [show c + 1 + i = c + (i + 1) by omega]
          exact hlt (i + 1) (by omega)
      rwa [show c + 1 + j = c + (j + 1) by omega] at h

/-- Under `f`, counter `j < 2^32` of a search queries its point once, and reads its digest. -/
theorem trial_queryH (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (j : Nat)
    (hj : j < MAX_COUNTER_TRIALS) :
    evalWithAnswerFn f (encode H pkSeed key msg (UInt32.ofNat j)) =
        codeword? (trunc N (HashSig.ofOutput (f (searchPoint (pkSeed, adrsEnc key, msg) j)))) ∧
      HashSig.queriesWith f (encode H pkSeed key msg (UInt32.ofNat j)) =
        [searchPoint (pkSeed, adrsEnc key, msg) j] := by
  simp only [encode, th, H, HashSig.queryH, HashSig.oracleHash]
  rw [toNat_ofNat_trial hj]
  simp only [evalWithAnswerFn_map, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    evalWithAnswerFn_query, HashSig.queriesWith_map, HashSig.queriesWith_bind,
    HashSig.queriesWith_pure, searchPoint, List.append_nil, true_and]
  exact HashSig.queriesWith_query_bind f _ pure

section Layers

variable (H : ByteArray → OracleComp HashSpec (Vector UInt8 32))
  (secrets : Prf (OracleComp HashSpec))

/-- A layer queries its search, signs with the counter it finds, and fails when it finds none. -/
theorem signLayer_search (pkSeed : PkSeed) (layer : Layer) (idx : Nat)
    (tree : Merkle.Built Digest) (msg : Digest) :
    HashSig.queriesWith f
        (Internal.findCounter H pkSeed (OtsKey.ofIndex layer idx) msg 0 MAX_COUNTER_TRIALS) ⊆
      HashSig.queriesWith f (signLayer H pkSeed secrets layer idx tree msg) ∧
    (∀ e, evalWithAnswerFn f (signLayer H pkSeed secrets layer idx tree msg) = .error e →
      evalWithAnswerFn f
        (Internal.findCounter H pkSeed (OtsKey.ofIndex layer idx) msg 0 MAX_COUNTER_TRIALS) =
        none) ∧
    (∀ s, evalWithAnswerFn f (signLayer H pkSeed secrets layer idx tree msg) = .ok s →
      ∃ x, evalWithAnswerFn f
        (Internal.findCounter H pkSeed (OtsKey.ofIndex layer idx) msg 0 MAX_COUNTER_TRIALS) =
        some (s.counter, x)) := by
  refine ⟨?_, fun e he => ?_, fun s hs => ?_⟩
  · rw [signLayer, HashSig.queriesWith_bind, otsSign, HashSig.queriesWith_bind]
    exact List.subset_append_of_subset_left _ (List.subset_append_left _ _)
  · rw [signLayer, evalWithAnswerFn_bind, otsSign, evalWithAnswerFn_bind] at he
    cases hc : evalWithAnswerFn f
        (Internal.findCounter H pkSeed (OtsKey.ofIndex layer idx) msg 0 MAX_COUNTER_TRIALS) with
    | none => rfl
    | some found =>
      obtain ⟨counter, x⟩ := found
      rw [hc] at he
      simp [evalWithAnswerFn_bind, evalWithAnswerFn_pure] at he
  · rw [signLayer, evalWithAnswerFn_bind, otsSign, evalWithAnswerFn_bind] at hs
    cases hc : evalWithAnswerFn f
        (Internal.findCounter H pkSeed (OtsKey.ofIndex layer idx) msg 0 MAX_COUNTER_TRIALS) with
    | none =>
      rw [hc] at hs
      simp [evalWithAnswerFn_pure] at hs
    | some found =>
      obtain ⟨counter, x⟩ := found
      rw [hc] at hs
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hs
      rw [← Except.ok.inj hs]
      exact ⟨x, rfl⟩

/-- Signing queries each search it reaches, fails after one that finds nothing, else signs. -/
theorem signDerived_searches (pkSeed : PkSeed) (top : Merkle.Built Digest) (rho : Randomizer)
    (msg : Message) (idx : Nat)
    (hidx : digestIndex (evalWithAnswerFn f (hMsg H rho pkSeed top.value msg)) = idx) :
    (∀ e, evalWithAnswerFn f (signDerived H secrets pkSeed top rho msg) = .error e →
      ∃ layer, evalWithAnswerFn f (layerSearch f H secrets pkSeed idx layer) = none ∧
        HashSig.queriesWith f (layerSearch f H secrets pkSeed idx layer) ⊆
          HashSig.queriesWith f (signDerived H secrets pkSeed top rho msg)) ∧
    (∀ sig, evalWithAnswerFn f (signDerived H secrets pkSeed top rho msg) = .ok sig →
      (∀ layer, HashSig.queriesWith f (layerSearch f H secrets pkSeed idx layer) ⊆
          HashSig.queriesWith f (signDerived H secrets pkSeed top rho msg)) ∧
      (∃ x, evalWithAnswerFn f (layerSearch f H secrets pkSeed idx .bottom) =
        some (sig.bottom.counter, x)) ∧
      (∃ x, evalWithAnswerFn f (layerSearch f H secrets pkSeed idx .middle) =
        some (sig.middle.counter, x)) ∧
      (∃ x, evalWithAnswerFn f (layerSearch f H secrets pkSeed idx .top) =
        some (sig.top.counter, x))) := by
  rw [signDerived, HashSig.queriesWith_bind, evalWithAnswerFn_bind]
  dsimp only
  rw [hidx, HashSig.queriesWith_bind, evalWithAnswerFn_bind]
  -- The FORS signer gives the FORS public key, which the bottom key signs.
  have hkey := eval_forsSign_snd f H secrets pkSeed idx
    (digestLeaves (evalWithAnswerFn f (hMsg H rho pkSeed top.value msg)))
  generalize HashSig.queriesWith f (hMsg H rho pkSeed top.value msg) = qh
  generalize HashSig.queriesWith f (forsSign H pkSeed secrets idx
    (digestLeaves (evalWithAnswerFn f (hMsg H rho pkSeed top.value msg)))) = qf
  generalize evalWithAnswerFn f (forsSign H pkSeed secrets idx
    (digestLeaves (evalWithAnswerFn f (hMsg H rho pkSeed top.value msg)))) = fs at hkey
  obtain ⟨fors, forsPk⟩ := fs
  dsimp only at hkey ⊢
  have hb : forsPk = evalWithAnswerFn f (Recompute.layerMessage H pkSeed secrets .bottom idx) :=
    hkey
  subst hb
  have hm := eval_buildTree_value f H secrets pkSeed .bottom (OtsKey.ofIndex .bottom idx).tree
  have ht := eval_buildTree_value f H secrets pkSeed .middle (OtsKey.ofIndex .middle idx).tree
  simp only [layerSearch, Recompute.layerMessage] at hm ht ⊢
  -- The bottom layer: its tree's build, then its signature.
  rw [HashSig.queriesWith_bind, evalWithAnswerFn_bind, HashSig.queriesWith_bind,
    evalWithAnswerFn_bind]
  generalize HashSig.queriesWith f
    (buildTree H pkSeed secrets .bottom (OtsKey.ofIndex .bottom idx).tree) = qbt
  have sb := signLayer_search f H secrets pkSeed .bottom idx
    (evalWithAnswerFn f (buildTree H pkSeed secrets .bottom (OtsKey.ofIndex .bottom idx).tree))
    (evalWithAnswerFn f (forsKey H pkSeed secrets idx))
  generalize HashSig.queriesWith f (signLayer H pkSeed secrets .bottom idx
    (evalWithAnswerFn f (buildTree H pkSeed secrets .bottom (OtsKey.ofIndex .bottom idx).tree))
    (evalWithAnswerFn f (forsKey H pkSeed secrets idx))) = qb at sb
  cases hrb : evalWithAnswerFn f (signLayer H pkSeed secrets .bottom idx
      (evalWithAnswerFn f (buildTree H pkSeed secrets .bottom (OtsKey.ofIndex .bottom idx).tree))
      (evalWithAnswerFn f (forsKey H pkSeed secrets idx))) with
  | error err =>
    refine ⟨fun e _ => ⟨.bottom, sb.2.1 err hrb, fun y hy => by simp [sb.1 hy]⟩,
      fun sig h => ?_⟩
    simp at h
  | ok bottom =>
    obtain ⟨xb, hxb⟩ := sb.2.2 bottom hrb
    simp only [pure_bind, hm]
    -- The middle layer signs the bottom tree's root.
    rw [HashSig.queriesWith_bind, evalWithAnswerFn_bind, HashSig.queriesWith_bind,
      evalWithAnswerFn_bind]
    generalize HashSig.queriesWith f
      (buildTree H pkSeed secrets .middle (OtsKey.ofIndex .middle idx).tree) = qmt
    have sm := signLayer_search f H secrets pkSeed .middle idx
      (evalWithAnswerFn f (buildTree H pkSeed secrets .middle (OtsKey.ofIndex .middle idx).tree))
      (evalWithAnswerFn f (treeRoot H pkSeed secrets .bottom (OtsKey.ofIndex .bottom idx).tree))
    generalize HashSig.queriesWith f (signLayer H pkSeed secrets .middle idx
      (evalWithAnswerFn f (buildTree H pkSeed secrets .middle (OtsKey.ofIndex .middle idx).tree))
      (evalWithAnswerFn f
        (treeRoot H pkSeed secrets .bottom (OtsKey.ofIndex .bottom idx).tree))) = qm at sm
    cases hrm : evalWithAnswerFn f (signLayer H pkSeed secrets .middle idx
        (evalWithAnswerFn f (buildTree H pkSeed secrets .middle (OtsKey.ofIndex .middle idx).tree))
        (evalWithAnswerFn f
          (treeRoot H pkSeed secrets .bottom (OtsKey.ofIndex .bottom idx).tree))) with
    | error err =>
      refine ⟨fun e _ => ⟨.middle, sm.2.1 err hrm, fun y hy => by simp [sm.1 hy]⟩,
        fun sig h => ?_⟩
      simp at h
    | ok middle =>
      obtain ⟨xm, hxm⟩ := sm.2.2 middle hrm
      simp only [ht]
      -- The top layer signs the middle tree's root, with the top tree already built.
      rw [HashSig.queriesWith_bind, evalWithAnswerFn_bind]
      have st := signLayer_search f H secrets pkSeed .top idx top
        (evalWithAnswerFn f (treeRoot H pkSeed secrets .middle (OtsKey.ofIndex .middle idx).tree))
      generalize HashSig.queriesWith f (signLayer H pkSeed secrets .top idx top
        (evalWithAnswerFn f
          (treeRoot H pkSeed secrets .middle (OtsKey.ofIndex .middle idx).tree))) = qt at st
      cases hrt : evalWithAnswerFn f (signLayer H pkSeed secrets .top idx top
          (evalWithAnswerFn f
            (treeRoot H pkSeed secrets .middle (OtsKey.ofIndex .middle idx).tree))) with
      | error err =>
        refine ⟨fun e _ => ⟨.top, st.2.1 err hrt, fun y hy => by simp [st.1 hy]⟩,
          fun sig h => ?_⟩
        simp at h
      | ok topSig =>
        obtain ⟨xt, hxt⟩ := st.2.2 topSig hrt
        simp only [evalWithAnswerFn_pure]
        refine ⟨fun e h => by simp at h, fun sig h => ?_⟩
        cases h
        refine ⟨fun layer => ?_, ⟨xb, hxb⟩, ⟨xm, hxm⟩, ⟨xt, hxt⟩⟩
        cases layer with
        | bottom => exact fun y hy => by simp [sb.1 hy]
        | middle => exact fun y hy => by simp [sm.1 hy]
        | top => exact fun y hy => by simp [st.1 hy]

end Layers

/-! ## The searches of a signing request -/

/-- A request queries the search of each layer that it reaches, and answers as they end. -/
theorem signerOf_searches (sk : SecretKey) (msg : Message) (key : ExpandedKey)
    (top : Merkle.Built Digest) (rho : Randomizer) (idx : Nat)
    (hkey : evalWithAnswerFn f (expandKey H sk.seed) = key)
    (htop : evalWithAnswerFn f (buildTree H key.pkSeed (prf H key.pkSeed sk.seed) .top 0) = top)
    (hrho : evalWithAnswerFn f (prfMsg H key.skPrf key.pkSeed msg) = rho)
    (hidx : digestIndex (evalWithAnswerFn f (hMsg H rho key.pkSeed top.value msg)) = idx) :
    (evalWithAnswerFn f (signerOf sk msg) = none →
      ∃ layer, evalWithAnswerFn f
          (layerSearch f H (prf H key.pkSeed sk.seed) key.pkSeed idx layer) = none ∧
        HashSig.queriesWith f (layerSearch f H (prf H key.pkSeed sk.seed) key.pkSeed idx layer) ⊆
          HashSig.queriesWith f (signerOf sk msg)) ∧
    (∀ sig, evalWithAnswerFn f (signerOf sk msg) = some sig →
      (∀ layer, HashSig.queriesWith f
          (layerSearch f H (prf H key.pkSeed sk.seed) key.pkSeed idx layer) ⊆
          HashSig.queriesWith f (signerOf sk msg)) ∧
      (∃ x, evalWithAnswerFn f (layerSearch f H (prf H key.pkSeed sk.seed) key.pkSeed idx .bottom)
        = some (sig.bottom.counter, x)) ∧
      (∃ x, evalWithAnswerFn f (layerSearch f H (prf H key.pkSeed sk.seed) key.pkSeed idx .middle)
        = some (sig.middle.counter, x)) ∧
      (∃ x, evalWithAnswerFn f (layerSearch f H (prf H key.pkSeed sk.seed) key.pkSeed idx .top)
        = some (sig.top.counter, x))) := by
  obtain ⟨herr, hok⟩ := signDerived_searches f H (prf H key.pkSeed sk.seed) key.pkSeed top rho
    msg idx hidx
  -- The request is the signer's result, made an option, after the key, the top tree and `R`.
  have hq : HashSig.queriesWith f (signDerived H (prf H key.pkSeed sk.seed) key.pkSeed top rho msg)
      ⊆ HashSig.queriesWith f (signerOf sk msg) := by
    rw [signerOf, HashSig.queriesWith_map, signWith, HashSig.queriesWith_bind, hkey]
    dsimp only
    rw [HashSig.queriesWith_bind, htop, HashSig.queriesWith_bind, hrho]
    exact List.subset_append_of_subset_right _ (List.subset_append_of_subset_right _
      (List.subset_append_of_subset_right _ (List.Subset.refl _)))
  have he : evalWithAnswerFn f (signerOf sk msg) = Except.toOption
      (evalWithAnswerFn f (signDerived H (prf H key.pkSeed sk.seed) key.pkSeed top rho msg)) := by
    rw [signerOf, evalWithAnswerFn_map, signWith, evalWithAnswerFn_bind, hkey]
    dsimp only
    rw [evalWithAnswerFn_bind, htop, evalWithAnswerFn_bind, hrho]
  rw [he]
  cases hs : evalWithAnswerFn f (signDerived H (prf H key.pkSeed sk.seed) key.pkSeed top rho msg)
    with
  | error e =>
    obtain ⟨layer, hnone, hsub⟩ := herr e hs
    refine ⟨fun _ => ⟨layer, hnone, fun y hy => hq (hsub hy)⟩, fun sig h => ?_⟩
    simp [Except.toOption] at h
  | ok sig' =>
    refine ⟨fun h => by simp [Except.toOption] at h, fun sig h => ?_⟩
    simp only [Except.toOption, Option.some.injEq] at h
    subst h
    obtain ⟨hsub, hb, hm, ht⟩ := hok sig' hs
    exact ⟨fun layer y hy => hq (hsub layer hy), hb, hm, ht⟩

/-- A counter search that returns counter `c` makes `c + 1` calls. -/
theorem hashCalls_findCounter_of_eq_some (pkSeed : PkSeed) (key : OtsKey) (msg : Digest)
    (counter : UInt32) (x : Codeword)
    (h : evalWithAnswerFn f (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS) =
      some (counter, x)) :
    hashCalls f (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS) =
      counter.toNat + 1 := by
  obtain ⟨i, hi, rfl, hx, hlt⟩ := eval_findFirst_eq_some f _ _ 0 _ counter x h
  rw [Nat.zero_add] at hx ⊢
  rw [toNat_ofNat_trial hi]
  refine hashCalls_findCounter_of_least f H (hashCalls_queryH f) pkSeed key msg i hi ?_ ?_
  · simp only [encodes, hx, Option.isSome_some]
  · intro j hj
    have := hlt j hj
    rw [Nat.zero_add] at this
    simp only [encodes, this, Option.isSome_none]

/-- A counter search that finds no counter below `T` queries and misses each counter below `T`. -/
theorem findCounter_misses (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (T : Nat)
    (hT : T ≤ MAX_COUNTER_TRIALS)
    (h : ∀ counter x, evalWithAnswerFn f
      (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS) = some (counter, x) →
        T ≤ counter.toNat) :
    ∀ j < T, evalWithAnswerFn f (encode H pkSeed key msg (UInt32.ofNat j)) = none ∧
      HashSig.queriesWith f (encode H pkSeed key msg (UInt32.ofNat j)) ⊆
        HashSig.queriesWith f (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS) := by
  have hmiss : ∀ j < T, evalWithAnswerFn f (encode H pkSeed key msg (UInt32.ofNat j)) = none := by
    intro j hj
    cases hc : evalWithAnswerFn f (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS)
      with
    | none =>
      -- No counter encodes, so neither does counter `j`.
      have hf := isSome_findCounter f H pkSeed key msg 0 MAX_COUNTER_TRIALS
      rw [hc, Option.isSome_none] at hf
      cases he : evalWithAnswerFn f (encode H pkSeed key msg (UInt32.ofNat j)) with
      | none => rfl
      | some y =>
        have hok : encodes f H pkSeed key msg (0 + j) = true := by
          simp only [encodes, Nat.zero_add, he, Option.isSome_some]
        have := (searchFinds_iff _ 0 MAX_COUNTER_TRIALS).2 ⟨j, by omega, hok⟩
        rw [← hf] at this
        exact absurd this Bool.false_ne_true
    | some found =>
      -- The counter found is the first that encodes, and it is at least `T`.
      obtain ⟨counter, x⟩ := found
      have hle := h counter x hc
      obtain ⟨i, hi, rfl, -, hlt⟩ := eval_findFirst_eq_some f _ _ 0 _ counter x hc
      rw [Nat.zero_add, toNat_ofNat_trial hi] at hle
      have := hlt j (by omega)
      rwa [Nat.zero_add] at this
  intro j hj
  refine ⟨hmiss j hj, ?_⟩
  have hsub := queriesWith_test_subset_findFirst f UInt32.ofNat (encode H pkSeed key msg) 0
    MAX_COUNTER_TRIALS j (by omega) fun i hi => by
      rw [Nat.zero_add]
      exact hmiss i (by omega)
  rw [Nat.zero_add] at hsub
  exact hsub

/-- **A request whose three counters are below `T` makes at most `470595 + 3 T` calls.**

The answers are those of one answer function, and the request returns the signature `sig`. -/
theorem hashCalls_signerOf_le_of_below (T : Nat) (sk : SecretKey) (msg : Message)
    (sig : Signature) (hsig : evalWithAnswerFn f (signerOf sk msg) = some sig)
    (h : SearchesBelow T (some sig)) :
    hashCalls f (signerOf sk msg) ≤ 470595 + 3 * T := by
  obtain ⟨key, hkey⟩ : ∃ key, evalWithAnswerFn f (expandKey H sk.seed) = key := ⟨_, rfl⟩
  obtain ⟨top, htop⟩ : ∃ top, evalWithAnswerFn f
      (buildTree H key.pkSeed (prf H key.pkSeed sk.seed) .top 0) = top := ⟨_, rfl⟩
  obtain ⟨rho, hrho⟩ : ∃ rho, evalWithAnswerFn f
      (prfMsg H key.skPrf key.pkSeed msg) = rho := ⟨_, rfl⟩
  obtain ⟨idx, hidx⟩ : ∃ idx, digestIndex
      (evalWithAnswerFn f (hMsg H rho key.pkSeed top.value msg)) = idx := ⟨_, rfl⟩
  obtain ⟨-, ⟨xb, hb⟩, ⟨xm, hm⟩, ⟨xt, ht⟩⟩ :=
    (signerOf_searches f sk msg key top rho idx hkey htop hrho hidx).2 sig hsig
  -- All three layers sign, each with the counter its search finds.
  have hsigns : ∀ layer,
      layerSigns f H (prf H key.pkSeed sk.seed) key.pkSeed idx layer = true := by
    intro layer
    rw [layerSigns_eq]
    cases layer
    · rw [hb, Option.isSome_some]
    · rw [hm, Option.isSome_some]
    · rw [ht, Option.isSome_some]
  obtain ⟨hlb, hlm, hlt⟩ := h
  rw [signerOf, hashCalls_map, hashCalls_signWith_of_signs f H (hashCalls_queryH f) sk msg key
    top rho idx hkey htop hrho hidx hsigns]
  rw [layerSearch] at hb hm ht ⊢
  rw [layerSearch, layerSearch, hashCalls_findCounter_of_eq_some f _ _ _ _ _ hb,
    hashCalls_findCounter_of_eq_some f _ _ _ _ _ hm,
    hashCalls_findCounter_of_eq_some f _ _ _ _ _ ht]
  omega

/-- **A request answered otherwise leaves a failed search of `T` trials in the cache.**

The request runs in the random-oracle model, from any cache, and `T <= 2^32`.

Its answer is nothing, or a signature with a counter of at least `T`.

Then the final cache holds a search whose first `T` counters all miss the code. -/
theorem failedSearch_of_signerOf (T : Nat) (hT : T ≤ MAX_COUNTER_TRIALS) (sk : SecretKey)
    (msg : Message) (cache : HashSpec.QueryCache) (z : Option Signature × HashSpec.QueryCache)
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (liftM (signerOf sk msg) : OracleComp OracleWorld (Option Signature))).run cache))
    (hlong : ¬SearchesBelow T z.1) :
    HashSig.FailedSearch searchPoint SearchMiss T z.2 := by
  obtain ⟨g, -, hval, hcached⟩ :=
    HashSig.exists_answerFn_of_mem_support (signerOf sk msg) cache z hz
  obtain ⟨key, hkey⟩ : ∃ key, evalWithAnswerFn g (expandKey H sk.seed) = key := ⟨_, rfl⟩
  obtain ⟨top, htop⟩ : ∃ top, evalWithAnswerFn g
      (buildTree H key.pkSeed (prf H key.pkSeed sk.seed) .top 0) = top := ⟨_, rfl⟩
  obtain ⟨rho, hrho⟩ : ∃ rho, evalWithAnswerFn g
      (prfMsg H key.skPrf key.pkSeed msg) = rho := ⟨_, rfl⟩
  obtain ⟨idx, hidx⟩ : ∃ idx, digestIndex
      (evalWithAnswerFn g (hMsg H rho key.pkSeed top.value msg)) = idx := ⟨_, rfl⟩
  obtain ⟨hnone, hsome⟩ := signerOf_searches g sk msg key top rho idx hkey htop hrho hidx
  -- Some layer's search finds no counter below `T`, and the request queries that search.
  obtain ⟨layer, hlong', hsub⟩ : ∃ layer,
      (∀ counter x, evalWithAnswerFn g
        (layerSearch g H (prf H key.pkSeed sk.seed) key.pkSeed idx layer) = some (counter, x) →
          T ≤ counter.toNat) ∧
      HashSig.queriesWith g (layerSearch g H (prf H key.pkSeed sk.seed) key.pkSeed idx layer) ⊆
        HashSig.queriesWith g (signerOf sk msg) := by
    rw [hval] at hlong
    cases hs : evalWithAnswerFn g (signerOf sk msg) with
    | none =>
      obtain ⟨layer, hl, hsub⟩ := hnone hs
      refine ⟨layer, fun counter x h => ?_, hsub⟩
      rw [hl] at h
      cases h
    | some sig =>
      rw [hs] at hlong
      obtain ⟨hsub, ⟨xb, hb⟩, ⟨xm, hm⟩, ⟨xt, ht⟩⟩ := hsome sig hs
      simp only [SearchesBelow, not_and_or, not_lt] at hlong
      rcases hlong with hl | hl | hl
      · refine ⟨.bottom, fun counter x h => ?_, hsub .bottom⟩
        rw [hb, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact hl
      · refine ⟨.middle, fun counter x h => ?_, hsub .middle⟩
        rw [hm, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact hl
      · refine ⟨.top, fun counter x h => ?_, hsub .top⟩
        rw [ht, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact hl
  -- Its first `T` counters miss under `g`, and the final cache holds their answers.
  refine ⟨(key.pkSeed, adrsEnc (OtsKey.ofIndex layer idx), evalWithAnswerFn g
    (Recompute.layerMessage H key.pkSeed (prf H key.pkSeed sk.seed) layer idx)), fun j hj => ?_⟩
  obtain ⟨hmiss, hq⟩ := findCounter_misses g _ _ _ T hT hlong' j hj
  obtain ⟨heval, hpoint⟩ := trial_queryH g key.pkSeed (OtsKey.ofIndex layer idx)
    (evalWithAnswerFn g (Recompute.layerMessage H key.pkSeed (prf H key.pkSeed sk.seed) layer idx))
    j (by omega)
  rw [hpoint] at hq
  refine ⟨_, hcached _ (hsub (hq (List.mem_singleton_self _))), ?_⟩
  rw [heval] at hmiss
  exact hmiss

/-! ## The adversary that stops after a long search -/

/-- The wrapper's handler, with a flag that records an answer with a long search.

Before the flag, it forwards every query and raises the flag on a long answer.

After the flag, it forwards coins, answers a hash call with 0 and a signing request with nothing. -/
def capImpl (T : Nat) :
    QueryImpl (OracleWorld + SigningSpec) (StateT Bool (OracleComp (OracleWorld + SigningSpec)))
  | .inl (.inl n) => fun stopped =>
      (fun u => (u, stopped)) <$> liftM ((OracleWorld + SigningSpec).query (.inl (.inl n)))
  | .inl (.inr x) => fun stopped =>
      if stopped then pure ((0 : HashSig.HashOutput), true)
      else (fun u => (u, false)) <$> liftM ((OracleWorld + SigningSpec).query (.inl (.inr x)))
  | .inr msg => fun stopped =>
      if stopped then pure (none, true)
      else (fun a => (a, !decide (SearchesBelow T a))) <$>
        liftM ((OracleWorld + SigningSpec).query (.inr msg))

/-- The adversary, wrapped to stop querying after an answer with a long search. -/
def capSearches (T : Nat) (adversary : Adversary) : Adversary where
  main pk := (simulateQ (capImpl T) (adversary.main pk)).run' false

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge

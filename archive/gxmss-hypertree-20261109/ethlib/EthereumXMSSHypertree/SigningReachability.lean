/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.Reachability
public import EthereumXMSSHypertree.Retry

/-!
# Invocation counts of complete source signing

The concrete counting interpreter retains the source retry count and each
early failure branch. All trees and retry loops are handled symbolically.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography
open Xmss Xmss.Constants
open Reachability

namespace SigningReachability

/-- The result projection of a counting bind is ordinary deterministic sequencing. -/
@[simp] theorem bind_result {α β : Type} (x : Counted α) (f : α → Counted β) :
    (x >>= f).result = (f x.result).result := rfl

/-- Counting bind adds every invocation in both computations. -/
@[simp] theorem bind_calls {α β : Type} (x : Counted α) (f : α → Counted β) :
    (x >>= f).calls = x.calls + (f x.result).calls := rfl

/-- Mapping a source value does not change the returned deterministic function value. -/
@[simp] theorem map_result {α β : Type} (x : Counted α) (f : α → β) :
    (f <$> x).result = f x.result := rfl

/-- Mapping a source value makes no further hash invocations. -/
@[simp] theorem map_calls {α β : Type} (x : Counted α) (f : α → β) :
    (f <$> x).calls = x.calls := Nat.add_zero _

/-- Returning a source value preserves that value. -/
@[simp] theorem pure_result {α : Type} (x : α) : (pure x : Counted α).result = x := rfl

/-- Returning a source value makes no hash invocations. -/
@[simp] theorem pure_calls {α : Type} (x : α) : (pure x : Counted α).calls = 0 := rfl

/-- Counting a source message digest retains its native deterministic result. -/
theorem messageDigest_result (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer) :
    (messageDigest (countedHash H) pp layer e msg rho).result =
      (messageDigest (pureHash H) pp layer e msg rho).run := rfl

/-- A source retry acceptance test retains its exact deterministic result. -/
theorem retry_test_result (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c : Nat) :
    (codeword? <$> messageDigest (countedHash H) pp layer e msg
      (trialRandomizer base c)).result = retryAccept H pp layer e msg base c := by
  rw [map_result, messageDigest_result]
  rfl

/-- A source retry acceptance test costs one invocation before its Boolean decision. -/
theorem retry_test_calls (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c : Nat) :
    (codeword? <$> messageDigest (countedHash H) pp layer e msg
      (trialRandomizer base c)).calls = 1 := by
  rw [map_calls]
  rfl

/-- The counting interpreter returns the exact deterministic source retry outcome. -/
theorem retry_result (H : ByteArray → Vector UInt8 32) (pp : PublicParam) (layer : Layer)
    (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    (Internal.findCodeword (countedHash H) pp layer e msg base c fuel).result =
      retryOutcome H pp layer e msg base c fuel := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    rw [findCodeword_step, retryOutcome_succ, bind_result, retry_test_result]
    cases ht : retryAccept H pp layer e msg base c <;> simp [ih]

/-- Each attempted source trial costs exactly one hash before its stopping decision. -/
theorem retry_calls_succ (H : ByteArray → Vector UInt8 32) (pp : PublicParam) (layer : Layer)
    (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    (Internal.findCodeword (countedHash H) pp layer e msg base c (fuel + 1)).calls =
      1 + match retryAccept H pp layer e msg base c with
        | some _ => 0
        | none =>
          (Internal.findCodeword (countedHash H) pp layer e msg base (c + 1) fuel).calls := by
  rw [findCodeword_step, bind_calls, retry_test_result, retry_test_calls]
  cases ht : retryAccept H pp layer e msg base c <;> rfl

/-- The actual source retry count never exceeds its remaining fuel. -/
theorem retry_calls_le (H : ByteArray → Vector UInt8 32) (pp : PublicParam) (layer : Layer)
    (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    (Internal.findCodeword (countedHash H) pp layer e msg base c fuel).calls ≤ fuel := by
  induction fuel generalizing c with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    rw [retry_calls_succ]
    cases ht : retryAccept H pp layer e msg base c with
    | none => have := ih (c + 1); simp only; omega
    | some x => simp

/-- Exhausting the source retry loop costs its full fuel, with every failed trial counted. -/
theorem retry_calls_of_none (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel : Nat)
    (h : retryOutcome H pp layer e msg base c fuel = none) :
    (Internal.findCodeword (countedHash H) pp layer e msg base c fuel).calls = fuel := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    rw [retryOutcome_succ] at h
    rw [retry_calls_succ]
    cases ht : retryAccept H pp layer e msg base c with
    | none =>
      simp only [ht] at h ⊢
      rw [ih (c + 1) h]
      omega
    | some x => simp [ht] at h

/-- A first success at counter `j` costs exactly `j-c+1` trials from counter `c`. -/
theorem retry_calls_at_first (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel j : Nat)
    {x : Vector (Fin CHAIN_LENGTH) V} (hlo : c ≤ j) (hhi : j < c + fuel)
    (hx : retryAccept H pp layer e msg base j = some x)
    (hbefore : ∀ k, c ≤ k → k < j → retryAccept H pp layer e msg base k = none) :
    (Internal.findCodeword (countedHash H) pp layer e msg base c fuel).calls = j - c + 1 := by
  induction fuel generalizing c with
  | zero => omega
  | succ fuel ih =>
    rw [retry_calls_succ]
    by_cases heq : j = c
    · subst j
      simp [hx]
    · rw [hbefore c (by omega) (by omega)]
      rw [ih (c + 1) (by omega) (by omega) (fun k hk hk' => hbefore k (by omega) hk')]
      simp only
      omega

/-- The actual source search after deriving the message's randomizer base. -/
@[expose] def search (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) :=
  Internal.findCodeword (countedHash H) pp layer e msg
    (randomizerBase pp (seedPrf (countedHash H) seed) layer e msg).result
    0 MAX_RANDOMIZER_TRIALS

/-- Actual hash invocations made by the source retry phase. -/
@[expose] def trials (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) : Nat :=
  (search H seed pp layer e msg).calls

/-- Source signing's retry budget is the source's finite 32-bit counter budget. -/
theorem trials_le (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) :
    trials H seed pp layer e msg ≤ 2 ^ 32 :=
  retry_calls_le H pp layer e msg _ 0 MAX_RANDOMIZER_TRIALS

/-- Every successful counted source search returns genuinely admitted source digits. -/
theorem search_digits_valid (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer)
    (x : Vector (Fin CHAIN_LENGTH) V) (h : (search H seed pp layer e msg).result = some (rho, x)) :
    ∃ d : Digest, codeword? d = some x := by
  have hs : retryOutcome H pp layer e msg
      (randomizerBase pp (seedPrf (countedHash H) seed) layer e msg).result
      0 MAX_RANDOMIZER_TRIALS = some (rho, x) := by
    rw [← retry_result]
    exact h
  obtain ⟨j, _, _, _, hx, _⟩ := retryOutcome_first H pp layer e msg _ 0 MAX_RANDOMIZER_TRIALS hs
  exact ⟨(messageDigest (pureHash H) pp layer e msg (trialRandomizer _ j)).run, hx⟩

/-- A failed actual source search consumes all `2^32` trials. -/
theorem trials_of_none (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray)
    (h : (search H seed pp layer e msg).result = none) :
    trials H seed pp layer e msg = 2 ^ 32 := by
  apply retry_calls_of_none
  rw [← retry_result]
  exact h

/-- Actual source success gives a least accepted counter and its exact invocation count. -/
theorem trials_first (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer)
    (x : Vector (Fin CHAIN_LENGTH) V) (h : (search H seed pp layer e msg).result = some (rho, x)) :
    ∃ j, j < MAX_RANDOMIZER_TRIALS ∧
      rho = trialRandomizer
        (randomizerBase pp (seedPrf (countedHash H) seed) layer e msg).result j ∧
      retryAccept H pp layer e msg
        (randomizerBase pp (seedPrf (countedHash H) seed) layer e msg).result j = some x ∧
      (∀ k, k < j → retryAccept H pp layer e msg
        (randomizerBase pp (seedPrf (countedHash H) seed) layer e msg).result k = none) ∧
      trials H seed pp layer e msg = j + 1 := by
  have hs : retryOutcome H pp layer e msg
      (randomizerBase pp (seedPrf (countedHash H) seed) layer e msg).result
      0 MAX_RANDOMIZER_TRIALS = some (rho, x) := by
    rw [← retry_result]
    exact h
  obtain ⟨j, hj, hj', hrho, hx, hbefore⟩ :=
    retryOutcome_first H pp layer e msg _ 0 MAX_RANDOMIZER_TRIALS hs
  refine ⟨j, by omega, hrho, hx, (fun k hk => hbefore k (by omega) hk), ?_⟩
  simpa only [trials, search, Nat.sub_zero] using retry_calls_at_first H pp layer e msg _
    0 MAX_RANDOMIZER_TRIALS j hj hj' hx hbefore

/-- Failed source OTS search returns no signature, without evaluating any chain starts. -/
theorem otsSign_result_of_none (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (h : (search H seed pp layer e msg).result = none) :
    (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).result = none := by
  simp only [otsSign, bind_result]
  rw [show (Internal.findCodeword (countedHash H) pp layer e msg
    (randomizerBase pp (seedPrf (countedHash H) seed) layer e msg).result
    0 MAX_RANDOMIZER_TRIALS).result = none from h]
  rfl

/-- Source OTS success is precisely success of its preceding actual search. -/
theorem otsSign_isSome (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray) :
    (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).result.isSome =
      (search H seed pp layer e msg).result.isSome := by
  simp only [otsSign, bind_result, search]
  generalize h : (Internal.findCodeword (countedHash H) pp layer e msg
    (randomizerBase pp (seedPrf (countedHash H) seed) layer e msg).result
    0 MAX_RANDOMIZER_TRIALS).result = outcome
  cases outcome with
  | none => rfl
  | some pair => rcases pair with ⟨rho, x⟩; simp only [bind_result, pure_result]; rfl

/-- Source OTS exhaustion costs its base derivation and all actual failed trials. -/
theorem otsSign_calls_of_none (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (h : (search H seed pp layer e msg).result = none) :
    (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).calls =
      1 + trials H seed pp layer e msg := by
  simp only [otsSign, bind_calls]
  rw [show (Internal.findCodeword (countedHash H) pp layer e msg
    (randomizerBase pp (seedPrf (countedHash H) seed) layer e msg).result
    0 MAX_RANDOMIZER_TRIALS).result = none from h]
  simp only [pure_calls, Nat.add_zero]
  rfl

/-- Source OTS success costs its base, actual trials, and its complete reveal phase. -/
theorem otsSign_calls_of_some (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer)
    (x : Vector (Fin CHAIN_LENGTH) V) (h : (search H seed pp layer e msg).result = some (rho, x)) :
    (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).calls =
      1 + trials H seed pp layer e msg + 135 := by
  obtain ⟨d, hd⟩ := search_digits_valid H seed pp layer e msg rho x h
  exact otsSign_calls_of_search_success H seed pp layer e msg rho d x hd h

/-- The source layer succeeds exactly when its source retry phase succeeds. -/
theorem layer_search_isSome (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : Nat) (msg : ByteArray) :
    (signLayer (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).result.toOption.isSome
      =
      (search H seed pp layer (UInt32.ofNat e) msg).result.isSome := by
  rw [← otsSign_isSome]
  simp only [signLayer, bind_result]
  generalize (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer
    (UInt32.ofNat e) msg).result = outcome
  cases outcome with
  | none => rfl
  | some pair => rcases pair with ⟨rho, values⟩; simp only [bind_result, pure_result]; rfl

/-- A rejected source layer spends only its base derivation and actual search trials. -/
theorem layer_calls_of_error (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : Nat) (msg : ByteArray) (err : XmssError)
    (h : (signLayer (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).result =
      .error err) :
    (signLayer (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).calls =
      1 + trials H seed pp layer (UInt32.ofNat e) msg := by
  have hi := layer_search_isSome H seed pp layer e msg
  rw [h] at hi
  have hs : (search H seed pp layer (UInt32.ofNat e) msg).result = none := by
    apply Option.not_isSome_iff_eq_none.mp
    intro hp
    rw [← hi] at hp
    exact Bool.false_ne_true hp
  have ho := otsSign_result_of_none H seed pp layer (UInt32.ofNat e) msg hs
  rw [signLayer_calls_of_failure H seed pp layer e msg ho]
  exact otsSign_calls_of_none H seed pp layer (UInt32.ofNat e) msg hs

/-- An accepted source layer also spends its complete reveal and path costs. -/
theorem layer_calls_of_ok (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature)
    (h : (signLayer (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).result =
      .ok sig) :
    (signLayer (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).calls =
      13434795 + trials H seed pp layer (UInt32.ofNat e) msg := by
  have hi := layer_search_isSome H seed pp layer e msg
  rw [h] at hi
  have hs : (search H seed pp layer (UInt32.ofNat e) msg).result.isSome := hi.symm
  obtain ⟨⟨rho, x⟩, hsearch⟩ := Option.isSome_iff_exists.mp hs
  have hoSome : (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer
      (UInt32.ofNat e) msg).result.isSome := by
    rw [otsSign_isSome]
    exact hs
  obtain ⟨⟨randomizer, values⟩, ho⟩ := Option.isSome_iff_exists.mp hoSome
  rw [signLayer_calls_of_success H seed pp layer e msg randomizer values ho,
    otsSign_calls_of_some H seed pp layer (UInt32.ofNat e) msg rho x hsearch]
  omega

/-- The actual bottom-layer source computation in derived-seed signing. -/
@[expose] def bottomLayer (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (idx : LeafIndex) (msg : Message) :=
  signLayer (countedHash H) pp (seedPrf (countedHash H) seed) .bottom idx.toNat (packBytes msg)

/-- The complete bottom tree that source signing recomputes after bottom success. -/
@[expose] def bottomRoot (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (idx : LeafIndex) :=
  node (countedHash H) pp (seedPrf (countedHash H) seed) .bottom LAYER_HEIGHT (bottomTree idx)

/-- The actual top-layer source computation, signing the recomputed bottom root. -/
@[expose] def topLayer (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (idx : LeafIndex) :=
  signLayer (countedHash H) pp (seedPrf (countedHash H) seed) .top (bottomTree idx)
    (packBytes (bottomRoot H seed pp idx).result)

/-- The number of actual bottom message-digest trials. -/
@[expose] def bottomTrials (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (idx : LeafIndex) (msg : Message) : Nat :=
  trials H seed pp .bottom (UInt32.ofNat idx.toNat) (packBytes msg)

/-- The number of actual top message-digest trials for the original bottom tree. -/
@[expose] def topTrials (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (idx : LeafIndex) : Nat :=
  trials H seed pp .top (UInt32.ofNat (bottomTree idx))
    (packBytes (bottomRoot H seed pp idx).result)

/-- Bottom failure ends derived-seed source signing before its root or top computations. -/
theorem signDerived_calls_bottom_error (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (idx : LeafIndex) (msg : Message) (err : XmssError)
    (hb : (bottomLayer H seed pp idx msg).result = .error err) :
    (signDerived (countedHash H) (seedPrf (countedHash H) seed) pp idx msg).calls =
      1 + bottomTrials H seed pp idx msg := by
  simp only [signDerived, bind_calls]
  rw [show (signLayer (countedHash H) pp (seedPrf (countedHash H) seed) .bottom
    idx.toNat (packBytes msg)).result = .error err from hb]
  simp only [pure_calls, Nat.add_zero]
  exact layer_calls_of_error H seed pp .bottom idx.toNat (packBytes msg) err hb

/-- Top failure occurs after bottom signing and the complete bottom-root recomputation. -/
theorem signDerived_calls_top_error (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (idx : LeafIndex) (msg : Message) (bottom : LayerSignature)
    (err : XmssError) (hb : (bottomLayer H seed pp idx msg).result = .ok bottom)
    (ht : (topLayer H seed pp idx).result = .error err) :
    (signDerived (countedHash H) (seedPrf (countedHash H) seed) pp idx msg).calls =
      26869675 + bottomTrials H seed pp idx msg + topTrials H seed pp idx := by
  simp only [signDerived, bind_calls]
  rw [show (signLayer (countedHash H) pp (seedPrf (countedHash H) seed) .bottom
    idx.toNat (packBytes msg)).result = .ok bottom from hb]
  simp only [bind_calls]
  have ht' := ht
  simp only [topLayer, bottomRoot] at ht'
  rw [ht']
  simp only [pure_calls, Nat.add_zero]
  have htop := layer_calls_of_error H seed pp .top (bottomTree idx)
    (packBytes (bottomRoot H seed pp idx).result) err ht
  simp only [bottomRoot] at htop
  rw [layer_calls_of_ok H seed pp .bottom idx.toNat (packBytes msg) bottom hb,
    height16_node_calls, htop]
  simp only [bottomTrials, topTrials, bottomRoot]
  omega

/-- Complete derived-seed source success includes two paths and a whole bottom tree. -/
theorem signDerived_calls_ok (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (idx : LeafIndex) (msg : Message) (bottom top : LayerSignature)
    (hb : (bottomLayer H seed pp idx msg).result = .ok bottom)
    (ht : (topLayer H seed pp idx).result = .ok top) :
    (signDerived (countedHash H) (seedPrf (countedHash H) seed) pp idx msg).calls =
      40304469 + bottomTrials H seed pp idx msg + topTrials H seed pp idx := by
  simp only [signDerived, bind_calls]
  rw [show (signLayer (countedHash H) pp (seedPrf (countedHash H) seed) .bottom
    idx.toNat (packBytes msg)).result = .ok bottom from hb]
  simp only [bind_calls]
  have ht' := ht
  simp only [topLayer, bottomRoot] at ht'
  rw [ht']
  simp only [bind_calls, pure_calls, Nat.add_zero]
  have htop := layer_calls_of_ok H seed pp .top (bottomTree idx)
    (packBytes (bottomRoot H seed pp idx).result) top ht
  simp only [bottomRoot] at htop
  rw [layer_calls_of_ok H seed pp .bottom idx.toNat (packBytes msg) bottom hb,
    height16_node_calls, htop]
  simp only [bottomTrials, topTrials, bottomRoot]
  omega

/-- The exact scheme seed derived by complete source signing from its raw secret key. -/
@[expose] def derivedSeed (H : ByteArray → Vector UInt8 32) (sk : SecretKey) : Seed :=
  (schemeSeed (countedHash H) sk.seed).result

/-- The exact public parameter derived by complete source signing. -/
@[expose] def derivedParam (H : ByteArray → Vector UInt8 32) (sk : SecretKey) : PublicParam :=
  (publicParamOf (seedPrf (countedHash H) (derivedSeed H sk))).result

/-- Complete source signing always spends two derivations before its derived-seed phases. -/
theorem signWith_calls (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) :
    (signWith (countedHash H) sk idx msg).calls = 2 +
      (signDerived (countedHash H) (seedPrf (countedHash H) (derivedSeed H sk))
        (derivedParam H sk) idx msg).calls := by
  simp only [signWith, bind_calls]
  change 1 + (1 + (signDerived (countedHash H)
    (seedPrf (countedHash H) (derivedSeed H sk)) (derivedParam H sk) idx msg).calls) = _
  omega

/-- Complete source bottom failure stops after two initial derivations and the bottom search. -/
theorem signWith_calls_bottom_error (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) (err : XmssError)
    (hb : (bottomLayer H (derivedSeed H sk) (derivedParam H sk) idx msg).result = .error err) :
    (signWith (countedHash H) sk idx msg).calls =
      3 + bottomTrials H (derivedSeed H sk) (derivedParam H sk) idx msg := by
  rw [signWith_calls, signDerived_calls_bottom_error H _ _ idx msg err hb]
  omega

/-- Complete source top failure retains bottom signing and its complete root computation. -/
theorem signWith_calls_top_error (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) (bottom : LayerSignature) (err : XmssError)
    (hb : (bottomLayer H (derivedSeed H sk) (derivedParam H sk) idx msg).result = .ok bottom)
    (ht : (topLayer H (derivedSeed H sk) (derivedParam H sk) idx).result = .error err) :
    (signWith (countedHash H) sk idx msg).calls =
      26869677 + bottomTrials H (derivedSeed H sk) (derivedParam H sk) idx msg +
        topTrials H (derivedSeed H sk) (derivedParam H sk) idx := by
  rw [signWith_calls, signDerived_calls_top_error H _ _ idx msg bottom err hb ht]
  omega

/-- Complete successful source signing retains both trial counts and every tree computation. -/
theorem signWith_calls_ok (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) (bottom top : LayerSignature)
    (hb : (bottomLayer H (derivedSeed H sk) (derivedParam H sk) idx msg).result = .ok bottom)
    (ht : (topLayer H (derivedSeed H sk) (derivedParam H sk) idx).result = .ok top) :
    (signWith (countedHash H) sk idx msg).calls =
      40304471 + bottomTrials H (derivedSeed H sk) (derivedParam H sk) idx msg +
        topTrials H (derivedSeed H sk) (derivedParam H sk) idx := by
  rw [signWith_calls, signDerived_calls_ok H _ _ idx msg bottom top hb ht]
  omega

/-- Exact source sequencing needs the invariant only at the actual preceding result. -/
theorem sound_bind_at_result {α β : Type} {P : ByteArray → Prop} (x : Counted α)
    (f : α → Counted β) (hx : Sound P x) (hf : Sound P (f x.result)) :
    Sound P (x >>= f) := by
  constructor
  · simp only [Counted.bind, bind, List.length_append]
    rw [hx.1, hf.1]
  · intro input hi
    obtain h | h := List.mem_append.mp hi
    · exact hx.2 input h
    · exact hf.2 input h

/-- A stronger input predicate preserves source count/log agreement. -/
theorem sound_mono {α : Type} {P Q : ByteArray → Prop} {x : Counted α}
    (hx : Sound P x) (h : ∀ input, P input → Q input) : Sound Q x :=
  ⟨hx.1, fun input hi => h input (hx.2 input hi)⟩

/-- Mapping a source return value preserves its exact full invocation log. -/
theorem sound_map {α β : Type} {P : ByteArray → Prop} (x : Counted α) (f : α → β)
    (hx : Sound P x) : Sound P (f <$> x) := by
  exact sound_bind x (fun a => pure (f a)) hx (fun a => sound_pure P (f a))

/-- All source retry inputs are legal when the message/randomizer fibre is legal. -/
theorem sound_retry (H : ByteArray → Vector UInt8 32) {P : ByteArray → Prop}
    (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer)
    (c fuel : Nat)
    (hmsg : ∀ rho : Randomizer, P (thInput pp (addrMsg layer e) (msg ++ packBytes rho))) :
    Sound P (Internal.findCodeword (countedHash H) pp layer e msg base c fuel) := by
  induction fuel generalizing c with
  | zero => exact sound_pure P _
  | succ fuel ih =>
    rw [findCodeword_step]
    apply sound_bind
    · apply sound_map
      exact sound_th H pp (addrMsg layer e) _ (hmsg _)
    · intro outcome
      cases outcome with
      | none => exact ih (c + 1)
      | some x => exact sound_pure P _

/-- Source OTS signing retains its base, actual message trials, starts, and revealed chains. -/
theorem sound_otsSign (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (key : KeyCoordinate layer) (msg : ByteArray)
    {P : ByteArray → Prop}
    (hbase : P (thInput pp (addrRnd layer (UInt32.ofNat key.val)) (packBytes seed ++ msg)))
    (hmsg : ∀ rho : Randomizer,
      P (thInput pp (addrMsg layer (UInt32.ofNat key.val)) (msg ++ packBytes rho)))
    (htree : ∀ input, LegalInput seed pp layer input → P input) :
    Sound P (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer
      (UInt32.ofNat key.val) msg) := by
  apply sound_bind
  · apply sound_bind _ _ (sound_countedHash H _ hbase)
    intro full
    exact sound_pure P _
  · intro base
    apply sound_bind _ _ (sound_retry H pp layer _ msg base 0 MAX_RANDOMIZER_TRIALS hmsg)
    intro outcome
    cases outcome with
    | none => exact sound_pure P _
    | some pair =>
      rcases pair with ⟨rho, x⟩
      apply sound_bind _ _ (sound_mono (sound_chainStarts H seed pp layer key) htree)
      intro starts
      apply sound_bind
      · apply sound_ofFnInOrder
        intro i
        exact sound_mono (sound_chain H seed pp layer key i 0 x[i] (by simp) starts[i]) htree
      · intro values
        exact sound_pure P _

/-- Source layer signing retains its complete legal path after successful OTS signing. -/
theorem sound_signLayer (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (key : KeyCoordinate layer) (msg : ByteArray)
    {P : ByteArray → Prop}
    (hbase : P (thInput pp (addrRnd layer (UInt32.ofNat key.val)) (packBytes seed ++ msg)))
    (hmsg : ∀ rho : Randomizer,
      P (thInput pp (addrMsg layer (UInt32.ofNat key.val)) (msg ++ packBytes rho)))
    (htree : ∀ input, LegalInput seed pp layer input → P input) :
    Sound P (signLayer (countedHash H) pp (seedPrf (countedHash H) seed) layer key.val msg) := by
  apply sound_bind _ _ (sound_otsSign H seed pp layer key msg hbase hmsg htree)
  intro outcome
  cases outcome with
  | none => exact sound_pure P _
  | some pair =>
    rcases pair with ⟨rho, values⟩
    apply sound_bind _ _ (sound_mono (sound_path H seed pp layer key) htree)
    intro path
    exact sound_pure P _

/-- Typed full-hash purposes in complete source signing at one original index and message. -/
inductive SigningQuerySite (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) where
  /-- The raw seed's distinguished scheme-tag input. -/
  | schemeSeed
  /-- The parameter derivation uses the all-zero parameter and its distinguished address. -/
  | parameter
  /-- A legal bottom tree input, retaining global source coordinates. -/
  | bottomTree (site : QuerySite .bottom)
  /-- A legal top tree input in the single source top tree. -/
  | topTree (site : QuerySite .top)
  /-- The bottom base derivation includes the exact 32-byte source message. -/
  | bottomBase
  /-- The top base derivation includes the exact 16-byte recomputed bottom root. -/
  | topBase
  /-- A bottom trial includes the exact message and its explicit randomizer. -/
  | bottomTrial (rho : Randomizer)
  /-- A top trial includes the exact recomputed root and its explicit randomizer. -/
  | topTrial (rho : Randomizer)

/-- The exact complete source input at a typed signing purpose. -/
@[expose] def SigningQuerySite.input {H : ByteArray → Vector UInt8 32} {sk : SecretKey}
    {idx : LeafIndex} {msg : Message} : SigningQuerySite H sk idx msg → ByteArray
  | .schemeSeed => ByteArray.mk SEED_TAG.toArray ++ packBytes sk.seed
  | .parameter => thInput (Vector.replicate PUBLIC_PARAM_LEN 0) addrParam
      (packBytes (derivedSeed H sk) ++ .empty)
  | .bottomTree site => site.input (derivedSeed H sk) (derivedParam H sk)
  | .topTree site => site.input (derivedSeed H sk) (derivedParam H sk)
  | .bottomBase => thInput (derivedParam H sk) (addrRnd .bottom (UInt32.ofNat idx.toNat))
      (packBytes (derivedSeed H sk) ++ packBytes msg)
  | .topBase => thInput (derivedParam H sk) (addrRnd .top (UInt32.ofNat (Xmss.bottomTree idx)))
      (packBytes (derivedSeed H sk) ++
        packBytes (bottomRoot H (derivedSeed H sk) (derivedParam H sk) idx).result)
  | .bottomTrial rho => thInput (derivedParam H sk) (addrMsg .bottom (UInt32.ofNat idx.toNat))
      (packBytes msg ++ packBytes rho)
  | .topTrial rho => thInput (derivedParam H sk) (addrMsg .top (UInt32.ofNat (Xmss.bottomTree idx)))
      (packBytes (bottomRoot H (derivedSeed H sk) (derivedParam H sk) idx).result ++ packBytes rho)

/-- A complete source signing input has an exact typed purpose witness. -/
@[expose] def SigningInput (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) (input : ByteArray) : Prop :=
  ∃ site : SigningQuerySite H sk idx msg, site.input = input

/-- The complete source bottom layer keeps all calls in the exact message/index fibre. -/
theorem sound_bottomLayer (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) : Sound (SigningInput H sk idx msg)
      (bottomLayer H (derivedSeed H sk) (derivedParam H sk) idx msg) := by
  apply sound_signLayer H (derivedSeed H sk) (derivedParam H sk) .bottom (leafIndexEquiv idx)
  · exact ⟨.bottomBase, rfl⟩
  · intro rho
    exact ⟨.bottomTrial rho, rfl⟩
  · intro input hi
    obtain ⟨site, rfl⟩ := hi
    exact ⟨.bottomTree site, rfl⟩

/-- The complete source top layer signs the exact recomputed root, with its original tree index. -/
theorem sound_topLayer (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) : Sound (SigningInput H sk idx msg)
      (topLayer H (derivedSeed H sk) (derivedParam H sk) idx) := by
  apply sound_signLayer H (derivedSeed H sk) (derivedParam H sk) .top
    ⟨bottomTree idx, bottomTree_lt idx⟩
  · exact ⟨.topBase, rfl⟩
  · intro rho
    exact ⟨.topTrial rho, rfl⟩
  · intro input hi
    obtain ⟨site, rfl⟩ := hi
    exact ⟨.topTree site, rfl⟩

/-- The complete source's recomputed bottom root retains every full subtree query. -/
theorem sound_signing_bottomRoot (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) : Sound (SigningInput H sk idx msg)
      (bottomRoot H (derivedSeed H sk) (derivedParam H sk) idx) := by
  apply sound_mono (sound_bottom_root H (derivedSeed H sk) (derivedParam H sk) idx)
  intro input hi
  obtain ⟨site, rfl⟩ := hi
  exact ⟨.bottomTree site, rfl⟩

/-- The actual derived-seed source signer logs only fully typed source purposes. -/
theorem sound_signDerived (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) : Sound (SigningInput H sk idx msg)
      (signDerived (countedHash H) (seedPrf (countedHash H) (derivedSeed H sk))
        (derivedParam H sk) idx msg) := by
  apply sound_bind _ _ (sound_bottomLayer H sk idx msg)
  intro outcome
  cases outcome with
  | error err => exact sound_pure _ _
  | ok bottom =>
    apply sound_bind_at_result _ _ (sound_pure _ bottom)
    apply sound_bind_at_result _ _ (sound_signing_bottomRoot H sk idx msg)
    apply sound_bind _ _ (sound_topLayer H sk idx msg)
    intro topOutcome
    cases topOutcome with
    | error err => exact sound_pure _ _
    | ok top =>
      apply sound_bind_at_result _ _ (sound_pure _ top)
      exact sound_pure _ _

/-- Every invocation made by complete raw-key source signing has its typed purpose witness. -/
theorem sound_signWith (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) :
    Sound (SigningInput H sk idx msg) (signWith (countedHash H) sk idx msg) := by
  apply sound_bind_at_result _ _ (sound_countedHash H _ ⟨.schemeSeed, rfl⟩)
  apply sound_bind_at_result
  · apply sound_bind _ _ (sound_countedHash H _ ⟨.parameter, rfl⟩)
    intro full
    exact sound_pure _ _
  · exact sound_signDerived H sk idx msg

/-- The complete source success log retains every counted invocation, including repetitions. -/
theorem signWith_inputs_length_ok (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) (bottom top : LayerSignature)
    (hb : (bottomLayer H (derivedSeed H sk) (derivedParam H sk) idx msg).result = .ok bottom)
    (ht : (topLayer H (derivedSeed H sk) (derivedParam H sk) idx).result = .ok top) :
    (signWith (countedHash H) sk idx msg).inputs.length =
      40304471 + bottomTrials H (derivedSeed H sk) (derivedParam H sk) idx msg +
        topTrials H (derivedSeed H sk) (derivedParam H sk) idx := by
  rw [← (sound_signWith H sk idx msg).1, signWith_calls_ok H sk idx msg bottom top hb ht]

/-- Complete source signing has a finite invocation bound across failure and success branches. -/
theorem signWith_calls_le (H : ByteArray → Vector UInt8 32) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) :
    (signWith (countedHash H) sk idx msg).calls ≤ 40304471 + 2 * 2 ^ 32 := by
  have hbnd : bottomTrials H (derivedSeed H sk) (derivedParam H sk) idx msg ≤ 2 ^ 32 :=
    trials_le H _ _ .bottom _ _
  cases hb : (bottomLayer H (derivedSeed H sk) (derivedParam H sk) idx msg).result with
  | error err =>
    rw [signWith_calls_bottom_error H sk idx msg err hb]
    omega
  | ok bottom =>
    have htnd : topTrials H (derivedSeed H sk) (derivedParam H sk) idx ≤ 2 ^ 32 :=
      trials_le H _ _ .top _ _
    cases ht : (topLayer H (derivedSeed H sk) (derivedParam H sk) idx).result with
    | error err =>
      rw [signWith_calls_top_error H sk idx msg bottom err hb ht]
      omega
    | ok top =>
      rw [signWith_calls_ok H sk idx msg bottom top hb ht]
      omega

end SigningReachability

end EthereumXMSSHypertree

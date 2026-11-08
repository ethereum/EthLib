module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Count
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.GraphView.Cost
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.CostProgram

/-!
# Proofs: the hash calls of one signing request, under one answer function

Under one answer function, a signing request costs the model at most what it costs EthLib.

Only the counter searches depend on the answers, and both signers search the same counters.

Before the layers, EthLib makes 337636 calls and the model 73709.

- EthLib derives `PK.seed` and `SK.prf` again and rebuilds the top tree: `2 + 264191` calls.
- Both make `PRF_msg` and `H_msg`, 3 calls, and the model tests its randomizer with one more.
- EthLib's FORS openings make 73440 calls.
  The model's make as many, then 265 to recover the FORS public key.

Both signers then sign the layers from the bottom up, and stop at the first failed search.

A layer of EthLib makes the calls of its message, of its one-time signature and of its path.

A layer of the model makes the calls of its one-time signature and of its path.

Below the top it then recovers the root of its tree, 74 calls.

The one-time signatures sign the same message, so they make the same calls and both succeed or fail.

The paths make the same calls, and EthLib's message, at least 66047 calls, covers the recovery.

So a budget of hash calls against EthLib is a budget against the model.
-/

@[expose] public section

/-! ## Counts of the shared constructions -/

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec)
open SphincsSecurity.Security.Prefix (hashCalls hashCalls_bind hashCalls_pure)

variable (f : QueryImpl HashSpec Id)

/-- A query to the oracle is one hash call. -/
theorem hashCalls_queryH (input : ByteArray) :
    hashCalls f (HashSig.queryH (m := OracleComp HashSpec) input) = 1 := by
  rw [HashSig.queryH, hashCalls_map]
  exact SphincsSecurity.Security.Prefix.hashCalls_oracleHash f _

/-- A vector computed in order makes the calls of its entries. -/
theorem hashCalls_ofFnInOrder {α : Type} :
    ∀ (n : Nat) (g : Fin n → OracleComp HashSpec α),
      hashCalls f (HashSig.ofFnInOrder n g) = ∑ i, hashCalls f (g i)
  | 0, _ => rfl
  | n + 1, g => by
    simp only [HashSig.ofFnInOrder, hashCalls_bind, hashCalls_pure, Nat.add_zero,
      hashCalls_ofFnInOrder n, Fin.sum_univ_succ]

/-- A vector computed in order makes `n * c` calls if each of its `n` entries makes `c`. -/
theorem hashCalls_ofFnInOrder_const {α : Type} (n c : Nat) (g : Fin n → OracleComp HashSpec α)
    (hg : ∀ i, hashCalls f (g i) = c) :
    hashCalls f (HashSig.ofFnInOrder n g) = n * c := by
  simp only [hashCalls_ofFnInOrder, hg, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

/-- A node of height `level` makes `(c + 1) * 2^level - 1` calls if each leaf makes `c`.

That is `c` calls for each of its `2^level` leaves and one for each of its `2^level - 1` hashes. -/
theorem hashCalls_node {α : Type} (hash : Nat → Nat → α → α → OracleComp HashSpec α)
    (leaves : Nat → OracleComp HashSpec α) (c : Nat)
    (hhash : ∀ level j left right, hashCalls f (hash level j left right) = 1)
    (hleaf : ∀ j, hashCalls f (leaves j) = c) :
    ∀ level j, hashCalls f (Merkle.node hash leaves level j) = (c + 1) * 2 ^ level - 1
  | 0, j => by
    rw [Merkle.node, hleaf, Nat.pow_zero, Nat.mul_one, Nat.add_sub_cancel]
  | level + 1, j => by
    rw [Merkle.node, hashCalls_bind, hashCalls_bind, hhash,
      hashCalls_node hash leaves c hhash hleaf level,
      hashCalls_node hash leaves c hhash hleaf level,
      Nat.pow_succ, ← Nat.mul_assoc]
    have hpos : 1 ≤ (c + 1) * 2 ^ level := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega

/-- The siblings of `n` nodes from `(level, j)` up make one whole node each. -/
theorem hashCalls_siblings {α : Type} (hash : Nat → Nat → α → α → OracleComp HashSpec α)
    (leaves : Nat → OracleComp HashSpec α) (c : Nat)
    (hhash : ∀ level j left right, hashCalls f (hash level j left right) = 1)
    (hleaf : ∀ j, hashCalls f (leaves j) = c) :
    ∀ level j n, hashCalls f (Merkle.siblings hash leaves level j n) =
      ∑ i : Fin n, ((c + 1) * 2 ^ (level + i.val) - 1)
  | _, _, 0 => rfl
  | level, j, n + 1 => by
    rw [Merkle.siblings, hashCalls_bind, hashCalls_bind, hashCalls_pure, Nat.add_zero,
      hashCalls_node f hash leaves c hhash hleaf,
      hashCalls_siblings hash leaves c hhash hleaf (level + 1) (j / 2) n, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

/-- The calls of a path of height `h` in a tree whose leaves make `c` calls each.

The path computes one whole node of each height below `h`. -/
def pathCalls (c h : Nat) : Nat :=
  ∑ z : Fin h, ((c + 1) * 2 ^ z.val - 1)

/-- A path of height `h` makes `(c + 1) * (2^h - 1) - h` calls. -/
theorem pathCalls_add (c h : Nat) : pathCalls c h + h = (c + 1) * (2 ^ h - 1) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [pathCalls, Fin.sum_univ_castSucc] at *
    simp only [Fin.val_castSucc, Fin.val_last] at *
    have hpos : 1 ≤ (c + 1) * 2 ^ h := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hsplit : (c + 1) * (2 ^ (h + 1) - 1) = (c + 1) * (2 ^ h - 1) + (c + 1) * 2 ^ h := by
      rw [← Nat.mul_add]
      congr 1
      have := Nat.one_le_two_pow (n := h)
      rw [Nat.pow_succ]
      omega
    omega

/-- The path of leaf `j` in a tree of height `h` makes the calls of one whole node per height. -/
theorem hashCalls_path {α : Type} (hash : Nat → Nat → α → α → OracleComp HashSpec α)
    (leaves : Nat → OracleComp HashSpec α) (c : Nat)
    (hhash : ∀ level j left right, hashCalls f (hash level j left right) = 1)
    (hleaf : ∀ j, hashCalls f (leaves j) = c) (h j : Nat) :
    hashCalls f (Merkle.path hash leaves h j) = pathCalls c h := by
  rw [Merkle.path, hashCalls_siblings f hash leaves c hhash hleaf, pathCalls]
  simp only [Nat.zero_add]

/-- A chain walk of `steps` steps makes `steps` calls if each step makes one. -/
theorem hashCalls_wotsChain {β : Type} {n : Nat} (step : Fin n → β → OracleComp HashSpec β)
    (hstep : ∀ k value, hashCalls f (step k value) = 1) (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ n) (value : β),
      hashCalls f (Wots.chain step start steps h value) = steps
  | 0, _, _ => hashCalls_pure f _
  | s + 1, h, value => by
    rw [Wots.chain, hashCalls_bind, hashCalls_wotsChain step hstep start s, hstep]

/-! ## Counter searches -/

/-- The trials that a search from trial `c` makes, at most `fuel` of them.

`ok` tells which trials pass, and the search stops at the first one that passes. -/
def searchCalls (ok : Nat → Bool) (c : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 => if ok c then 1 else searchCalls ok (c + 1) fuel + 1

/-- Whether a search from trial `c`, with at most `fuel` trials, finds a trial that passes. -/
def searchFinds (ok : Nat → Bool) (c : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 => ok c || searchFinds ok (c + 1) fuel

/-- A search makes at most `fuel` trials. -/
theorem searchCalls_le (ok : Nat → Bool) : ∀ (c fuel : Nat), searchCalls ok c fuel ≤ fuel
  | _, 0 => le_rfl
  | c, fuel + 1 => by
    have := searchCalls_le ok (c + 1) fuel
    rw [searchCalls]
    split <;> omega

/-- A search whose first passing trial is `c + k`, with `k < fuel`, makes `k + 1` trials. -/
theorem searchCalls_of_least (ok : Nat → Bool) :
    ∀ (k c fuel : Nat), k < fuel → ok (c + k) = true → (∀ i < k, ok (c + i) = false) →
      searchCalls ok c fuel = k + 1
  | _, _, 0, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | 0, c, fuel + 1, _, hok, _ => by
    have hc : ok c = true := hok
    simp only [searchCalls, hc, ↓reduceIte]
  | k + 1, c, fuel + 1, hk, hok, hlt => by
    have hc : ok c = false := hlt 0 (Nat.succ_pos k)
    have hshift : c + 1 + k = c + (k + 1) := by omega
    have ih := searchCalls_of_least ok k (c + 1) fuel (by omega) (by rw [hshift]; exact hok)
      (fun i hi => by
        have hi' : c + 1 + i = c + (i + 1) := by omega
        rw [hi']
        exact hlt (i + 1) (by omega))
    simp only [searchCalls, hc, Bool.false_eq_true, ↓reduceIte, ih]

/-- A search with no passing trial among its `fuel` trials makes all `fuel` of them. -/
theorem searchCalls_of_none (ok : Nat → Bool) :
    ∀ (c fuel : Nat), (∀ i < fuel, ok (c + i) = false) → searchCalls ok c fuel = fuel
  | _, 0, _ => rfl
  | c, fuel + 1, h => by
    have hc : ok c = false := h 0 (Nat.succ_pos fuel)
    have ih := searchCalls_of_none ok (c + 1) fuel (fun i hi => by
      have hi' : c + 1 + i = c + (i + 1) := by omega
      rw [hi']
      exact h (i + 1) (by omega))
    simp only [searchCalls, hc, Bool.false_eq_true, ↓reduceIte, ih]

/-- A search finds a trial exactly when one of its `fuel` trials passes. -/
theorem searchFinds_iff (ok : Nat → Bool) :
    ∀ (c fuel : Nat), searchFinds ok c fuel = true ↔ ∃ i < fuel, ok (c + i) = true
  | _, 0 => by simp [searchFinds]
  | c, fuel + 1 => by
    rw [searchFinds, Bool.or_eq_true, searchFinds_iff ok (c + 1) fuel]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨0, Nat.succ_pos fuel, h⟩
      · have hi' : c + 1 + i = c + (i + 1) := by omega
        exact ⟨i + 1, by omega, by rw [← hi']; exact h⟩
    · rintro ⟨i, hi, h⟩
      cases i with
      | zero => exact Or.inl h
      | succ i =>
        have hi' : c + 1 + i = c + (i + 1) := by omega
        exact Or.inr ⟨i, by omega, by rw [hi']; exact h⟩

/-- A search makes one call per trial, up to the first that passes, if each test makes one. -/
theorem hashCalls_findFirst {κ β : Type} (trial : Nat → κ)
    (test : κ → OracleComp HashSpec (Option β)) (htest : ∀ k, hashCalls f (test k) = 1) :
    ∀ (c fuel : Nat), hashCalls f (Wots.findFirst trial test c fuel) =
      searchCalls (fun c => (evalWithAnswerFn f (test (trial c))).isSome) c fuel
  | _, 0 => hashCalls_pure f _
  | c, fuel + 1 => by
    rw [Wots.findFirst, hashCalls_bind, htest, searchCalls]
    cases h : evalWithAnswerFn f (test (trial c)) with
    | none =>
      simp only [hashCalls_findFirst trial test htest (c + 1) fuel, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte]
      omega
    | some x =>
      simp only [hashCalls_pure, Option.isSome_some, ↓reduceIte]

/-- A search returns a trial exactly when one of its trials passes. -/
theorem isSome_findFirst {κ β : Type} (trial : Nat → κ)
    (test : κ → OracleComp HashSpec (Option β)) :
    ∀ (c fuel : Nat), (evalWithAnswerFn f (Wots.findFirst trial test c fuel)).isSome =
      searchFinds (fun c => (evalWithAnswerFn f (test (trial c))).isSome) c fuel
  | _, 0 => rfl
  | c, fuel + 1 => by
    rw [Wots.findFirst, evalWithAnswerFn_bind, searchFinds]
    cases h : evalWithAnswerFn f (test (trial c)) with
    | none =>
      simp only [isSome_findFirst trial test (c + 1) fuel, Option.isSome_none, Bool.false_or]
    | some x =>
      simp only [evalWithAnswerFn_pure, Option.isSome_some, Bool.true_or]

/-- The result of a search is the result of the test of the trial it returns. -/
theorem eval_test_of_findFirst {κ β : Type} (trial : Nat → κ)
    (test : κ → OracleComp HashSpec (Option β)) :
    ∀ (c fuel : Nat) (k : κ) (x : β),
      evalWithAnswerFn f (Wots.findFirst trial test c fuel) = some (k, x) →
        evalWithAnswerFn f (test k) = some x
  | _, 0, _, _, h => by simp [Wots.findFirst] at h
  | c, fuel + 1, k, x, h => by
    rw [Wots.findFirst, evalWithAnswerFn_bind] at h
    cases ht : evalWithAnswerFn f (test (trial c)) with
    | none =>
      rw [ht] at h
      exact eval_test_of_findFirst trial test (c + 1) fuel k x h
    | some y =>
      rw [ht, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ht

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge

/-! ## The calls of EthLib's algorithms -/

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec)
open SphincsSecurity.Security.Prefix (hashCalls hashCalls_bind hashCalls_pure)

variable (f : QueryImpl HashSpec Id) (H : ByteArray → OracleComp HashSpec (Vector UInt8 32))
  (hH : ∀ input, hashCalls f (H input) = 1)
  (secrets : Prf (OracleComp HashSpec)) (hsecrets : ∀ adrs, hashCalls f (secrets adrs) = 1)

/-! ### Tweakable hashes -/

include hH

/-- A tweakable hash is one call. -/
theorem hashCalls_th (pkSeed : PkSeed) (adrs : Adrs) (payload : ByteArray) :
    hashCalls f (th H pkSeed adrs payload) = 1 := by
  rw [th, hashCalls_bind, hH, hashCalls_pure]

/-- A `PRF` call is one tweakable hash. -/
theorem hashCalls_prf (pkSeed : PkSeed) (seed : Seed) (adrs : Adrs) :
    hashCalls f (prf H pkSeed seed adrs) = 1 :=
  hashCalls_th f H hH _ _ _

/-! ### WOTS+C -/

omit hH in
include hsecrets in
/-- The 64 chain starts make one `PRF` call each. -/
theorem hashCalls_chainStarts (key : OtsKey) : hashCalls f (chainStarts secrets key) = V := by
  rw [chainStarts, hashCalls_ofFnInOrder_const f V 1 _ fun _ => hsecrets _, Nat.mul_one]

/-- A chain walk of `steps` steps makes `steps` calls. -/
theorem hashCalls_chain (pkSeed : PkSeed) (key : OtsKey) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    hashCalls f (chain H pkSeed key i start steps h value) = steps :=
  hashCalls_wotsChain f _ (fun _ _ => hashCalls_th f H hH _ _ _) start steps _ value

include hsecrets in
/-- A one-time key's leaf makes 257 calls: 64 `PRF` calls, `64 * 3` chain steps and one `T_v`. -/
theorem hashCalls_otsPublicLeaf (pkSeed : PkSeed) (key : OtsKey) :
    hashCalls f (otsPublicLeaf H pkSeed secrets key) = 257 := by
  rw [otsPublicLeaf, hashCalls_bind, hashCalls_chainStarts f secrets hsecrets, hashCalls_bind,
    hashCalls_ofFnInOrder_const f V (CHAIN_LENGTH - 1) _
      fun i => hashCalls_chain f H hH _ _ _ _ _ _ _, otsLeafHash, hashCalls_th f H hH]
  decide

/-- An encoding is one call. -/
theorem hashCalls_encode (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (counter : UInt32) :
    hashCalls f (encode H pkSeed key msg counter) = 1 := by
  rw [encode, hashCalls_map, hashCalls_th f H hH]

omit hH

/-- Whether counter `c` gives a codeword for the message, under `f`. -/
def encodes (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (c : Nat) : Bool :=
  (evalWithAnswerFn f (encode H pkSeed key msg (UInt32.ofNat c))).isSome

include hH in
/-- The counter search makes one call per counter it tries, up to the first one that encodes. -/
theorem hashCalls_findCounter (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (c fuel : Nat) :
    hashCalls f (Internal.findCounter H pkSeed key msg c fuel) =
      searchCalls (encodes f H pkSeed key msg) c fuel :=
  hashCalls_findFirst f _ _ (hashCalls_encode f H hH pkSeed key msg) c fuel

/-- The counter search finds a counter exactly when one of the counters it tries encodes. -/
theorem isSome_findCounter (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (c fuel : Nat) :
    (evalWithAnswerFn f (Internal.findCounter H pkSeed key msg c fuel)).isSome =
      searchFinds (encodes f H pkSeed key msg) c fuel :=
  isSome_findFirst f _ _ c fuel

include hH in
/-- The search makes `c + 1` calls if `c < 2^32` is the least counter that encodes. -/
theorem hashCalls_findCounter_of_least (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (c : Nat)
    (hc : c < MAX_COUNTER_TRIALS) (hok : encodes f H pkSeed key msg c = true)
    (hlt : ∀ i < c, encodes f H pkSeed key msg i = false) :
    hashCalls f (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS) = c + 1 := by
  rw [hashCalls_findCounter f H hH]
  exact searchCalls_of_least _ c 0 _ hc (by rw [Nat.zero_add]; exact hok)
    (fun i hi => by rw [Nat.zero_add]; exact hlt i hi)

include hH in
/-- The search makes `2^32` calls if no counter below `2^32` encodes. -/
theorem hashCalls_findCounter_of_none (pkSeed : PkSeed) (key : OtsKey) (msg : Digest)
    (h : ∀ i < MAX_COUNTER_TRIALS, encodes f H pkSeed key msg i = false) :
    hashCalls f (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS) =
      MAX_COUNTER_TRIALS := by
  rw [hashCalls_findCounter f H hH]
  exact searchCalls_of_none _ 0 _ (fun i hi => by rw [Nat.zero_add]; exact h i hi)

/-- The digits of the codeword that the counter search returns sum to the target. -/
theorem sum_of_findCounter (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (c fuel : Nat)
    (counter : UInt32) (x : Codeword)
    (h : evalWithAnswerFn f (Internal.findCounter H pkSeed key msg c fuel) = some (counter, x)) :
    ∑ i : Fin V, (x[i] : Nat) = TARGET_SUM := by
  have he := eval_test_of_findFirst f _ _ c fuel counter x h
  rw [encode, evalWithAnswerFn_map] at he
  exact sum_of_codeword he

include hH hsecrets in
/-- A one-time signature makes the calls of its search, and 192 more if the search finds a counter.

They are the 64 `PRF` calls of the chain starts and the 128 chain steps to the codeword. -/
theorem hashCalls_otsSign (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) :
    hashCalls f (otsSign H pkSeed secrets key msg) =
      hashCalls f (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS) +
        if (evalWithAnswerFn f
            (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS)).isSome then
          V + TARGET_SUM
        else 0 := by
  rw [otsSign, hashCalls_bind]
  cases hs : evalWithAnswerFn f (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS) with
  | none =>
    simp only [hashCalls_pure, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  | some found =>
    obtain ⟨counter, x⟩ := found
    have hsum := sum_of_findCounter f H pkSeed key msg 0 MAX_COUNTER_TRIALS counter x hs
    simp only [Option.isSome_some, ↓reduceIte]
    rw [hashCalls_bind, hashCalls_chainStarts f secrets hsecrets, hashCalls_bind,
      hashCalls_ofFnInOrder, hashCalls_pure, Nat.add_zero]
    simp only [hashCalls_chain f H hH]
    rw [hsum]

/-- A one-time signature is found exactly when its counter search finds a counter. -/
theorem isSome_otsSign (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) :
    (evalWithAnswerFn f (otsSign H pkSeed secrets key msg)).isSome =
      (evalWithAnswerFn f (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS)).isSome := by
  rw [otsSign, evalWithAnswerFn_bind]
  cases evalWithAnswerFn f (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS) with
  | none => rfl
  | some found =>
    obtain ⟨counter, x⟩ := found
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.isSome_some]

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec)
open SphincsSecurity.Security.Prefix (hashCalls hashCalls_bind hashCalls_pure)

variable (f : QueryImpl HashSpec Id) (H : ByteArray → OracleComp HashSpec (Vector UInt8 32))
  (hH : ∀ input, hashCalls f (H input) = 1)
  (secrets : Prf (OracleComp HashSpec)) (hsecrets : ∀ adrs, hashCalls f (secrets adrs) = 1)

/-! ### The hypertree -/

include hH hsecrets

/-- A leaf of a layer tree is a one-time key's leaf, 257 calls. -/
theorem hashCalls_leaves (pkSeed : PkSeed) (layer : Layer) (tree e : Nat) :
    hashCalls f (leaves H pkSeed secrets layer tree e) = 257 :=
  hashCalls_otsPublicLeaf f H hH secrets hsecrets pkSeed _

omit hsecrets in
/-- A node hash of a layer tree is one call. -/
theorem hashCalls_nodeHash (pkSeed : PkSeed) (layer : Layer) (tree z j : Nat)
    (left right : Digest) : hashCalls f (nodeHash H pkSeed layer tree z j left right) = 1 :=
  hashCalls_th f H hH _ _ _

/-- A node of height `z` of a layer tree makes `258 * 2^z - 1` calls. -/
theorem hashCalls_treeNode (pkSeed : PkSeed) (layer : Layer) (tree z j : Nat) :
    hashCalls f (node H pkSeed secrets layer tree z j) = 258 * 2 ^ z - 1 :=
  hashCalls_node f _ _ 257 (hashCalls_nodeHash f H hH pkSeed layer tree)
    (hashCalls_leaves f H hH secrets hsecrets pkSeed layer tree) z j

/-- The root of a layer tree of height `h` makes `258 * 2^h - 1` calls. -/
theorem hashCalls_treeRoot (pkSeed : PkSeed) (layer : Layer) (tree : Nat) :
    hashCalls f (treeRoot H pkSeed secrets layer tree) = 258 * 2 ^ layer.height - 1 :=
  hashCalls_node f _ _ 257 (hashCalls_nodeHash f H hH pkSeed layer tree)
    (hashCalls_leaves f H hH secrets hsecrets pkSeed layer tree) _ 0

/-- The path of a key in a layer tree builds one whole node of each height below the root. -/
theorem hashCalls_treePath (pkSeed : PkSeed) (layer : Layer) (tree e : Nat) :
    hashCalls f (path H pkSeed secrets layer tree e) = pathCalls 257 layer.height :=
  hashCalls_path f _ _ 257 (hashCalls_nodeHash f H hH pkSeed layer tree)
    (hashCalls_leaves f H hH secrets hsecrets pkSeed layer tree) _ _

omit hH hsecrets in
/-- The trees of the bottom, middle and top layers make 66047, 66047 and 264191 calls. -/
theorem treeCalls_eq : 258 * 2 ^ Layer.bottom.height - 1 = 66047 ∧
    258 * 2 ^ Layer.middle.height - 1 = 66047 ∧ 258 * 2 ^ Layer.top.height - 1 = 264191 := by
  decide

omit hH hsecrets in
/-- The paths of the bottom, middle and top layers make 65782, 65782 and 263924 calls. -/
theorem pathCalls_layers : pathCalls 257 Layer.bottom.height = 65782 ∧
    pathCalls 257 Layer.middle.height = 65782 ∧ pathCalls 257 Layer.top.height = 263924 := by
  decide

/-! ### FORS -/

omit hH in
/-- A FORS secret is one `PRF` call. -/
theorem hashCalls_forsSecret (idx : Nat) (kappa : Fin FORS_TREES) (s : Nat) :
    hashCalls f (forsSecret secrets idx kappa s) = 1 :=
  hsecrets _

/-- A FORS leaf makes two calls: its secret, then `F` of it. -/
theorem hashCalls_forsLeaves (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES) (s : Nat) :
    hashCalls f (forsLeaves H pkSeed secrets idx kappa s) = 2 := by
  rw [forsLeaves, hashCalls_bind, hashCalls_forsSecret f secrets hsecrets, forsLeafHash,
    hashCalls_th f H hH]

omit hsecrets in
/-- A FORS node hash is one call. -/
theorem hashCalls_forsNodeHash (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (z j : Nat) (left right : Digest) :
    hashCalls f (forsNodeHash H pkSeed idx kappa z j left right) = 1 :=
  hashCalls_th f H hH _ _ _

/-- A FORS node of height `z` makes `3 * 2^z - 1` calls. -/
theorem hashCalls_forsNode (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES) (z j : Nat) :
    hashCalls f (forsNode H pkSeed secrets idx kappa z j) = 3 * 2 ^ z - 1 :=
  hashCalls_node f _ _ 2 (hashCalls_forsNodeHash f H hH pkSeed idx kappa)
    (hashCalls_forsLeaves f H hH secrets hsecrets pkSeed idx kappa) z j

/-- The root of a FORS tree makes `3 * 2^10 - 1 = 3071` calls. -/
theorem hashCalls_forsRoot (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES) :
    hashCalls f (forsRoot H pkSeed secrets idx kappa) = 3 * 2 ^ FORS_HEIGHT - 1 :=
  hashCalls_node f _ _ 2 (hashCalls_forsNodeHash f H hH pkSeed idx kappa)
    (hashCalls_forsLeaves f H hH secrets hsecrets pkSeed idx kappa) _ 0

/-- The FORS key makes the calls of its 24 roots and one `T_k`. -/
theorem hashCalls_forsKey (pkSeed : PkSeed) (idx : Nat) :
    hashCalls f (forsKey H pkSeed secrets idx) = FORS_TREES * (3 * 2 ^ FORS_HEIGHT - 1) + 1 := by
  rw [forsKey, hashCalls_bind,
    hashCalls_ofFnInOrder_const f _ _ _ (hashCalls_forsRoot f H hH secrets hsecrets pkSeed idx),
    forsPkFromRoots, hashCalls_th f H hH]

/-- The opening of a FORS tree makes its secret and one whole node of each height below the root. -/
theorem hashCalls_treeOpen (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) :
    hashCalls f (treeOpen H pkSeed secrets idx kappa s) = 1 + pathCalls 2 FORS_HEIGHT := by
  rw [treeOpen, hashCalls_bind, hashCalls_forsSecret f secrets hsecrets, hashCalls_bind,
    hashCalls_path f _ _ 2 (hashCalls_forsNodeHash f H hH pkSeed idx kappa)
      (hashCalls_forsLeaves f H hH secrets hsecrets pkSeed idx kappa),
    hashCalls_pure, Nat.add_zero]

/-- The FORS openings make the calls of 24 tree openings. -/
theorem hashCalls_forsSign (pkSeed : PkSeed) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    hashCalls f (forsSign H pkSeed secrets idx leaves) =
      FORS_TREES * (1 + pathCalls 2 FORS_HEIGHT) :=
  hashCalls_ofFnInOrder_const f _ _ _ fun kappa =>
    hashCalls_treeOpen f H hH secrets hsecrets pkSeed idx kappa _

omit hH hsecrets in
/-- The FORS key makes `24 * (1024 + 1024 + 1023) + 1 = 73705` calls, and the openings 73440. -/
theorem forsCalls_eq : FORS_TREES * (3 * 2 ^ FORS_HEIGHT - 1) + 1 = 73705 ∧
    FORS_TREES * (1 + pathCalls 2 FORS_HEIGHT) = 73440 := by
  decide

/-! ### The randomizer and the digest -/

omit hsecrets

/-- `PRF_msg` is one call. -/
theorem hashCalls_prfMsg (skPrf : HashOutput) (optRand : PkSeed) (msg : Message) :
    hashCalls f (prfMsg H skPrf optRand msg) = 1 :=
  -- The randomizer has the length of a digest, but under another name.
  (hashCalls_bind f (H _) _).trans (by rw [hH]; rfl)

/-- `H_msg` makes two calls. -/
theorem hashCalls_hMsg (rho : Randomizer) (pkSeed : PkSeed) (pkRoot : Digest) (msg : Message) :
    hashCalls f (hMsg H rho pkSeed pkRoot msg) = DIGEST_CALLS := by
  simp only [hMsg, hashCalls_bind, hashCalls_ofFnInOrder_const f _ 1 _ fun _ => hH _,
    hashCalls_pure, Nat.mul_one, Nat.add_zero]

/-! ### Key generation -/

/-- The key expansion makes two calls: `PK.seed`, then `SK.prf`. -/
theorem hashCalls_expandKey (seed : Seed) : hashCalls f (expandKey H seed) = 2 := by
  simp only [expandKey, hashCalls_bind, hH, hashCalls_pure]

include hsecrets in
/-- The public key makes the calls of the top tree, `258 * 2^10 - 1`. -/
theorem hashCalls_publicKeyOf (pkSeed : PkSeed) :
    hashCalls f (publicKeyOf H pkSeed secrets) = 258 * 2 ^ TOP_HEIGHT - 1 := by
  rw [publicKeyOf, hashCalls_bind, hashCalls_treeRoot f H hH secrets hsecrets, hashCalls_pure,
    Nat.add_zero]
  rfl

omit hH in
/-- The public key holds the seed it is built from. -/
theorem pkSeed_publicKeyOf (pkSeed : PkSeed) :
    (evalWithAnswerFn f (publicKeyOf H pkSeed secrets)).pkSeed = pkSeed := by
  rw [publicKeyOf, evalWithAnswerFn_bind, evalWithAnswerFn_pure]

/-- Key generation makes the 2 calls of the key expansion and the calls of the top tree. -/
theorem hashCalls_keyGenWith (seed : Seed) :
    hashCalls f (keyGenWith H seed) = 2 + (258 * 2 ^ TOP_HEIGHT - 1) := by
  rw [keyGenWith, hashCalls_bind, hashCalls_expandKey f H hH, hashCalls_bind,
    hashCalls_publicKeyOf f H hH _ (hashCalls_prf f H hH _ _), hashCalls_pure, Nat.add_zero]

omit hH in
/-- Key generation makes `2 + (258 * 2^10 - 1) = 264193` calls. -/
theorem keyGenCalls_eq : 2 + (258 * 2 ^ TOP_HEIGHT - 1) = 264193 := by
  decide

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge

/-! ## The calls of one signing request -/

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec)
open SphincsSecurity.Security.Prefix (hashCalls hashCalls_bind hashCalls_pure)

variable (f : QueryImpl HashSpec Id) (H : ByteArray → OracleComp HashSpec (Vector UInt8 32))
  (hH : ∀ input, hashCalls f (H input) = 1)
  (secrets : Prf (OracleComp HashSpec)) (hsecrets : ∀ adrs, hashCalls f (secrets adrs) = 1)

/-! ### One layer -/

/-- The calls of the message that the key of a layer signs.

The bottom key signs the FORS key, and a higher key signs the root of the tree below it. -/
def messageCalls : Layer → Nat
  | .bottom => FORS_TREES * (3 * 2 ^ FORS_HEIGHT - 1) + 1
  | .middle => 258 * 2 ^ Layer.bottom.height - 1
  | .top => 258 * 2 ^ Layer.middle.height - 1

/-- The messages of the bottom, middle and top keys make 73705, 66047 and 66047 calls. -/
theorem messageCalls_eq : messageCalls .bottom = 73705 ∧ messageCalls .middle = 66047 ∧
    messageCalls .top = 66047 := by
  decide

include hH hsecrets in
/-- The message of a layer's key makes the calls of the FORS key or of the tree below. -/
theorem hashCalls_layerMessage (pkSeed : PkSeed) (layer : Layer) (idx : Nat) :
    hashCalls f (layerMessage H pkSeed secrets layer idx) = messageCalls layer := by
  cases layer with
  | bottom => exact hashCalls_forsKey f H hH secrets hsecrets pkSeed idx
  | middle => exact hashCalls_treeRoot f H hH secrets hsecrets pkSeed .bottom _
  | top => exact hashCalls_treeRoot f H hH secrets hsecrets pkSeed .middle _

include hH hsecrets in
/-- A layer makes the calls of its one-time signature, and those of the path if it signs. -/
theorem hashCalls_signLayer (pkSeed : PkSeed) (layer : Layer) (idx : Nat) (msg : Digest) :
    hashCalls f (signLayer H pkSeed secrets layer idx msg) =
      hashCalls f (otsSign H pkSeed secrets (OtsKey.ofIndex layer idx) msg) +
        if (evalWithAnswerFn f
            (otsSign H pkSeed secrets (OtsKey.ofIndex layer idx) msg)).isSome then
          pathCalls 257 layer.height
        else 0 := by
  rw [signLayer]
  rw [hashCalls_bind]
  cases evalWithAnswerFn f (otsSign H pkSeed secrets (OtsKey.ofIndex layer idx) msg) with
  | none => simp only [hashCalls_pure, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  | some ots =>
    obtain ⟨counter, chainValues⟩ := ots
    simp only [Option.isSome_some, ↓reduceIte]
    rw [hashCalls_bind, hashCalls_treePath f H hH secrets hsecrets, hashCalls_pure, Nat.add_zero]

/-- A layer gives a signature exactly when its one-time signature is found. -/
theorem isOk_signLayer (pkSeed : PkSeed) (layer : Layer) (idx : Nat) (msg : Digest) :
    (evalWithAnswerFn f (signLayer H pkSeed secrets layer idx msg)).isOk =
      (evalWithAnswerFn f (otsSign H pkSeed secrets (OtsKey.ofIndex layer idx) msg)).isSome := by
  rw [signLayer]
  rw [evalWithAnswerFn_bind]
  cases evalWithAnswerFn f (otsSign H pkSeed secrets (OtsKey.ofIndex layer idx) msg) with
  | none => rfl
  | some ots =>
    obtain ⟨counter, chainValues⟩ := ots
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.isSome_some]
    rfl

/-- The counter search of a layer under `f`, on the message its key signs under `f`. -/
def layerSearch (pkSeed : PkSeed) (idx : Nat) (layer : Layer) :
    OracleComp HashSpec (Option (UInt32 × Codeword)) :=
  Internal.findCounter H pkSeed (OtsKey.ofIndex layer idx)
    (evalWithAnswerFn f (layerMessage H pkSeed secrets layer idx)) 0 MAX_COUNTER_TRIALS

/-- Whether a layer signs under `f`: its result on the message its key signs is not an error. -/
def layerSigns (pkSeed : PkSeed) (idx : Nat) (layer : Layer) : Bool :=
  (evalWithAnswerFn f (signLayer H pkSeed secrets layer idx
    (evalWithAnswerFn f (layerMessage H pkSeed secrets layer idx)))).isOk

/-- The calls of one layer under `f`: the message its key signs, then its signature. -/
def layerCalls (pkSeed : PkSeed) (idx : Nat) (layer : Layer) : Nat :=
  hashCalls f (layerMessage H pkSeed secrets layer idx) +
    hashCalls f (signLayer H pkSeed secrets layer idx
      (evalWithAnswerFn f (layerMessage H pkSeed secrets layer idx)))

/-- The calls of the three layers, signed from the bottom up, up to the first that fails. -/
def layersCost (signs : Layer → Bool) (cost : Layer → Nat) : Nat :=
  cost .bottom + if signs .bottom then cost .middle + (if signs .middle then cost .top else 0)
    else 0

/-- A layer signs exactly when its counter search finds a counter. -/
theorem layerSigns_eq (pkSeed : PkSeed) (idx : Nat) (layer : Layer) :
    layerSigns f H secrets pkSeed idx layer =
      (evalWithAnswerFn f (layerSearch f H secrets pkSeed idx layer)).isSome := by
  rw [layerSigns, isOk_signLayer, isSome_otsSign]
  rfl

include hH hsecrets in
/-- A layer makes the calls of its message and of its search, and on success 192 and its path. -/
theorem layerCalls_eq (pkSeed : PkSeed) (idx : Nat) (layer : Layer) :
    layerCalls f H secrets pkSeed idx layer =
      messageCalls layer + hashCalls f (layerSearch f H secrets pkSeed idx layer) +
        if layerSigns f H secrets pkSeed idx layer then V + TARGET_SUM + pathCalls 257 layer.height
        else 0 := by
  rw [layerCalls, hashCalls_layerMessage f H hH secrets hsecrets,
    hashCalls_signLayer f H hH secrets hsecrets, isSome_otsSign,
    hashCalls_otsSign f H hH secrets hsecrets, layerSigns_eq, layerSearch]
  split <;> omega

include hH in
/-- A layer that fails has tried all `2^32` counters. -/
theorem hashCalls_layerSearch_of_fails (pkSeed : PkSeed) (idx : Nat) (layer : Layer)
    (h : layerSigns f H secrets pkSeed idx layer = false) :
    hashCalls f (layerSearch f H secrets pkSeed idx layer) = MAX_COUNTER_TRIALS := by
  rw [layerSigns_eq, layerSearch, isSome_findCounter] at h
  rw [layerSearch, hashCalls_findCounter f H hH]
  refine searchCalls_of_none _ 0 _ fun i hi => ?_
  cases hok : encodes f H pkSeed (OtsKey.ofIndex layer idx)
      (evalWithAnswerFn f (layerMessage H pkSeed secrets layer idx)) (0 + i) with
  | false => rfl
  | true =>
    have := (searchFinds_iff _ 0 _).2 ⟨i, hi, hok⟩
    rw [h] at this
    exact absurd this Bool.false_ne_true

include hH hsecrets in
/-- A layer that fails makes the calls of its message and of all `2^32` counters, and stops. -/
theorem layerCalls_of_fails (pkSeed : PkSeed) (idx : Nat) (layer : Layer)
    (h : layerSigns f H secrets pkSeed idx layer = false) :
    layerCalls f H secrets pkSeed idx layer = messageCalls layer + MAX_COUNTER_TRIALS := by
  rw [layerCalls_eq f H hH secrets hsecrets, hashCalls_layerSearch_of_fails f H hH secrets _ _ _ h,
    h]
  rfl

/-- The calls of the layers grow with the calls of each layer. -/
theorem layersCost_le (signs : Layer → Bool) {cost cost' : Layer → Nat}
    (h : ∀ layer, cost layer ≤ cost' layer) : layersCost signs cost ≤ layersCost signs cost' := by
  have hb := h .bottom
  have hm := h .middle
  have ht := h .top
  unfold layersCost
  cases signs .bottom <;> cases signs .middle <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    omega

/-! ### The whole request -/

include hH hsecrets in
/-- Signing from the secrets makes `H_msg`, the FORS openings and the layers to the first failure.

`idx` is the index that the digest names under `f`. -/
theorem hashCalls_signDerived (pk : PublicKey) (rho : Randomizer) (msg : Message) (idx : Nat)
    (hidx : digestIndex (evalWithAnswerFn f (hMsg H rho pk.pkSeed pk.root msg)) = idx) :
    hashCalls f (signDerived H secrets pk rho msg) =
      DIGEST_CALLS + FORS_TREES * (1 + pathCalls 2 FORS_HEIGHT) +
        layersCost (layerSigns f H secrets pk.pkSeed idx)
          (layerCalls f H secrets pk.pkSeed idx) := by
  rw [signDerived]
  dsimp only
  rw [hashCalls_bind, hashCalls_hMsg f H hH]
  rw [hidx, hashCalls_bind, hashCalls_forsSign f H hH secrets hsecrets]
  simp only [layersCost, layerCalls, layerSigns]
  rw [hashCalls_bind, hashCalls_bind]
  split
  · rename_i bottom hb
    simp only [hb, pure_bind, Except.isOk, Except.toBool, ↓reduceIte]
    rw [hashCalls_bind, hashCalls_bind]
    split
    · rename_i middle hm
      simp only [hm, ↓reduceIte]
      rw [hashCalls_bind, hashCalls_bind]
      split
      · simp only [hashCalls_pure]
        omega
      · simp only [hashCalls_pure]
        omega
    · rename_i err hm
      simp only [hm, hashCalls_pure, Bool.false_eq_true, ↓reduceIte]
      omega
  · rename_i err hb
    simp only [hb, hashCalls_pure, Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte]
    omega

include hH in
/-- A signing request makes the key expansion, the top tree and `PRF_msg`, then signs.

`key`, `pk` and `rho` are the expanded key, the public key and `R` under `f`. -/
theorem hashCalls_signWith (sk : SecretKey) (msg : Message) (key : ExpandedKey) (pk : PublicKey)
    (rho : Randomizer) (hkey : evalWithAnswerFn f (expandKey H sk.seed) = key)
    (hpk : evalWithAnswerFn f (publicKeyOf H key.pkSeed (prf H key.pkSeed sk.seed)) = pk)
    (hrho : evalWithAnswerFn f (prfMsg H key.skPrf key.pkSeed msg) = rho) :
    hashCalls f (signWith H sk msg) =
      2 + (258 * 2 ^ TOP_HEIGHT - 1) + 1 +
        hashCalls f (signDerived H (prf H key.pkSeed sk.seed) pk rho msg) := by
  rw [signWith, hashCalls_bind, hashCalls_expandKey f H hH, hkey]
  dsimp only
  rw [hashCalls_bind, hashCalls_publicKeyOf f H hH _ (hashCalls_prf f H hH _ _), hpk,
    hashCalls_bind, hashCalls_prfMsg f H hH, hrho]
  omega

include hH in
/-- A signing request, step by step, as the signer runs it.

1. The key expansion, 2 calls, and the top tree for `PK.root`, `258 * 2^10 - 1`.
2. `PRF_msg`, 1 call, and `H_msg`, 2 calls.
3. The FORS openings, `24 * (1 + 3059)` calls.
4. The layers from the bottom up, each its message, its search and, if it signs, 192 and its path.

The signer stops at the first layer that fails, after its search. -/
theorem hashCalls_signWith_layers (sk : SecretKey) (msg : Message) (key : ExpandedKey)
    (pk : PublicKey) (rho : Randomizer) (idx : Nat)
    (hkey : evalWithAnswerFn f (expandKey H sk.seed) = key)
    (hpk : evalWithAnswerFn f (publicKeyOf H key.pkSeed (prf H key.pkSeed sk.seed)) = pk)
    (hrho : evalWithAnswerFn f (prfMsg H key.skPrf key.pkSeed msg) = rho)
    (hidx : digestIndex (evalWithAnswerFn f (hMsg H rho key.pkSeed pk.root msg)) = idx) :
    hashCalls f (signWith H sk msg) =
      2 + (258 * 2 ^ TOP_HEIGHT - 1) + 1 + DIGEST_CALLS +
        FORS_TREES * (1 + pathCalls 2 FORS_HEIGHT) +
        layersCost (layerSigns f H (prf H key.pkSeed sk.seed) key.pkSeed idx)
          (layerCalls f H (prf H key.pkSeed sk.seed) key.pkSeed idx) := by
  have hseed : pk.pkSeed = key.pkSeed := by rw [← hpk, pkSeed_publicKeyOf]
  rw [hashCalls_signWith f H hH sk msg key pk rho hkey hpk hrho,
    hashCalls_signDerived f H hH _ (hashCalls_prf f H hH _ _) pk rho msg idx
      (by rw [hseed]; exact hidx), hseed]
  omega

/-- The calls before the layers: `2 + 264191 + 1 + 2 + 73440 = 337636`. -/
theorem signPrefixCalls_eq :
    2 + (258 * 2 ^ TOP_HEIGHT - 1) + 1 + DIGEST_CALLS + FORS_TREES * (1 + pathCalls 2 FORS_HEIGHT) =
      337636 := by
  decide

include hH in
/-- A request whose three layers sign makes `939499` calls and those of its three searches.

With least counters `c_0`, `c_1` and `c_2`, that is `939502 + c_0 + c_1 + c_2` calls. -/
theorem hashCalls_signWith_of_signs (sk : SecretKey) (msg : Message) (key : ExpandedKey)
    (pk : PublicKey) (rho : Randomizer) (idx : Nat)
    (hkey : evalWithAnswerFn f (expandKey H sk.seed) = key)
    (hpk : evalWithAnswerFn f (publicKeyOf H key.pkSeed (prf H key.pkSeed sk.seed)) = pk)
    (hrho : evalWithAnswerFn f (prfMsg H key.skPrf key.pkSeed msg) = rho)
    (hidx : digestIndex (evalWithAnswerFn f (hMsg H rho key.pkSeed pk.root msg)) = idx)
    (hsigns : ∀ layer, layerSigns f H (prf H key.pkSeed sk.seed) key.pkSeed idx layer = true) :
    hashCalls f (signWith H sk msg) =
      939499 + hashCalls f (layerSearch f H (prf H key.pkSeed sk.seed) key.pkSeed idx .bottom) +
        hashCalls f (layerSearch f H (prf H key.pkSeed sk.seed) key.pkSeed idx .middle) +
        hashCalls f (layerSearch f H (prf H key.pkSeed sk.seed) key.pkSeed idx .top) := by
  have hprf := hashCalls_prf f H hH key.pkSeed sk.seed
  rw [hashCalls_signWith_layers f H hH sk msg key pk rho idx hkey hpk hrho hidx,
    signPrefixCalls_eq, layersCost, layerCalls_eq f H hH _ hprf, layerCalls_eq f H hH _ hprf,
    layerCalls_eq f H hH _ hprf, hsigns, hsigns, hsigns]
  obtain ⟨hb, hm, ht⟩ := messageCalls_eq
  obtain ⟨pb, pm, pt⟩ := pathCalls_layers
  have hchains : V + TARGET_SUM = 192 := by decide
  simp only [↓reduceIte, hb, hm, ht, pb, pm, pt, hchains]
  omega

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge

/-! ## The model's request -/

open OracleComp OracleSpec

namespace SphincsSecurity.Security.SignCost

variable [Params]
open Concrete Completeness Prefix

variable (f : QueryImpl HashSpec Id)

/-! ## The prefix: the randomizer and its test -/

/-- The first randomizer lands, so the walk stops there and returns it. -/
theorem eval_signDigestLoop_succ (sk : Seeded.SecretKey) (message : Message)
    (step randomness : Randomness) (attempts : Nat) :
    evalWithAnswerFn f (Seeded.signDigestLoop sk message step (attempts + 1) randomness :
      OracleComp HashSpec (Option (Randomness × Index))) =
      some (randomness, blockIndex (evalWithAnswerFn f
        (messageDigestCall sk.parameter sk.root message randomness firstCall :
          OracleComp HashSpec HashOutput))) := by
  simp only [Seeded.signDigestLoop, Seeded.signAttempt, evalWithAnswerFn_bind,
    landed_full, ↓reduceIte, evalWithAnswerFn_pure]

/-- The walk makes one call: the first `H_msg` call, whose low bits it tests. -/
theorem hashCalls_signDigestLoop_succ (sk : Seeded.SecretKey) (message : Message)
    (step randomness : Randomness) (attempts : Nat) :
    hashCalls f (Seeded.signDigestLoop sk message step (attempts + 1) randomness :
      OracleComp HashSpec (Option (Randomness × Index))) = 1 := by
  rw [Seeded.signDigestLoop, hashCalls_bind, hashCalls_signAttempt]
  have heval : evalWithAnswerFn f (Seeded.signAttempt sk message randomness :
      OracleComp HashSpec (Option Index)) = some (blockIndex (evalWithAnswerFn f
        (messageDigestCall sk.parameter sk.root message randomness firstCall :
          OracleComp HashSpec HashOutput))) := by
    simp only [Seeded.signAttempt, evalWithAnswerFn_bind, landed_full, ↓reduceIte,
      evalWithAnswerFn_pure]
  rw [heval]
  rfl

/-- The randomizer `R` that the signer derives for a message. -/
noncomputable def signRandomness (sk : Seeded.SecretKey) (message : Message) : Randomness :=
  (evalWithAnswerFn f (deriveRandomizer sk.prf sk.parameter message :
    OracleComp HashSpec (Randomness × Randomness))).1

omit [Params] in
/-- `R` is the first 16 bytes of the answer at the input of `PRF_msg`. -/
theorem signRandomness_eq (sk : Seeded.SecretKey) (message : Message) :
    signRandomness f sk message =
      truncateHash (f (randomizerHashInput sk.prf sk.parameter message)) := by
  simp only [signRandomness, deriveRandomizer, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

/-- The index that the digest at `R` names. -/
noncomputable def signIndex (sk : Seeded.SecretKey) (message : Message) : Index :=
  digestIndex (Completeness.digestValue f sk message (signRandomness f sk message))

/-! ## One layer -/

/-- The one-time signature of a layer on the path of an index, on the message that its key signs.

That message is the FORS public key at the bottom, and the root of the tree below above it. -/
def signLayerOts (sk : Seeded.SecretKey) (index : Index) (lay : Layer) :
    OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))) :=
  Seeded.otsSign sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) sk.seed
    (layerMessageValue f sk index lay)

/-- Whether the counter search of a layer finds a counter that encodes. -/
noncomputable def signLayerFound (sk : Seeded.SecretKey) (index : Index) (lay : Layer) : Bool :=
  (evalWithAnswerFn f (signLayerOts f sk index lay)).isSome

/-- The calls of one layer: its one-time signature, then on success its path and root recovery.

The top layer recovers no root, so its recovery costs nothing. -/
noncomputable def signLayerCost (sk : Seeded.SecretKey) (index : Index) (lay : Layer) : Nat :=
  hashCalls f (signLayerOts f sk index lay) +
    if signLayerFound f sk index lay then GraphView.treePathCost lay + GraphView.recoverCost lay
    else 0

/-- A one-time signature makes the calls of its search, and 192 more if the search succeeds. -/
theorem hashCalls_seededOtsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput) :
    hashCalls f (Seeded.otsSign parameter lay tree leaf seed message :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
      hashCalls f (ReferenceChoice.search parameter lay tree leaf message encodingAttemptLimit 0) +
        if (firstEncoding f parameter lay tree leaf message encodingAttemptLimit 0).isSome then 192
        else 0 :=
  GraphView.hashCalls_otsSignFrom_search f parameter lay tree leaf seed message _ _

/-- A one-time signature is found exactly when its search finds a counter. -/
theorem isSome_seededOtsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput) :
    (evalWithAnswerFn f (Seeded.otsSign parameter lay tree leaf seed message :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))).isSome =
      (firstEncoding f parameter lay tree leaf message encodingAttemptLimit 0).isSome := by
  rw [Seeded.otsSign, otsSignFrom_eq_firstEncoding, Option.isSome_map]

/-- One step of the signer, from the honest value below its layer, costs the calls of the layer. -/
theorem hashCalls_layerStep_below (sk : Seeded.SecretKey) (index : Index) (lay : Layer) :
    hashCalls f (Seeded.layerStep sk index lay (belowValue f sk index lay) :
      OracleComp HashSpec (Option (LayerSignature lay × Digest))) =
      signLayerCost f sk index lay := by
  rw [GraphView.hashCalls_layerStep, rootPayload_belowValue, signLayerCost, signLayerFound,
    signLayerOts, hashCalls_seededOtsSign, isSome_seededOtsSign]
  split <;> omega

/-- A step of the signer from the honest value below its layer succeeds when its search does. -/
theorem isSome_layerStep_below (sk : Seeded.SecretKey) (index : Index) (lay : Layer) :
    (evalWithAnswerFn f (Seeded.layerStep sk index lay (belowValue f sk index lay) :
      OracleComp HashSpec (Option (LayerSignature lay × Digest)))).isSome =
      signLayerFound f sk index lay := by
  rw [eval_layerStep f sk index (landed_full _ _) lay, Option.isSome_map,
    GraphView.eval_signLayer_isSome, signLayerFound, signLayerOts, isSome_seededOtsSign]

/-- The calls of one layer, from its search: the trials, then on success 192, the path and recovery.
-/
theorem signLayerCost_eq_search (sk : Seeded.SecretKey) (index : Index) (lay : Layer) :
    signLayerCost f sk index lay =
      hashCalls f (ReferenceChoice.search sk.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (layerMessageValue f sk index lay) encodingAttemptLimit 0) +
      if (firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (layerMessageValue f sk index lay) encodingAttemptLimit 0).isSome then
        192 + GraphView.treePathCost lay + GraphView.recoverCost lay
      else 0 := by
  rw [signLayerCost, signLayerFound, signLayerOts, hashCalls_seededOtsSign, isSome_seededOtsSign]
  split <;> omega

/-! ## The whole request -/

/-- The calls of the FORS part: the `k` openings, the recovery of the `k` roots, and `T_k`. -/
def forsCost : Nat := forsTrees * GraphView.treeOpenCost + forsTrees * (1 + forsHeight) + 1

/-- The end of signing at a randomizer: `H_msg`, the FORS part, then the layers from the bottom up.

The layers stop after the first one whose search fails. -/
theorem hashCalls_finishSign (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness) :
    hashCalls f (Seeded.finishSign sk message randomness) =
      digestCalls + forsCost +
        seqCost
          (signLayerFound f sk (digestIndex (Completeness.digestValue f sk message randomness)))
          (signLayerCost f sk (digestIndex (Completeness.digestValue f sk message randomness)))
    := by
  simp only [Seeded.finishSign, hashCalls_bind, hashCalls_messageDigest,
    GraphView.hashCalls_forsOpen_exact, GraphView.hashCalls_forsRecover,
    GraphView.hashCalls_forsPublicKey, eval_forsPublicKey_forsRecover, forsCost,
    Completeness.digestValue]
  generalize digestIndex (evalWithAnswerFn f
    (messageDigest sk.parameter sk.root message randomness :
      OracleComp HashSpec MessageDigest)) = index
  -- The state of the thread at layer `v` is the honest value below that layer.
  let state : Nat → Digest := fun v =>
    if h : v < numLayers then belowValue f sk index ⟨v, h⟩ else 0
  have hstate : ∀ lay : Layer, state lay.val = belowValue f sk index lay :=
    fun lay => by simp only [state, dite_eq_left lay.isLt]
  have hbottom : evalWithAnswerFn f (Seeded.forsKey sk.parameter index sk.seed :
      OracleComp HashSpec Digest) = state (numLayers - 1) := by
    rw [show numLayers - 1 = bottomLayer.val from rfl, hstate, belowValue,
      dite_eq_right (by change ¬(numLayers - 1 + 1 < numLayers); omega)]
  -- Each step below the top hands the layer above its honest value.
  have hnext : ∀ (lay : Layer) (part : LayerSignature lay) (next : Digest), lay.val ≠ 0 →
      evalWithAnswerFn f (Seeded.layerStep sk index lay (state lay.val)) = some (part, next) →
        next = state (lay.val - 1) := by
    intro lay part next hlay h
    rw [hstate lay, eval_layerStep f sk index (landed_full _ _) lay] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, hnext⟩ := h
    rw [← hnext, dite_eq_right hlay, ← hstate]
    rfl
  have hlayers : hashCalls f (sequenceThread (fun lay below => Seeded.layerStep sk index lay below)
      (state (numLayers - 1))) =
      seqCost (signLayerFound f sk index) (signLayerCost f sk index) := by
    rw [GraphView.hashCalls_sequenceThread f state _ hnext]
    exact congrArg₂ (fun ok cost => seqCost ok cost)
      (funext fun lay => by rw [hstate lay, isSome_layerStep_below])
      (funext fun lay => by rw [hstate lay, hashCalls_layerStep_below])
  rw [hbottom, hlayers]
  cases evalWithAnswerFn f (sequenceThread (fun lay below => Seeded.layerStep sk index lay below)
      (state (numLayers - 1))) <;> simp only [hashCalls_pure] <;> omega

/-- A signing request: `PRF_msg`, the test of `R`, `H_msg`, the FORS part, then the layers.

The layers run from the bottom up and stop after the first one whose search fails. -/
theorem hashCalls_sign (sk : Seeded.SecretKey) (message : Message) :
    hashCalls f (Seeded.sign sk message : OracleComp HashSpec (Option Signature)) =
      1 + 1 + digestCalls + forsCost +
        seqCost (signLayerFound f sk (signIndex f sk message))
          (signLayerCost f sk (signIndex f sk message)) := by
  rw [Det.seededSign_eq, hashCalls_bind, Det.hashCalls_deriveRandomizer, hashCalls_bind,
    show digestAttemptLimit = (2 ^ 32 - 1) + 1 from rfl, hashCalls_signDigestLoop_succ,
    eval_signDigestLoop_succ]
  dsimp only
  rw [hashCalls_finishSign]
  simp only [signIndex, signRandomness]
  omega

/-! ## The counter search -/

/-- Whether counter `c` encodes the message under `f`, that is gives a codeword. -/
noncomputable def counterEncodes (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : HashInput) (c : Nat) : Bool :=
  (evalWithAnswerFn f (encode parameter lay tree leaf message (BitVec.ofNat counterBits c) :
    OracleComp HashSpec (Option Encoding))).isSome

/-- A search that finds no counter has tried all of its counters, one call each. -/
theorem hashCalls_search_of_none (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : HashInput) :
    ∀ (attempts start : Nat),
      (firstEncoding f parameter lay tree leaf message attempts start).isSome = false →
      hashCalls f (ReferenceChoice.search parameter lay tree leaf message attempts start) = attempts
  | 0, _, _ => by simp only [ReferenceChoice.search, hashCalls_pure]
  | attempts + 1, start, h => by
      cases he : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [firstEncoding, he] at h
          simp only [ReferenceChoice.search, hashCalls_bind, hashCalls_encode, he,
            hashCalls_search_of_none parameter lay tree leaf message attempts (start + 1) h]
          omega
      | some word => simp only [firstEncoding, he, Option.isSome_some, Bool.true_eq_false] at h

/-- A search whose least encoding counter is `start + k`, with `k < attempts`, makes `k + 1` calls.
-/
theorem hashCalls_search_of_least (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : HashInput) :
    ∀ (k attempts start : Nat), k < attempts →
      counterEncodes f parameter lay tree leaf message (start + k) = true →
      (∀ i < k, counterEncodes f parameter lay tree leaf message (start + i) = false) →
      hashCalls f (ReferenceChoice.search parameter lay tree leaf message attempts start) = k + 1
  | _, 0, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | 0, attempts + 1, start, _, hok, _ => by
      rw [Nat.add_zero] at hok
      obtain ⟨word, he⟩ := Option.isSome_iff_exists.1 hok
      simp only [ReferenceChoice.search, hashCalls_bind, hashCalls_encode, he, hashCalls_pure]
  | k + 1, attempts + 1, start, hk, hok, hlt => by
      have he : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) = none :=
        Option.not_isSome_iff_eq_none.1 (by simpa [counterEncodes] using hlt 0 (Nat.succ_pos k))
      have hrest := hashCalls_search_of_least parameter lay tree leaf message k attempts (start + 1)
        (by omega) (by rw [show start + 1 + k = start + (k + 1) by omega]; exact hok)
        (fun i hi => by rw [show start + 1 + i = start + (i + 1) by omega]; exact hlt _ (by omega))
      simp only [ReferenceChoice.search, hashCalls_bind, hashCalls_encode, he, hrest]
      omega

/-- A search whose counters include one that encodes finds a counter. -/
theorem isSome_firstEncoding_of_encodes (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput) :
    ∀ (k attempts start : Nat), k < attempts →
      counterEncodes f parameter lay tree leaf message (start + k) = true →
      (firstEncoding f parameter lay tree leaf message attempts start).isSome = true
  | _, 0, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | k, attempts + 1, start, hk, hok => by
      cases he : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | some word => simp only [firstEncoding, he, Option.isSome_some]
      | none =>
          simp only [firstEncoding, he]
          cases k with
          | zero => simp [counterEncodes, he] at hok
          | succ k =>
              exact isSome_firstEncoding_of_encodes parameter lay tree leaf message k attempts
                (start + 1) (by omega)
                (by rw [show start + 1 + k = start + (k + 1) by omega]; exact hok)

/-- A one-time signature whose least counter that encodes is `c < 2^32` makes `c + 1 + 192` calls.

They are the `c + 1` trials, the 64 chain starts and the 128 chain steps to the codeword. -/
theorem hashCalls_seededOtsSign_of_least (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput) (c : Nat)
    (hc : c < encodingAttemptLimit)
    (hok : counterEncodes f parameter lay tree leaf message c = true)
    (hlt : ∀ i < c, counterEncodes f parameter lay tree leaf message i = false) :
    hashCalls f (Seeded.otsSign parameter lay tree leaf seed message :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) = c + 1 + 192 := by
  rw [hashCalls_seededOtsSign, hashCalls_search_of_least f parameter lay tree leaf message c _ 0 hc
      (by rw [Nat.zero_add]; exact hok) (fun i hi => by rw [Nat.zero_add]; exact hlt i hi),
    isSome_firstEncoding_of_encodes f parameter lay tree leaf message c _ 0 hc
      (by rw [Nat.zero_add]; exact hok), ite_eq_left rfl]

/-- A one-time signature that is not found has tried all `2^32` counters, and makes no other call.
-/
theorem hashCalls_seededOtsSign_of_none (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput)
    (h : (evalWithAnswerFn f (Seeded.otsSign parameter lay tree leaf seed message :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))).isSome = false) :
    hashCalls f (Seeded.otsSign parameter lay tree leaf seed message :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) = encodingAttemptLimit := by
  rw [isSome_seededOtsSign] at h
  rw [hashCalls_seededOtsSign, hashCalls_search_of_none f parameter lay tree leaf message _ 0 h, h,
    ite_eq_right Bool.false_ne_true, Nat.add_zero]

/-- A layer whose search fails makes the `2^32` trials of its search and nothing else. -/
theorem signLayerCost_of_not_found (sk : Seeded.SecretKey) (index : Index) (lay : Layer)
    (h : signLayerFound f sk index lay = false) :
    signLayerCost f sk index lay = encodingAttemptLimit := by
  rw [signLayerCost, h, ite_eq_right Bool.false_ne_true, Nat.add_zero, signLayerOts,
    hashCalls_seededOtsSign_of_none f _ _ _ _ _ _ h]

/-! ## The configuration: 26 index bits in three layers, the lower two of height 8 -/

/-- Every layer keeps its whole tree, so a path holds no surrogate. -/
theorem keptHeight_eq_layerHeight (lay : Layer) : keptHeight lay = layerHeight lay := by
  by_cases h : lay.val = 0
  · have hl : lay = topLayer := Fin.ext h
    subst hl
    rw [keptHeight_top, layerHeight_top, Params.full]
    have := maxLayerHeight_add
    omega
  · exact keptHeight_of_ne_top lay h

/-- The path of a layer of height `j` makes `sum_{i < j} (258 * 2^i - 1)` calls.

It computes the sibling node at each level `i`, which has `2^i` one-time leaves of 257 calls each.
-/
theorem treePathCost_eq (lay : Layer) :
    GraphView.treePathCost lay = ∑ i ∈ Finset.range (layerHeight lay), (258 * 2 ^ i - 1) := by
  rw [GraphView.treePathCost, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun level _ => ?_
  rw [keptHeight_eq_layerHeight, ite_eq_left level.isLt]

/-- The opening of a FORS tree of height `a` makes `1 + sum_{i < a} (3 * 2^i - 1)` calls. -/
theorem treeOpenCost_eq :
    GraphView.treeOpenCost = 1 + ∑ i ∈ Finset.range forsHeight, (3 * 2 ^ i - 1) := by
  rw [GraphView.treeOpenCost, ← Fin.sum_univ_eq_sum_range (fun i => 3 * 2 ^ i - 1)]

section Configuration

variable (hH : totalHeight = 26) (hd : numLayers = 3) (hl : lowerHeight = 8)
  (hk : forsTrees = 24) (ha : forsHeight = 10)

include hH hd hl in
/-- The top layer has height `26 - 2 * 8 = 10`. -/
theorem layerHeight_top_eq : layerHeight topLayer = 10 := by
  rw [layerHeight_top, maxLayerHeight, hH, hd, hl]

include hl in
/-- A layer below the top has height 8. -/
theorem layerHeight_eq_of_ne_top (lay : Layer) (h : lay.val ≠ 0) : layerHeight lay = 8 := by
  rw [layerHeight_of_ne_top lay h, hl]

include hH hd hl hk ha in
/-- `H_msg` makes two calls: the digest has `30 + 3 + 1 = 34` bytes. -/
theorem digestCalls_eq : digestCalls = 2 := by
  have hbottom : bottomHeight = lowerHeight := by
    unfold bottomHeight layerHeight
    rw [ite_eq_right (by simp only [hd]; omega)]
  unfold digestCalls digestBytes mdBytes treeIndexBytes leafIndexBytes
  rw [hbottom, hH, hk, ha, hl]

include ha in
/-- The opening of a FORS tree of height 10 makes `1 + 3059 = 3060` calls. -/
theorem treeOpenCost_eq_3060 : GraphView.treeOpenCost = 3060 := by
  rw [treeOpenCost_eq, ha]
  decide

include hk ha in
/-- The FORS part makes `24 * 3060 + 24 * 11 + 1 = 73705` calls. -/
theorem forsCost_eq : forsCost = 73705 := by
  rw [forsCost, treeOpenCost_eq_3060 ha, hk, ha]

include hH hd hl in
/-- The path of the top layer, of height 10, makes 263924 calls. -/
theorem treePathCost_top : GraphView.treePathCost topLayer = 263924 := by
  rw [treePathCost_eq, layerHeight_top_eq hH hd hl]
  decide

include hl in
/-- The path of a layer below the top, of height 8, makes 65782 calls. -/
theorem treePathCost_of_ne_top (lay : Layer) (h : lay.val ≠ 0) :
    GraphView.treePathCost lay = 65782 := by
  rw [treePathCost_eq, layerHeight_eq_of_ne_top hl lay h]
  decide

/-- The top layer recovers no root. -/
theorem recoverCost_top : GraphView.recoverCost topLayer = 0 := ite_eq_left rfl

include hl in
/-- Below the top, recovering the root makes `1 + 64 + 1 + 8 = 74` calls.

They are the encoding, the remaining chain steps, the leaf and the fold up the tree. -/
theorem recoverCost_of_ne_top (lay : Layer) (h : lay.val ≠ 0) : GraphView.recoverCost lay = 74 := by
  rw [GraphView.recoverCost, ite_eq_right h, layerHeight_eq_of_ne_top hl lay h]

include hH hd hl in
/-- The top layer makes its one-time signature, then 263924 calls for its path if it is found. -/
theorem signLayerCost_top (sk : Seeded.SecretKey) (index : Index) :
    signLayerCost f sk index topLayer = hashCalls f (signLayerOts f sk index topLayer) +
      if signLayerFound f sk index topLayer then 263924 else 0 := by
  rw [signLayerCost, treePathCost_top hH hd hl, recoverCost_top]

include hl in
/-- A lower layer makes its one-time signature, then `65782 + 74` calls if it is found. -/
theorem signLayerCost_of_ne_top (sk : Seeded.SecretKey) (index : Index) (lay : Layer)
    (h : lay.val ≠ 0) :
    signLayerCost f sk index lay = hashCalls f (signLayerOts f sk index lay) +
      if signLayerFound f sk index lay then 65782 + 74 else 0 := by
  rw [signLayerCost, treePathCost_of_ne_top hl lay h, recoverCost_of_ne_top hl lay h]

/-- Three computations run from the last index down, each after the one above it succeeds. -/
theorem seqCost_three {n : Nat} (hn : n = 3) (ok : Fin n → Bool) (cost : Fin n → Nat) :
    seqCost ok cost = cost ⟨2, by omega⟩ + if ok ⟨2, by omega⟩ then
      cost ⟨1, by omega⟩ + (if ok ⟨1, by omega⟩ then cost ⟨0, by omega⟩ else 0) else 0 := by
  subst hn
  simp only [seqCost, ite_self, Nat.add_zero]
  rfl

include hH hd hl hk ha in
/-- A signing request in the configuration: 4 calls, 73705 for FORS, then the three layers.

The bottom layer runs first, the middle one if the bottom is found, the top one if both are. -/
theorem hashCalls_sign_three (sk : Seeded.SecretKey) (message : Message) (bottom middle : Layer)
    (hb : bottom.val = 2) (hm : middle.val = 1) :
    hashCalls f (Seeded.sign sk message : OracleComp HashSpec (Option Signature)) =
      4 + 73705 + (signLayerCost f sk (signIndex f sk message) bottom +
        if signLayerFound f sk (signIndex f sk message) bottom then
          signLayerCost f sk (signIndex f sk message) middle +
            (if signLayerFound f sk (signIndex f sk message) middle then
              signLayerCost f sk (signIndex f sk message) topLayer else 0)
        else 0) := by
  obtain ⟨b, hb2⟩ := bottom
  obtain ⟨m, hm1⟩ := middle
  simp only at hb hm
  subst hb hm
  rw [hashCalls_sign, seqCost_three hd, digestCalls_eq hH hd hl hk ha, forsCost_eq hk ha]
  rfl

include hH hd hl hk ha in
/-- A request whose three layers are found, with one-time signatures of `c + 1 + 192` calls each.

That count holds when `c` is the least counter that encodes, here `c_b`, `c_m` and `c_t`.

Before the layers, the request makes `4 + 73705` calls.

A lower layer then makes `c + 1 + 192 + 65782 + 74` calls, and the top layer `c + 1 + 192 + 263924`.

The sum is `469924 + c_b + c_m + c_t`. -/
theorem hashCalls_sign_of_found (sk : Seeded.SecretKey) (message : Message) (bottom middle : Layer)
    (hb : bottom.val = 2) (hm : middle.val = 1) (cb cm ct : Nat)
    (hcb : hashCalls f (signLayerOts f sk (signIndex f sk message) bottom) = cb + 1 + 192)
    (hcm : hashCalls f (signLayerOts f sk (signIndex f sk message) middle) = cm + 1 + 192)
    (hct : hashCalls f (signLayerOts f sk (signIndex f sk message) topLayer) = ct + 1 + 192)
    (hfb : signLayerFound f sk (signIndex f sk message) bottom = true)
    (hfm : signLayerFound f sk (signIndex f sk message) middle = true)
    (hft : signLayerFound f sk (signIndex f sk message) topLayer = true) :
    hashCalls f (Seeded.sign sk message : OracleComp HashSpec (Option Signature)) =
      469924 + cb + cm + ct := by
  rw [hashCalls_sign_three f hH hd hl hk ha sk message bottom middle hb hm,
    signLayerCost_of_ne_top f hl _ _ bottom (by omega),
    signLayerCost_of_ne_top f hl _ _ middle (by omega), signLayerCost_top f hH hd hl,
    hcb, hcm, hct, hfb, hfm, hft]
  simp only [↓reduceIte]
  omega

end Configuration

end SphincsSecurity.Security.SignCost

/-! ## EthLib's request against the model's -/

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec)
open SphincsSecurity.Security.Prefix (hashCalls hashCalls_bind hashCalls_pure)
open SphincsSecurity.Security.SignCost (signLayerFound signLayerCost signLayerOts)
open SphincsSecurity.Completeness

variable (f : QueryImpl HashSpec Id)

/-- EthLib's one-time signature at a key of the model makes the calls of the model's. -/
theorem hashCalls_otsSign_queryH (S : SphincsSecurity.MasterSeed)
    (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (lay : SphincsSecurity.Layer) (msg : Digest) :
    hashCalls f (otsSign (queryH (m := OracleComp HashSpec)) (ofParam P) (secretsOf S P)
        (OtsKey.ofIndex (layerOf lay) index.val) msg)
      = hashCalls f (SphincsSecurity.Seeded.otsSign P lay
          (SphincsSecurity.Concrete.treeIndexAt index lay)
          (SphincsSecurity.Concrete.leafIndexAt index lay) S msg.toList
            : OracleComp HashSpec _) := by
  rw [ofIndex_eq, otsSign_queryH, hashCalls_map]

/-- EthLib's one-time signature at a key of the model is found exactly when the model's is. -/
theorem isSome_otsSign_queryH (S : SphincsSecurity.MasterSeed)
    (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (lay : SphincsSecurity.Layer) (msg : Digest) :
    (evalWithAnswerFn f (otsSign (queryH (m := OracleComp HashSpec)) (ofParam P) (secretsOf S P)
        (OtsKey.ofIndex (layerOf lay) index.val) msg)).isSome
      = (evalWithAnswerFn f (SphincsSecurity.Seeded.otsSign P lay
          (SphincsSecurity.Concrete.treeIndexAt index lay)
          (SphincsSecurity.Concrete.leafIndexAt index lay) S msg.toList
            : OracleComp HashSpec _)).isSome := by
  rw [ofIndex_eq, otsSign_queryH, evalWithAnswerFn_map, Option.isSome_map]

/-- A layer of EthLib signs exactly when the model's layer finds its one-time signature. -/
theorem layerSigns_queryH (sk : SphincsSecurity.Seeded.SecretKey) (index : SphincsSecurity.Index)
    (lay : SphincsSecurity.Layer) :
    layerSigns f queryH (secretsOf sk.seed sk.parameter) (ofParam sk.parameter) index.val
        (layerOf lay)
      = signLayerFound f sk index lay := by
  rw [layerSigns, isOk_signLayer, layerMessage_answers, isSome_otsSign_queryH,
    toList_belowValue]
  rfl

/-- What the model's path and root recovery cost, EthLib's message and path cover, layer by layer.

- Top: 263924 path calls, no recovery, against 66047 + 263924.
- Middle and bottom: 65782 + 74, against 66047 + 65782 and 73705 + 65782. -/
theorem treePathCost_add_le (lay : SphincsSecurity.Layer) :
    SphincsSecurity.Security.GraphView.treePathCost lay
        + SphincsSecurity.Security.GraphView.recoverCost lay
      ≤ messageCalls (layerOf lay) + pathCalls 257 (layerOf lay).height := by
  obtain ⟨hmb, hmm, hmt⟩ := messageCalls_eq
  obtain ⟨hpb, hpm, hpt⟩ := pathCalls_layers
  obtain ⟨v, hv⟩ := lay
  change v < 3 at hv
  interval_cases v
  · have hpath : SphincsSecurity.Security.GraphView.treePathCost ⟨0, by decide⟩ = 263924 :=
      SphincsSecurity.Security.SignCost.treePathCost_top rfl rfl rfl
    have hrec : SphincsSecurity.Security.GraphView.recoverCost ⟨0, by decide⟩ = 0 :=
      SphincsSecurity.Security.SignCost.recoverCost_top
    simp only [layerOf, hpath, hrec, hmt, hpt]
    omega
  · have hpath : SphincsSecurity.Security.GraphView.treePathCost ⟨1, by decide⟩ = 65782 :=
      SphincsSecurity.Security.SignCost.treePathCost_of_ne_top rfl _ (by decide)
    have hrec : SphincsSecurity.Security.GraphView.recoverCost ⟨1, by decide⟩ = 74 :=
      SphincsSecurity.Security.SignCost.recoverCost_of_ne_top rfl _ (by decide)
    simp only [layerOf, hpath, hrec, hmm, hpm]
    omega
  · have hpath : SphincsSecurity.Security.GraphView.treePathCost ⟨2, by decide⟩ = 65782 :=
      SphincsSecurity.Security.SignCost.treePathCost_of_ne_top rfl _ (by decide)
    have hrec : SphincsSecurity.Security.GraphView.recoverCost ⟨2, by decide⟩ = 74 :=
      SphincsSecurity.Security.SignCost.recoverCost_of_ne_top rfl _ (by decide)
    simp only [layerOf, hpath, hrec, hmb, hpb]
    omega

/-- A layer of the model costs at most the same layer of EthLib.

Both make the same one-time signature, and EthLib also computes the layer's message. -/
theorem signLayerCost_le_layerCalls (sk : SphincsSecurity.Seeded.SecretKey)
    (index : SphincsSecurity.Index) (lay : SphincsSecurity.Layer) :
    signLayerCost f sk index lay
      ≤ layerCalls f queryH (secretsOf sk.seed sk.parameter) (ofParam sk.parameter) index.val
          (layerOf lay) := by
  have hsecrets : ∀ adrs, hashCalls f (secretsOf (m := OracleComp HashSpec) sk.seed
      sk.parameter adrs) = 1 :=
    fun adrs => hashCalls_prf f queryH (hashCalls_queryH f) _ _ adrs
  have hle := treePathCost_add_le lay
  rw [layerCalls, hashCalls_layerMessage f queryH (hashCalls_queryH f) _ hsecrets,
    hashCalls_signLayer f queryH (hashCalls_queryH f) _ hsecrets, layerMessage_answers,
    hashCalls_otsSign_queryH, isSome_otsSign_queryH, toList_belowValue, signLayerCost,
    signLayerFound, signLayerOts]
  split <;> omega

/-- One signing request costs the model at most what it costs EthLib, under every answer function.

The model signs with the secret key that its key generation returns under the same answers.

- Before the layers, EthLib makes 337636 calls and the model 73709.
- Each layer, signed from the bottom up, costs EthLib at least what it costs the model.
  Both signers fail at the same layer, so they reach the same layers.

So the model's cost is at most EthLib's on success and on a failure at any of the three layers. -/
theorem hashCalls_sign_le (S0 : SphincsSecurity.MasterSeed) (m : Message) :
    hashCalls f (SphincsSecurity.Seeded.sign
      (evalWithAnswerFn f (SphincsSecurity.Seeded.keygen S0 : OracleComp HashSpec _)).2
      (toMessage m) : OracleComp HashSpec _) ≤ hashCalls f (signWith H ⟨ofSeed S0⟩ m) := by
  conv_rhs => rw [← ofMessage_toMessage m]
  generalize toMessage m = msg
  rw [eval_keygen]
  generalize hP : evalWithAnswerFn f (SphincsSecurity.derivePublicSeed S0 :
    OracleComp HashSpec SphincsSecurity.PublicParameter) = P
  generalize hprf : evalWithAnswerFn f (SphincsSecurity.derivePrf S0 :
    OracleComp HashSpec HashSig.HashOutput) = skPrf
  generalize hroot : evalWithAnswerFn f (SphincsSecurity.Seeded.treeRoot P
    SphincsSecurity.topLayer SphincsSecurity.Concrete.rootTree S0 :
      OracleComp HashSpec SphincsSecurity.Digest) = root
  dsimp only
  set sk : SphincsSecurity.Seeded.SecretKey := ⟨S0, skPrf, P, root⟩ with hsk
  set index := SphincsSecurity.Security.SignCost.signIndex f sk msg with hindex
  -- EthLib's expanded key, public key and randomizer are the model's.
  have hkey : evalWithAnswerFn f (expandKey (queryH (m := OracleComp HashSpec)) (ofSeed S0))
      = ofExpanded P skPrf := by
    rw [expandKey_queryH, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      hP, hprf]
  have hpk : evalWithAnswerFn f (publicKeyOf (queryH (m := OracleComp HashSpec))
      (ofExpanded P skPrf).pkSeed (prf queryH (ofExpanded P skPrf).pkSeed (ofSeed S0)))
      = ofPublicKey ⟨root, P⟩ := by
    simp only [ofExpanded]
    rw [publicKeyOf_queryH, evalWithAnswerFn_map, hroot]
  have hrho : evalWithAnswerFn f (prfMsg (queryH (m := OracleComp HashSpec))
      (ofExpanded P skPrf).skPrf (ofExpanded P skPrf).pkSeed (ofMessage msg))
      = ofRandomizer (SphincsSecurity.Security.SignCost.signRandomness f sk msg) := by
    simp only [ofExpanded]
    rw [prfMsg_queryH, evalWithAnswerFn_map]
    rfl
  have hidx : digestIndex (evalWithAnswerFn f (hMsg (queryH (m := OracleComp HashSpec))
      (ofRandomizer (SphincsSecurity.Security.SignCost.signRandomness f sk msg))
      (ofExpanded P skPrf).pkSeed (ofPublicKey ⟨root, P⟩).root (ofMessage msg))) = index.val := by
    simp only [ofExpanded, ofPublicKey]
    rw [messageDigest_queryH, evalWithAnswerFn_map, eval_sequenceFin, digestIndex_ofOutputs,
      hindex, SphincsSecurity.Security.SignCost.signIndex, digestValue,
      SphincsSecurity.Concrete.messageDigest, evalWithAnswerFn_bind, eval_sequenceFin,
      evalWithAnswerFn_pure]
  rw [hashCalls_signWith_layers f queryH (hashCalls_queryH f) ⟨ofSeed S0⟩ (ofMessage msg)
    (ofExpanded P skPrf) (ofPublicKey ⟨root, P⟩) _ index.val hkey hpk hrho hidx, signPrefixCalls_eq,
    SphincsSecurity.Security.SignCost.hashCalls_sign_three f rfl rfl rfl rfl rfl sk msg
      bottomLayer middleLayer rfl rfl, ← hindex]
  -- Layer by layer, the flags agree and the model's costs are at most EthLib's.
  have hb : layerSigns f queryH (prf queryH (ofExpanded P skPrf).pkSeed (ofSeed S0))
      (ofExpanded P skPrf).pkSeed index.val .bottom = signLayerFound f sk index bottomLayer :=
    layerSigns_queryH f sk index bottomLayer
  have hm : layerSigns f queryH (prf queryH (ofExpanded P skPrf).pkSeed (ofSeed S0))
      (ofExpanded P skPrf).pkSeed index.val .middle = signLayerFound f sk index middleLayer :=
    layerSigns_queryH f sk index middleLayer
  have cb : signLayerCost f sk index bottomLayer ≤ layerCalls f queryH
      (prf queryH (ofExpanded P skPrf).pkSeed (ofSeed S0)) (ofExpanded P skPrf).pkSeed index.val
      .bottom :=
    signLayerCost_le_layerCalls f sk index bottomLayer
  have cm : signLayerCost f sk index middleLayer ≤ layerCalls f queryH
      (prf queryH (ofExpanded P skPrf).pkSeed (ofSeed S0)) (ofExpanded P skPrf).pkSeed index.val
      .middle :=
    signLayerCost_le_layerCalls f sk index middleLayer
  have ct : signLayerCost f sk index SphincsSecurity.topLayer ≤ layerCalls f queryH
      (prf queryH (ofExpanded P skPrf).pkSeed (ofSeed S0)) (ofExpanded P skPrf).pkSeed index.val
      .top :=
    signLayerCost_le_layerCalls f sk index SphincsSecurity.topLayer
  rw [layersCost, hb, hm]
  cases signLayerFound f sk index bottomLayer <;> cases signLayerFound f sk index middleLayer <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

omit f in
/-- An adversary with `q` hash calls against EthLib, translated, has `q` against the model. -/
theorem hasHashQueryBound_translate_self (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound adversary q) :
    SphincsSecurity.Security.HasHashQueryBound (translate adversary) q := by
  have h := hasHashQueryBound_translate Nat.one_pos le_rfl
    (fun f S0 m => by simpa only [Nat.one_mul] using hashCalls_sign_le f S0 m)
    adversary q hq
  rwa [Nat.one_mul, Nat.div_one] at h

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge

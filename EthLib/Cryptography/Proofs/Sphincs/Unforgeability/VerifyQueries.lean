module

public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import EthLib.Cryptography.Proofs.Sphincs.Encoding
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Game
public import EthLib.Cryptography.Proofs.Wots

/-!
# Proofs: the hash calls of leanSPHINCS verification

Verification makes at most 466 hash calls, whatever the key, the message and the signature.

- The digest: 2 calls.
- FORS: a leaf and 9 nodes in each of the 24 trees, 240 calls.
- Each of the 3 layers: an encoding, 64 chain steps and a leaf, 66 calls.
- The paths: one call per level, `8 + 8 + 10 = 26` calls.

That is `2 + 240 + 3 * 66 + 26 = 466`.

A layer walks `3 * 64 - 128 = 64` chain steps, because the digits of a codeword sum to 128.

Verification stops at the first layer that fails, so it can make fewer calls.

The count holds for every hash that makes at most one oracle call, and the game's `H` is one.

Verification also reads nothing but the answers to its own calls.

- When a fixed function answers every call, verification computes EthLib's verification with
  that function as its hash.
- Two functions that agree on the inputs verification hashes under the first give the same
  verdict.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open OracleSpec OracleComp

/-! ## The inputs a computation queries

This part holds for every oracle computation. -/

section Queries

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- The inputs a computation queries when `f` answers every query, in the order of the queries. -/
def queriesWith (f : QueryImpl spec Id) (oa : OracleComp spec α) : List spec.Domain :=
  OracleComp.construct (C := fun _ => List spec.Domain) (fun _ => [])
    (fun t _ rest => t :: rest (f t)) oa

/-- A computation that returns at once queries nothing. -/
@[simp] theorem queriesWith_pure (f : QueryImpl spec Id) (a : α) :
    queriesWith f (pure a : OracleComp spec α) = [] :=
  rfl

/-- A computation that starts with a query queries that input, then what the rest queries. -/
@[simp] theorem queriesWith_query_bind (f : QueryImpl spec Id) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) :
    queriesWith f ((query t : OracleComp spec (spec.Range t)) >>= k)
      = t :: queriesWith f (k (f t)) :=
  rfl

/-- A computation with at most `n` queries on every path queries at most `n` inputs. -/
theorem length_queriesWith_le (f : QueryImpl spec Id) {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : (queriesWith f oa).length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    have := ih (f t) (h.2 (f t))
    change (t :: queriesWith f (k (f t))).length ≤ n
    rw [List.length_cons]
    omega

/-- Two answer functions that agree on the inputs queried under the first give the same result.

The queries are then the same too. -/
theorem evalWithAnswerFn_congr (f g : QueryImpl spec Id) {oa : OracleComp spec α}
    (h : ∀ t ∈ queriesWith f oa, f t = g t) :
    evalWithAnswerFn f oa = evalWithAnswerFn g oa ∧ queriesWith f oa = queriesWith g oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    change ∀ t' ∈ t :: queriesWith f (k (f t)), f t' = g t' at h
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨hk₁, hk₂⟩ := ih (f t) h.2
    change evalWithAnswerFn f (k (f t)) = evalWithAnswerFn g (k (g t)) ∧
      t :: queriesWith f (k (f t)) = t :: queriesWith g (k (g t))
    rw [← h.1]
    exact ⟨hk₁, congrArg _ hk₂⟩

end Queries

/-! ## Verification under a map of monads

A map of monads that keeps `pure` and `bind` sends verification to verification.

The hash of the second is the mapped hash. -/

section Map

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  (φ : ∀ {β : Type}, m β → n β)
  (map_pure : ∀ {β : Type} (b : β), φ (pure b) = pure b)
  (map_bind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ x >>= fun b => φ (f b))
  (H : ByteArray → m (Vector UInt8 32))

include map_pure map_bind

/-- The map keeps `map` too. -/
theorem map_monad_map {β γ : Type} (g : β → γ) (x : m β) : φ (g <$> x) = g <$> φ x := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, map_bind]
  simp only [Function.comp_def, map_pure]

omit [LawfulMonad m] [LawfulMonad n] in
/-- Computing a vector in order commutes with the map. -/
theorem ofFnInOrder_map_monad {α : Type} :
    ∀ (k : Nat) (f : Fin k → m α),
      φ (Xmss.ofFnInOrder k f) = Xmss.ofFnInOrder k fun i => φ (f i)
  | 0, _ => map_pure _
  | k + 1, f => by
    simp only [Xmss.ofFnInOrder, map_bind, map_pure, ofFnInOrder_map_monad k]

omit [LawfulMonad m] [LawfulMonad n] in
/-- A hash chain commutes with the map. -/
theorem chain_map_monad {α : Type} {k : Nat} (step : Fin k → α → m α) (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ k) (value : α),
      φ (Wots.chain step start steps h value)
        = Wots.chain (fun i v => φ (step i v)) start steps h value
  | 0, _, _ => map_pure _
  | s + 1, h, value => by
    rw [Wots.chain_succ, Wots.chain_succ, map_bind, chain_map_monad step start s]

omit [LawfulMonad m] [LawfulMonad n] in
/-- A tweakable hash call commutes with the map. -/
theorem th_map_monad (pp : PublicParam) (A : Address) (payload : ByteArray) :
    φ (th H pp A payload) = th (fun x => φ (H x)) pp A payload := by
  rw [th, th, thFull, thFull]
  erw [map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

omit [LawfulMonad m] [LawfulMonad n] in
/-- A FORS node hash commutes with the map. -/
theorem forsNodeHash_map_monad (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (level j : Nat) (left right : Digest) :
    φ (forsNodeHash H pp idx kappa level j left right)
      = forsNodeHash (fun x => φ (H x)) pp idx kappa level j left right :=
  th_map_monad φ map_pure map_bind H _ _ _

omit [LawfulMonad m] [LawfulMonad n] in
/-- A hypertree node hash commutes with the map. -/
theorem nodeHash_map_monad (pp : PublicParam) (layer : Layer) (tree level j : Nat)
    (left right : Digest) :
    φ (nodeHash H pp layer tree level j left right)
      = nodeHash (fun x => φ (H x)) pp layer tree level j left right :=
  th_map_monad φ map_pure map_bind H _ _ _

omit [LawfulMonad m] [LawfulMonad n] in
/-- A chain step commutes with the map. -/
theorem chainStep_map_monad (pp : PublicParam) (key : OtsKey) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) :
    φ (chainStep H pp key i mu value) = chainStep (fun x => φ (H x)) pp key i mu value :=
  th_map_monad φ map_pure map_bind H _ _ _

omit [LawfulMonad m] [LawfulMonad n] in
/-- The message digest commutes with the map. -/
theorem messageDigest_map_monad (pp : PublicParam) (msg : Message) (rho : Randomizer) :
    φ (messageDigest H pp msg rho) = messageDigest (fun x => φ (H x)) pp msg rho := by
  rw [messageDigest, messageDigest, map_bind, ofFnInOrder_map_monad φ map_pure map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

omit [LawfulMonad m] [LawfulMonad n] in
/-- Recovering one FORS tree commutes with the map. -/
theorem treeRecover_map_monad (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) (opening : TreeOpening) :
    φ (treeRecover H pp idx kappa l opening)
      = treeRecover (fun x => φ (H x)) pp idx kappa l opening := by
  rw [treeRecover, treeRecover, map_bind, forsLeafHash, forsLeafHash,
    th_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun leaf => ?_)
  rw [map_bind, Merkle.climb_map_monad (φ := φ) (map_pure := map_pure) (map_bind := map_bind)]
  simp only [forsNodeHash_map_monad φ map_pure map_bind, map_pure]

omit [LawfulMonad m] [LawfulMonad n] in
/-- Recovering a FORS key commutes with the map. -/
theorem forsRecover_map_monad (pp : PublicParam) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) :
    φ (forsRecover H pp idx leaves openings)
      = forsRecover (fun x => φ (H x)) pp idx leaves openings := by
  rw [forsRecover, forsRecover, ofFnInOrder_map_monad φ map_pure map_bind]
  simp only [treeRecover_map_monad φ map_pure map_bind]

/-- Recovering a one-time leaf commutes with the map. -/
theorem otsLeaf_map_monad (pp : PublicParam) (key : OtsKey) (msg : ByteArray) (counter : UInt32)
    (y : Vector Digest V) :
    φ (otsLeaf H pp key msg counter y) = otsLeaf (fun x => φ (H x)) pp key msg counter y := by
  rw [otsLeaf, otsLeaf, map_bind, encode, encode, map_monad_map φ map_pure map_bind,
    th_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun x => ?_)
  cases x with
  | none => exact map_pure _
  | some x =>
    simp only [map_bind, map_pure, ofFnInOrder_map_monad φ map_pure map_bind, chain,
      chain_map_monad φ map_pure map_bind, chainStep_map_monad φ map_pure map_bind, otsLeafHash,
      th_map_monad φ map_pure map_bind]

/-- A layer's root commutes with the map. -/
theorem layerRoot_map_monad (pp : PublicParam) (layer : Layer) (idx : Nat) (msg : ByteArray)
    (sig : LayerSignature layer) :
    φ (layerRoot H pp layer idx msg sig) = layerRoot (fun x => φ (H x)) pp layer idx msg sig := by
  rw [layerRoot, layerRoot, map_bind, otsLeaf_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun leaf => ?_)
  cases leaf with
  | none => exact map_pure _
  | some leaf =>
    simp only [map_bind, map_pure, fold, Merkle.climb_map_monad (φ := φ) (map_pure := map_pure)
      (map_bind := map_bind), nodeHash_map_monad φ map_pure map_bind]

/-- Verification commutes with the map. -/
theorem verifyWith_map_monad (pk : PublicKey) (msg : Message) (sig : Signature) :
    φ (verifyWith H pk msg sig) = verifyWith (fun x => φ (H x)) pk msg sig := by
  rw [verifyWith, verifyWith, map_bind, messageDigest_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun d => ?_)
  rw [map_bind, forsRecover_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun key => ?_)
  rw [map_bind, layerRoot_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun r₀ => ?_)
  cases r₀ with
  | none => exact map_pure _
  | some r₀ =>
    rw [map_bind, layerRoot_map_monad φ map_pure map_bind]
    refine congrArg _ (funext fun r₁ => ?_)
    cases r₁ with
    | none => exact map_pure _
    | some r₁ =>
      rw [map_bind, layerRoot_map_monad φ map_pure map_bind]
      refine congrArg _ (funext fun r₂ => ?_)
      cases r₂ with
      | none => exact map_pure _
      | some r₂ => exact map_pure _

end Map

/-! ## Counting the calls of verification

This part holds for every hash that makes at most one oracle call. -/

section Count

variable {ι : Type} {spec : OracleSpec ι}

/-- Computing a vector in order makes the calls of its entries, added. -/
theorem ofFnInOrder_isTotalQueryBound {α : Type} :
    ∀ (k : Nat) (f : Fin k → OracleComp spec α) (b : Fin k → Nat),
      (∀ i, IsTotalQueryBound (f i) (b i)) →
        IsTotalQueryBound (Xmss.ofFnInOrder k f) (∑ i, b i)
  | 0, _, _, _ => isQueryBound_pure _ _ _ _
  | k + 1, f, b, h => by
    rw [Xmss.ofFnInOrder, Fin.sum_univ_succ]
    refine isTotalQueryBound_bind (h 0) fun _ => ?_
    rw [← Nat.add_zero (∑ i : Fin k, b i.succ)]
    exact isTotalQueryBound_bind (ofFnInOrder_isTotalQueryBound k _ _ fun i => h i.succ)
      fun _ => isQueryBound_pure _ _ _ _

/-- A hash chain makes one call per step, when each step makes at most one. -/
theorem chain_isTotalQueryBound {α : Type} {k : Nat} (step : Fin k → α → OracleComp spec α)
    (hstep : ∀ i v, IsTotalQueryBound (step i v) 1) (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ k) (value : α),
      IsTotalQueryBound (Wots.chain step start steps h value) steps
  | 0, _, _ => isQueryBound_pure _ _ _ _
  | s + 1, h, value => by
    rw [Wots.chain_succ]
    exact isTotalQueryBound_bind (chain_isTotalQueryBound step hstep start s _ value)
      fun _ => hstep _ _

/-- A climb makes one call per sibling, when each node hash makes at most one. -/
theorem climb_isTotalQueryBound {α : Type} (hash : Nat → Nat → α → α → OracleComp spec α)
    (hhash : ∀ level j left right, IsTotalQueryBound (hash level j left right) 1) :
    ∀ (siblings : List α) (level j : Nat) (current : α),
      IsTotalQueryBound (Merkle.climb hash level j current siblings) siblings.length
  | [], _, _, _ => isQueryBound_pure _ _ _ _
  | _ :: rest, level, j, current => by
    rw [Merkle.climb, List.length_cons]
    exact (isTotalQueryBound_bind (hhash _ _ _ _)
      fun _ => climb_isTotalQueryBound hash hhash rest _ _ _).mono (by omega)

/-- The chains of a codeword have `3 * 64 - 128 = 64` steps left above the revealed positions. -/
theorem sum_steps_of_codeword {d : Digest} {x : Codeword} (h : codeword? d = some x) :
    ∑ i : Fin V, (CHAIN_LENGTH - 1 - (x[i] : Nat)) = CHAIN_HASHES := by
  have hle : ∀ i : Fin V, (x[i] : Nat) ≤ CHAIN_LENGTH - 1 := fun i => by
    have := x[i].isLt
    omega
  have hsum : ∑ i : Fin V, (CHAIN_LENGTH - 1 - (x[i] : Nat)) + ∑ i : Fin V, (x[i] : Nat)
      = V * (CHAIN_LENGTH - 1) := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [sum_of_codeword h] at hsum
  rw [← chain_hashes_eq]
  omega

variable (H : ByteArray → OracleComp spec (Vector UInt8 32))
  (hH : ∀ x, IsTotalQueryBound (H x) 1)

include hH

/-- A tweakable hash call makes one call. -/
theorem th_isTotalQueryBound (pp : PublicParam) (A : Address) (payload : ByteArray) :
    IsTotalQueryBound (th H pp A payload) 1 :=
  isTotalQueryBound_bind (n₂ := 0) (hH _) fun _ => isQueryBound_pure _ _ _ _

/-- The message digest makes one call per half. -/
theorem messageDigest_isTotalQueryBound (pp : PublicParam) (msg : Message) (rho : Randomizer) :
    IsTotalQueryBound (messageDigest H pp msg rho) DIGEST_CALLS := by
  rw [messageDigest]
  refine (isTotalQueryBound_bind (n₂ := 0) ?_ fun _ => isQueryBound_pure _ _ _ _).mono le_rfl
  have := ofFnInOrder_isTotalQueryBound DIGEST_CALLS
    (fun call => thFull H pp (addrMsg call) (packBytes msg ++ packBytes rho)) (fun _ => 1)
    fun _ => hH _
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this

/-- Recovering one FORS tree makes a call for the leaf and one per level up to level 9. -/
theorem treeRecover_isTotalQueryBound (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) (opening : TreeOpening) :
    IsTotalQueryBound (treeRecover H pp idx kappa l opening) FORS_HEIGHT := by
  rw [treeRecover]
  refine (isTotalQueryBound_bind (th_isTotalQueryBound H hH _ _ _) fun _ =>
    isTotalQueryBound_bind (n₂ := 0)
      (climb_isTotalQueryBound _ (fun _ _ _ _ => th_isTotalQueryBound H hH _ _ _) _ _ _ _)
      fun _ => isQueryBound_pure _ _ _ _).mono ?_
  simp only [List.length_take, FORS_HEIGHT]
  omega

/-- Recovering the FORS key makes `24 * 10 = 240` calls. -/
theorem forsRecover_isTotalQueryBound (pp : PublicParam) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) :
    IsTotalQueryBound (forsRecover H pp idx leaves openings) (FORS_TREES * FORS_HEIGHT) := by
  rw [forsRecover]
  simpa using ofFnInOrder_isTotalQueryBound FORS_TREES _ (fun _ => FORS_HEIGHT)
    fun _ => treeRecover_isTotalQueryBound H hH _ _ _ _ _

/-- Recovering a one-time leaf makes an encoding call, 64 chain steps and a leaf call. -/
theorem otsLeaf_isTotalQueryBound (pp : PublicParam) (key : OtsKey) (msg : ByteArray)
    (counter : UInt32) (y : Vector Digest V) :
    IsTotalQueryBound (otsLeaf H pp key msg counter y) (1 + (CHAIN_HASHES + 1)) := by
  rw [otsLeaf]
  refine isTotalQueryBound_bind_of_mem_support
    ((isQueryBound_map_iff _ _ _ _ _).2 (th_isTotalQueryBound H hH _ _ _)) fun x hx => ?_
  obtain ⟨d, -, hxd⟩ := mem_support_map_peel _ _ hx
  rcases x with _ | x
  · exact isQueryBound_pure _ _ _ _
  · have hd : codeword? d = some x := hxd.symm
    refine (isTotalQueryBound_bind
      (ofFnInOrder_isTotalQueryBound V _ (fun i => CHAIN_LENGTH - 1 - (x[i] : Nat)) fun i =>
        chain_isTotalQueryBound _ (fun _ _ => th_isTotalQueryBound H hH _ _ _) _ _ _ _)
      fun _ => isTotalQueryBound_bind (n₂ := 0) (th_isTotalQueryBound H hH _ _ _)
        fun _ => isQueryBound_pure _ _ _ _).mono ?_
    rw [sum_steps_of_codeword hd]

/-- A layer's root makes the calls of its one-time leaf, then one per level of its path. -/
theorem layerRoot_isTotalQueryBound (pp : PublicParam) (layer : Layer) (idx : Nat)
    (msg : ByteArray) (sig : LayerSignature layer) :
    IsTotalQueryBound (layerRoot H pp layer idx msg sig)
      (1 + (CHAIN_HASHES + 1) + layer.height) := by
  rw [layerRoot]
  refine isTotalQueryBound_bind (otsLeaf_isTotalQueryBound H hH _ _ _ _ _) fun leaf => ?_
  cases leaf with
  | none => exact isQueryBound_pure _ _ _ _
  | some leaf =>
    rw [← Nat.add_zero layer.height]
    refine isTotalQueryBound_bind ?_ fun _ => isQueryBound_pure _ _ _ _
    rw [fold]
    have := climb_isTotalQueryBound (nodeHash H pp layer (OtsKey.ofIndex layer idx).tree)
      (fun _ _ _ _ => th_isTotalQueryBound H hH _ _ _) sig.path.toList 0
      (OtsKey.ofIndex layer idx).leaf leaf
    rwa [Vector.length_toList] at this

/-- The most hash calls verification makes: the digest, FORS, three layers and their paths. -/
def verifyCalls : Nat :=
  DIGEST_CALLS + FORS_TREES * FORS_HEIGHT + LAYERS * (CHAIN_HASHES + 2) + HEIGHT

/-- Verification makes at most that many hash calls, on every path. -/
theorem verifyWith_isTotalQueryBound (pk : PublicKey) (msg : Message) (sig : Signature) :
    IsTotalQueryBound (verifyWith H pk msg sig) verifyCalls := by
  rw [verifyWith]
  refine (isTotalQueryBound_bind (n₂ := FORS_TREES * FORS_HEIGHT +
      ((1 + (CHAIN_HASHES + 1) + Layer.bottom.height) +
        ((1 + (CHAIN_HASHES + 1) + Layer.middle.height) +
          (1 + (CHAIN_HASHES + 1) + Layer.top.height + 0))))
    (messageDigest_isTotalQueryBound H hH _ _ _) fun _ =>
    isTotalQueryBound_bind (forsRecover_isTotalQueryBound H hH _ _ _ _) fun _ =>
    isTotalQueryBound_bind (layerRoot_isTotalQueryBound H hH _ _ _ _ _) fun r₀ => ?_).mono ?_
  · cases r₀ with
    | none => exact isQueryBound_pure _ _ _ _
    | some r₀ =>
      refine isTotalQueryBound_bind (layerRoot_isTotalQueryBound H hH _ _ _ _ _) fun r₁ => ?_
      cases r₁ with
      | none => exact isQueryBound_pure _ _ _ _
      | some r₁ =>
        refine isTotalQueryBound_bind (layerRoot_isTotalQueryBound H hH _ _ _ _ _) fun r₂ => ?_
        cases r₂ with
        | none => exact isQueryBound_pure _ _ _ _
        | some r₂ => exact isQueryBound_pure _ _ _ _
  · decide

end Count

/-- Verification makes at most 466 calls. -/
theorem verifyCalls_eq : verifyCalls = 466 := by
  decide

/-! ## Verification in the game -/

/-- The game's `H` makes one oracle call. -/
theorem H_isTotalQueryBound (x : ByteArray) : IsTotalQueryBound (H x) 1 :=
  (isQueryBound_map_iff _ _ _ _ _).2 ((isQueryBound_query_iff _ _ _ _).2 Nat.one_pos)

/-- In the game, verification makes at most 466 hash calls, on every path. -/
theorem verifyWith_H_isTotalQueryBound (pk : PublicKey) (msg : Message) (sig : Signature) :
    IsTotalQueryBound (verifyWith H pk msg sig) 466 :=
  verifyCalls_eq ▸ verifyWith_isTotalQueryBound H H_isTotalQueryBound pk msg sig

/-- The inputs verification hashes in the game, when `F` answers every query. -/
def verifyQueries (F : QueryImpl XmssSecurity.OracleWorld Id) (pk : PublicKey) (msg : Message)
    (sig : Signature) : List XmssSecurity.OracleWorld.Domain :=
  queriesWith F (verifyWith H pk msg sig)

/-- Verification hashes at most 466 inputs. -/
theorem length_verifyQueries_le (F : QueryImpl XmssSecurity.OracleWorld Id) (pk : PublicKey)
    (msg : Message) (sig : Signature) : (verifyQueries F pk msg sig).length ≤ 466 :=
  length_queriesWith_le F (verifyWith_H_isTotalQueryBound pk msg sig)

/-- When `F` answers every query, the game's verification is EthLib's verification.

Its hash is the one that `F` gives. -/
theorem evalWithAnswerFn_verifyWith (F : QueryImpl XmssSecurity.OracleWorld Id) (pk : PublicKey)
    (msg : Message) (sig : Signature) :
    evalWithAnswerFn F (verifyWith H pk msg sig)
      = (verifyWith (pureHash fun x => evalWithAnswerFn F (H x)) pk msg sig : Id Bool) := by
  have hmap := verifyWith_map_monad (m := OracleComp XmssSecurity.OracleWorld) (n := Id)
    (fun x => evalWithAnswerFn F x) (fun _ => rfl)
    (fun x f => by rw [evalWithAnswerFn_bind]; rfl) H pk msg sig
  -- The mapped hash is the pure hash of the answers, as a function.
  have hH : (fun x => (evalWithAnswerFn F (H x) : Id (Vector UInt8 32)))
      = pureHash fun x => evalWithAnswerFn F (H x) := rfl
  exact hmap.trans (congrArg (fun h => verifyWith h pk msg sig) hH)

/-- Verification reads only the answers at the inputs it hashes.

Two answer functions that agree there give the same verdict, after the same inputs. -/
theorem verifyWith_congr (F G : QueryImpl XmssSecurity.OracleWorld Id) (pk : PublicKey)
    (msg : Message) (sig : Signature) (h : ∀ t ∈ verifyQueries F pk msg sig, F t = G t) :
    evalWithAnswerFn F (verifyWith H pk msg sig)
        = evalWithAnswerFn G (verifyWith H pk msg sig) ∧
      verifyQueries F pk msg sig = verifyQueries G pk msg sig :=
  evalWithAnswerFn_congr F G h

end EthLib.Cryptography.Sphincs.Unforgeability

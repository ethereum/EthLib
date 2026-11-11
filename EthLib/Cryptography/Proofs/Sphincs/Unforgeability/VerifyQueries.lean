module

public import EthLib.Cryptography.Proofs.HashSig
public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import EthLib.Cryptography.Proofs.Sphincs.Encoding
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Game
public import EthLib.Cryptography.Proofs.Wots

/-!
# Proofs: the hash calls of leanSPHINCS verification

Verification makes at most 491 hash calls, whatever the key, the message and the signature.

- The digest: 2 calls.
- FORS: a leaf and 10 nodes in each of the 24 trees, then `T_k` over the roots, 265 calls.
- Each of the 3 layers: an encoding, 64 chain steps and a leaf, 66 calls.
- The paths: one call per height, `8 + 8 + 10 = 26` calls.

That is `2 + 265 + 3 * 66 + 26 = 491`.

A layer walks `3 * 64 - 128 = 64` chain steps, because the digits of a codeword sum to 128.

Verification stops at the first layer whose encoding is not a codeword, so it can make fewer calls.

A signature that verifies passes every layer, so it takes exactly 491 calls.

The count holds for every hash that makes at most one oracle call, and the game's `H` is one.

Verification also reads nothing but the answers to its own calls.

- Let a fixed function answer every call.
  Verification then computes EthLib's verification, with that function as its hash.
- Take two functions that agree on the inputs that verification hashes under the first.
  They give the same verdict.
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

omit [LawfulMonad m] [LawfulMonad n] in
/-- A tweakable hash call commutes with the map. -/
theorem th_map_monad (pkSeed : PkSeed) (adrs : Adrs) (payload : ByteArray) :
    φ (th H pkSeed adrs payload) = th (fun x => φ (H x)) pkSeed adrs payload := by
  rw [th, th, map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

omit [LawfulMonad m] [LawfulMonad n] in
/-- A FORS node hash commutes with the map. -/
theorem forsNodeHash_map_monad (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (z j : Nat) (left right : Digest) :
    φ (forsNodeHash H pkSeed idx kappa z j left right)
      = forsNodeHash (fun x => φ (H x)) pkSeed idx kappa z j left right :=
  th_map_monad φ map_pure map_bind H _ _ _

omit [LawfulMonad m] [LawfulMonad n] in
/-- The FORS public key from the roots commutes with the map. -/
theorem forsPkFromRoots_map_monad (pkSeed : PkSeed) (idx : Nat)
    (roots : Vector Digest FORS_TREES) :
    φ (forsPkFromRoots H pkSeed idx roots) = forsPkFromRoots (fun x => φ (H x)) pkSeed idx roots :=
  th_map_monad φ map_pure map_bind H _ _ _

omit [LawfulMonad m] [LawfulMonad n] in
/-- A hypertree node hash commutes with the map. -/
theorem nodeHash_map_monad (pkSeed : PkSeed) (layer : Layer) (tree z j : Nat)
    (left right : Digest) :
    φ (nodeHash H pkSeed layer tree z j left right)
      = nodeHash (fun x => φ (H x)) pkSeed layer tree z j left right :=
  th_map_monad φ map_pure map_bind H _ _ _

omit [LawfulMonad m] [LawfulMonad n] in
/-- A chain step commutes with the map. -/
theorem chainStep_map_monad (pkSeed : PkSeed) (key : OtsKey) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) :
    φ (chainStep H pkSeed key i mu value) = chainStep (fun x => φ (H x)) pkSeed key i mu value :=
  th_map_monad φ map_pure map_bind H _ _ _

omit [LawfulMonad m] [LawfulMonad n] in
/-- The message digest commutes with the map. -/
theorem hMsg_map_monad (rho : Randomizer) (pkSeed : PkSeed) (pkRoot : Digest) (msg : Message) :
    φ (hMsg H rho pkSeed pkRoot msg) = hMsg (fun x => φ (H x)) rho pkSeed pkRoot msg := by
  rw [hMsg, hMsg, map_bind, HashSig.ofFnInOrder_map_monad φ map_pure map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

omit [LawfulMonad m] [LawfulMonad n] in
/-- Recovering one FORS tree's root commutes with the map. -/
theorem treeRecover_map_monad (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) (opening : TreeOpening) :
    φ (treeRecover H pkSeed idx kappa s opening)
      = treeRecover (fun x => φ (H x)) pkSeed idx kappa s opening := by
  rw [treeRecover, treeRecover, map_bind, forsLeafHash, forsLeafHash,
    th_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun leaf => ?_)
  rw [Merkle.climb_map_monad (φ := φ) (map_pure := map_pure) (map_bind := map_bind)]
  simp only [forsNodeHash_map_monad φ map_pure map_bind]

omit [LawfulMonad m] [LawfulMonad n] in
/-- Recovering a FORS public key commutes with the map. -/
theorem forsRecover_map_monad (pkSeed : PkSeed) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) :
    φ (forsRecover H pkSeed idx leaves openings)
      = forsRecover (fun x => φ (H x)) pkSeed idx leaves openings := by
  rw [forsRecover, forsRecover, map_bind, HashSig.ofFnInOrder_map_monad φ map_pure map_bind]
  simp only [treeRecover_map_monad φ map_pure map_bind,
    forsPkFromRoots_map_monad φ map_pure map_bind]

/-- Recovering a one-time leaf commutes with the map. -/
theorem otsLeaf_map_monad (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (counter : UInt32)
    (y : Vector Digest V) :
    φ (otsLeaf H pkSeed key msg counter y)
      = otsLeaf (fun x => φ (H x)) pkSeed key msg counter y := by
  rw [otsLeaf, otsLeaf, map_bind, encode, encode, HashSig.map_monad_map φ map_pure map_bind,
    th_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun x => ?_)
  cases x with
  | none => exact map_pure _
  | some x =>
    simp only [map_bind, map_pure, HashSig.ofFnInOrder_map_monad φ map_pure map_bind, chain,
      Wots.chain_map_monad φ map_pure map_bind, chainStep_map_monad φ map_pure map_bind,
      otsLeafHash, th_map_monad φ map_pure map_bind]

/-- A layer's root commutes with the map. -/
theorem layerRoot_map_monad (pkSeed : PkSeed) (layer : Layer) (idx : Nat) (msg : Digest)
    (sig : LayerSignature layer) :
    φ (layerRoot H pkSeed layer idx msg sig)
      = layerRoot (fun x => φ (H x)) pkSeed layer idx msg sig := by
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
  rw [verifyWith, verifyWith, map_bind, hMsg_map_monad φ map_pure map_bind]
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
        IsTotalQueryBound (HashSig.ofFnInOrder k f) (∑ i, b i)
  | 0, _, _, _ => isQueryBound_pure _ _ _ _
  | k + 1, f, b, h => by
    rw [HashSig.ofFnInOrder, Fin.sum_univ_succ]
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
theorem th_isTotalQueryBound (pkSeed : PkSeed) (adrs : Adrs) (payload : ByteArray) :
    IsTotalQueryBound (th H pkSeed adrs payload) 1 :=
  isTotalQueryBound_bind (n₂ := 0) (hH _) fun _ => isQueryBound_pure _ _ _ _

/-- The message digest makes one call per block of output. -/
theorem hMsg_isTotalQueryBound (rho : Randomizer) (pkSeed : PkSeed) (pkRoot : Digest)
    (msg : Message) : IsTotalQueryBound (hMsg H rho pkSeed pkRoot msg) DIGEST_CALLS := by
  rw [hMsg]
  refine (isTotalQueryBound_bind (n₂ := 0) ?_ fun _ => isQueryBound_pure _ _ _ _).mono le_rfl
  have := ofFnInOrder_isTotalQueryBound DIGEST_CALLS
    (fun i => H (packBytes rho ++ packBytes pkSeed ++ packBytes pkRoot ++ packBytes msg
      ++ packBytes (toByte 4 i.val))) (fun _ => 1) fun _ => hH _
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this

/-- Recovering one FORS tree's root makes a call for the leaf and one per height. -/
theorem treeRecover_isTotalQueryBound (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) (opening : TreeOpening) :
    IsTotalQueryBound (treeRecover H pkSeed idx kappa s opening) (1 + FORS_HEIGHT) := by
  rw [treeRecover]
  refine isTotalQueryBound_bind (th_isTotalQueryBound H hH _ _ _) fun leaf => ?_
  have := climb_isTotalQueryBound (forsNodeHash H pkSeed idx kappa)
    (fun _ _ _ _ => th_isTotalQueryBound H hH _ _ _) opening.path.toList 0 s.val leaf
  rwa [Vector.length_toList] at this

/-- Recovering the FORS public key makes `24 * 11 + 1 = 265` calls: the trees, then `T_k`. -/
theorem forsRecover_isTotalQueryBound (pkSeed : PkSeed) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) :
    IsTotalQueryBound (forsRecover H pkSeed idx leaves openings)
      (FORS_TREES * (1 + FORS_HEIGHT) + 1) := by
  rw [forsRecover]
  refine isTotalQueryBound_bind ?_ fun _ => th_isTotalQueryBound H hH _ _ _
  simpa using ofFnInOrder_isTotalQueryBound FORS_TREES _ (fun _ => 1 + FORS_HEIGHT)
    fun _ => treeRecover_isTotalQueryBound H hH _ _ _ _ _

/-- Recovering a one-time leaf makes an encoding call, 64 chain steps and a leaf call. -/
theorem otsLeaf_isTotalQueryBound (pkSeed : PkSeed) (key : OtsKey) (msg : Digest)
    (counter : UInt32) (y : Vector Digest V) :
    IsTotalQueryBound (otsLeaf H pkSeed key msg counter y) (1 + (CHAIN_HASHES + 1)) := by
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

/-- A layer's root makes the calls of its one-time leaf, then one per height of its path. -/
theorem layerRoot_isTotalQueryBound (pkSeed : PkSeed) (layer : Layer) (idx : Nat)
    (msg : Digest) (sig : LayerSignature layer) :
    IsTotalQueryBound (layerRoot H pkSeed layer idx msg sig)
      (1 + (CHAIN_HASHES + 1) + layer.height) := by
  rw [layerRoot]
  refine isTotalQueryBound_bind (otsLeaf_isTotalQueryBound H hH _ _ _ _ _) fun leaf => ?_
  cases leaf with
  | none => exact isQueryBound_pure _ _ _ _
  | some leaf =>
    rw [← Nat.add_zero layer.height]
    refine isTotalQueryBound_bind ?_ fun _ => isQueryBound_pure _ _ _ _
    rw [fold]
    have := climb_isTotalQueryBound (nodeHash H pkSeed layer (OtsKey.ofIndex layer idx).tree)
      (fun _ _ _ _ => th_isTotalQueryBound H hH _ _ _) sig.path.toList 0
      (OtsKey.ofIndex layer idx).leaf leaf
    rwa [Vector.length_toList] at this

/-- The most hash calls verification makes: the digest, FORS, three layers and their paths. -/
def verifyCalls : Nat :=
  DIGEST_CALLS + (FORS_TREES * (1 + FORS_HEIGHT) + 1) + LAYERS * (CHAIN_HASHES + 2) + HEIGHT

/-- Verification makes at most that many hash calls, on every path. -/
theorem verifyWith_isTotalQueryBound (pk : PublicKey) (msg : Message) (sig : Signature) :
    IsTotalQueryBound (verifyWith H pk msg sig) verifyCalls := by
  rw [verifyWith]
  refine (isTotalQueryBound_bind (n₂ := (FORS_TREES * (1 + FORS_HEIGHT) + 1) +
      ((1 + (CHAIN_HASHES + 1) + Layer.bottom.height) +
        ((1 + (CHAIN_HASHES + 1) + Layer.middle.height) +
          (1 + (CHAIN_HASHES + 1) + Layer.top.height + 0))))
    (hMsg_isTotalQueryBound H hH _ _ _ _) fun _ =>
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

/-! ## The exact count when verification accepts

With a fixed function for the answers, a layer that accepts makes every call of its bound.

So verification makes exactly as many calls as its bound when it accepts. -/

section Exact

variable {ι : Type} {spec : OracleSpec ι} (F : QueryImpl spec Id)

/-- A bind queries what its first part queries, then what the rest queries after that answer. -/
theorem queriesWith_bind {α β : Type} (oa : OracleComp spec α) (k : α → OracleComp spec β) :
    queriesWith F (oa >>= k)
      = queriesWith F oa ++ queriesWith F (k (evalWithAnswerFn F oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k' ih =>
    rw [bind_assoc]
    change t :: queriesWith F (k' (F t) >>= k) = (t :: queriesWith F (k' (F t))) ++ _
    rw [ih, evalWithAnswerFn_bind, List.cons_append]
    rfl

/-- A map queries what the computation queries. -/
theorem queriesWith_map {α β : Type} (g : α → β) (oa : OracleComp spec α) :
    queriesWith F (g <$> oa) = queriesWith F oa := by
  rw [map_eq_bind_pure_comp, queriesWith_bind]
  simp

/-- Computing a vector in order queries the inputs of its entries, entry 0 first. -/
theorem length_queriesWith_ofFnInOrder {α : Type} :
    ∀ (k : Nat) (f : Fin k → OracleComp spec α),
      (queriesWith F (HashSig.ofFnInOrder k f)).length = ∑ i, (queriesWith F (f i)).length
  | 0, _ => rfl
  | k + 1, f => by
    rw [HashSig.ofFnInOrder, Fin.sum_univ_succ, queriesWith_bind, List.length_append,
      queriesWith_bind, List.length_append, length_queriesWith_ofFnInOrder k]
    simp

/-- A walk of `steps` steps queries `steps` inputs, when each step queries one. -/
theorem length_queriesWith_chain {α : Type} {k : Nat} (step : Fin k → α → OracleComp spec α)
    (hstep : ∀ i v, (queriesWith F (step i v)).length = 1) (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ k) (value : α),
      (queriesWith F (Wots.chain step start steps h value)).length = steps
  | 0, _, _ => rfl
  | s + 1, h, value => by
    rw [Wots.chain_succ, queriesWith_bind, List.length_append,
      length_queriesWith_chain step hstep start s _ value, hstep]

/-- A climb queries one input per sibling, when each node hash queries one. -/
theorem length_queriesWith_climb {α : Type} (hash : Nat → Nat → α → α → OracleComp spec α)
    (hhash : ∀ z j left right, (queriesWith F (hash z j left right)).length = 1) :
    ∀ (siblings : List α) (z j : Nat) (current : α),
      (queriesWith F (Merkle.climb hash z j current siblings)).length = siblings.length
  | [], _, _, _ => rfl
  | _ :: rest, z, j, current => by
    rw [Merkle.climb, queriesWith_bind, List.length_append, hhash,
      length_queriesWith_climb hash hhash rest, List.length_cons]
    omega

variable (H : ByteArray → OracleComp spec (Vector UInt8 32))
  (hH : ∀ x, (queriesWith F (H x)).length = 1)

include hH

/-- A tweakable hash call queries one input. -/
theorem length_queriesWith_th (pkSeed : PkSeed) (adrs : Adrs) (payload : ByteArray) :
    (queriesWith F (th H pkSeed adrs payload)).length = 1 := by
  rw [th, queriesWith_bind, List.length_append, hH]
  rfl

/-- The message digest queries one input per block of output. -/
theorem length_queriesWith_hMsg (rho : Randomizer) (pkSeed : PkSeed) (pkRoot : Digest)
    (msg : Message) : (queriesWith F (hMsg H rho pkSeed pkRoot msg)).length = DIGEST_CALLS := by
  rw [hMsg, queriesWith_bind, List.length_append, length_queriesWith_ofFnInOrder]
  simp [hH]

/-- Recovering one FORS tree's root queries the leaf, then one input per height. -/
theorem length_queriesWith_treeRecover (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) (opening : TreeOpening) :
    (queriesWith F (treeRecover H pkSeed idx kappa s opening)).length = 1 + FORS_HEIGHT := by
  rw [treeRecover, queriesWith_bind, List.length_append, forsLeafHash,
    length_queriesWith_th F H hH, length_queriesWith_climb F (forsNodeHash H pkSeed idx kappa)
      (fun _ _ _ _ => length_queriesWith_th F H hH _ _ _), Vector.length_toList]

/-- Recovering the FORS public key queries `24 * 11 + 1 = 265` inputs. -/
theorem length_queriesWith_forsRecover (pkSeed : PkSeed) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) :
    (queriesWith F (forsRecover H pkSeed idx leaves openings)).length
      = FORS_TREES * (1 + FORS_HEIGHT) + 1 := by
  rw [forsRecover, queriesWith_bind, List.length_append, length_queriesWith_ofFnInOrder,
    forsPkFromRoots, length_queriesWith_th F H hH]
  simp [length_queriesWith_treeRecover F H hH]

/-- Recovering a one-time leaf queries an encoding, 64 chain steps and a leaf.

The encoding must be a codeword, so that the recovery returns a leaf. -/
theorem length_queriesWith_otsLeaf (pkSeed : PkSeed) (key : OtsKey) (msg : Digest)
    (counter : UInt32) (y : Vector Digest V)
    (h : (evalWithAnswerFn F (otsLeaf H pkSeed key msg counter y)).isSome) :
    (queriesWith F (otsLeaf H pkSeed key msg counter y)).length = 1 + (CHAIN_HASHES + 1) := by
  rw [otsLeaf, evalWithAnswerFn_bind] at h
  rw [otsLeaf, queriesWith_bind, List.length_append]
  rcases hx : evalWithAnswerFn F (encode H pkSeed key msg counter) with _ | x
  · rw [hx] at h
    exact absurd h (by simp)
  · -- The encoding is a codeword, so all chains are walked to their ends.
    rw [encode, evalWithAnswerFn_map] at hx
    rw [encode, queriesWith_map, length_queriesWith_th F H hH]
    dsimp only
    rw [queriesWith_bind, List.length_append, length_queriesWith_ofFnInOrder, queriesWith_bind,
      List.length_append, otsLeafHash, length_queriesWith_th F H hH]
    have hc : ∀ i : Fin V, (queriesWith F (chain H pkSeed key i x[i] (CHAIN_LENGTH - 1 - x[i])
        (by have := x[i].isLt; omega) y[i])).length = CHAIN_LENGTH - 1 - x[i] := fun i =>
      length_queriesWith_chain F _ (fun _ _ => length_queriesWith_th F H hH _ _ _) _ _ _ _
    rw [Finset.sum_congr rfl fun i _ => hc i, sum_steps_of_codeword hx, queriesWith_pure,
      List.length_nil]

/-- A layer's root queries its one-time leaf's inputs, then one per height of its path.

The layer must accept, so that it returns a root. -/
theorem length_queriesWith_layerRoot (pkSeed : PkSeed) (layer : Layer) (idx : Nat)
    (msg : Digest) (sig : LayerSignature layer)
    (h : (evalWithAnswerFn F (layerRoot H pkSeed layer idx msg sig)).isSome) :
    (queriesWith F (layerRoot H pkSeed layer idx msg sig)).length
      = 1 + (CHAIN_HASHES + 1) + layer.height := by
  rw [layerRoot, evalWithAnswerFn_bind] at h
  rw [layerRoot, queriesWith_bind, List.length_append]
  rcases hleaf : evalWithAnswerFn F (otsLeaf H pkSeed (OtsKey.ofIndex layer idx) msg sig.counter
    sig.chainValues) with _ | leaf
  · rw [hleaf] at h
    exact absurd h (by simp)
  · rw [length_queriesWith_otsLeaf F H hH _ _ _ _ _ (by rw [hleaf]; rfl)]
    dsimp only
    rw [queriesWith_bind, List.length_append, fold,
      length_queriesWith_climb F (nodeHash H pkSeed layer (OtsKey.ofIndex layer idx).tree)
        (fun _ _ _ _ => length_queriesWith_th F H hH _ _ _), Vector.length_toList]
    rfl

/-- **A signature that verifies takes exactly as many calls as the bound.**

Every layer accepted, so each made all its calls. -/
theorem length_queriesWith_verifyWith (pk : PublicKey) (msg : Message) (sig : Signature)
    (h : evalWithAnswerFn F (verifyWith H pk msg sig) = true) :
    (queriesWith F (verifyWith H pk msg sig)).length = verifyCalls := by
  rw [verifyWith] at h ⊢
  simp only [evalWithAnswerFn_bind, queriesWith_bind, List.length_append,
    length_queriesWith_hMsg F H hH, length_queriesWith_forsRecover F H hH] at h ⊢
  generalize evalWithAnswerFn F (hMsg H sig.randomizer pk.pkSeed pk.root msg) = d at h ⊢
  generalize evalWithAnswerFn F (forsRecover H pk.pkSeed (digestIndex d) (digestLeaves d)
    sig.fors) = forsPk at h ⊢
  -- Each layer accepted, since a rejection returns false at once.
  rcases h0 : evalWithAnswerFn F (layerRoot H pk.pkSeed .bottom (digestIndex d) forsPk
    sig.bottom) with _ | r₀ <;> rw [h0] at h
  · exact absurd h (by simp)
  rw [length_queriesWith_layerRoot F H hH _ _ _ _ _ (by rw [h0]; rfl)]
  dsimp only at h ⊢
  simp only [evalWithAnswerFn_bind, queriesWith_bind, List.length_append] at h ⊢
  rcases h1 : evalWithAnswerFn F (layerRoot H pk.pkSeed .middle (digestIndex d) r₀
    sig.middle) with _ | r₁ <;> rw [h1] at h
  · exact absurd h (by simp)
  rw [length_queriesWith_layerRoot F H hH _ _ _ _ _ (by rw [h1]; rfl)]
  dsimp only at h ⊢
  simp only [evalWithAnswerFn_bind, queriesWith_bind, List.length_append] at h ⊢
  rcases h2 : evalWithAnswerFn F (layerRoot H pk.pkSeed .top (digestIndex d) r₁
    sig.top) with _ | r₂ <;> rw [h2] at h
  · exact absurd h (by simp)
  rw [length_queriesWith_layerRoot F H hH _ _ _ _ _ (by rw [h2]; rfl)]
  dsimp only
  rw [queriesWith_pure, List.length_nil]
  decide

end Exact

/-- Verification makes at most `2 + 265 + 3 * 66 + 26 = 491` calls. -/
theorem verifyCalls_eq : verifyCalls = 491 := by
  decide

/-! ## Verification in the game -/

/-- The game's `H` makes one oracle call. -/
theorem H_isTotalQueryBound (x : ByteArray) : IsTotalQueryBound (H x) 1 :=
  (isQueryBound_map_iff _ _ _ _ _).2 ((isQueryBound_query_iff _ _ _ _).2 Nat.one_pos)

/-- In the game, verification makes at most 491 hash calls, on every path. -/
theorem verifyWith_H_isTotalQueryBound (pk : PublicKey) (msg : Message) (sig : Signature) :
    IsTotalQueryBound (verifyWith H pk msg sig) 491 :=
  verifyCalls_eq ▸ verifyWith_isTotalQueryBound H H_isTotalQueryBound pk msg sig

/-- The inputs verification hashes in the game, when `F` answers every query. -/
def verifyQueries (F : QueryImpl HashSig.OracleWorld Id) (pk : PublicKey) (msg : Message)
    (sig : Signature) : List HashSig.OracleWorld.Domain :=
  queriesWith F (verifyWith H pk msg sig)

/-- Verification hashes at most 491 inputs. -/
theorem length_verifyQueries_le (F : QueryImpl HashSig.OracleWorld Id) (pk : PublicKey)
    (msg : Message) (sig : Signature) : (verifyQueries F pk msg sig).length ≤ 491 :=
  length_queriesWith_le F (verifyWith_H_isTotalQueryBound pk msg sig)

/-- In the game, one hash call queries one input. -/
theorem length_queriesWith_H (F : QueryImpl HashSig.OracleWorld Id) (x : ByteArray) :
    (queriesWith F (H x)).length = 1 :=
  rfl

/-- **In the game, a signature that verifies is checked with exactly 491 hash calls.**

The bound of 491 is then reached: no layer stopped verification early. -/
theorem length_verifyQueries_of_verify (F : QueryImpl HashSig.OracleWorld Id) (pk : PublicKey)
    (msg : Message) (sig : Signature) (h : evalWithAnswerFn F (verifyWith H pk msg sig) = true) :
    (verifyQueries F pk msg sig).length = 491 :=
  (length_queriesWith_verifyWith F H (length_queriesWith_H F) pk msg sig h).trans verifyCalls_eq

/-- When `F` answers every query, the game's verification is EthLib's verification.

Its hash is the one that `F` gives. -/
theorem evalWithAnswerFn_verifyWith (F : QueryImpl HashSig.OracleWorld Id) (pk : PublicKey)
    (msg : Message) (sig : Signature) :
    evalWithAnswerFn F (verifyWith H pk msg sig)
      = (verifyWith (pureHash fun x => evalWithAnswerFn F (H x)) pk msg sig : Id Bool) := by
  have hmap := verifyWith_map_monad (m := OracleComp HashSig.OracleWorld) (n := Id)
    (fun x => evalWithAnswerFn F x) (fun _ => rfl)
    (fun x f => by rw [evalWithAnswerFn_bind]; rfl) H pk msg sig
  -- The mapped hash is the pure hash of the answers, as a function.
  have hH : (fun x => (evalWithAnswerFn F (H x) : Id (Vector UInt8 32)))
      = pureHash fun x => evalWithAnswerFn F (H x) := rfl
  exact hmap.trans (congrArg (fun h => verifyWith h pk msg sig) hH)

/-- Verification reads only the answers at the inputs it hashes.

Two answer functions that agree there give the same verdict, after the same inputs. -/
theorem verifyWith_congr (F G : QueryImpl HashSig.OracleWorld Id) (pk : PublicKey)
    (msg : Message) (sig : Signature) (h : ∀ t ∈ verifyQueries F pk msg sig, F t = G t) :
    evalWithAnswerFn F (verifyWith H pk msg sig)
        = evalWithAnswerFn G (verifyWith H pk msg sig) ∧
      verifyQueries F pk msg sig = verifyQueries G pk msg sig :=
  evalWithAnswerFn_congr F G h

end EthLib.Cryptography.Sphincs.Unforgeability

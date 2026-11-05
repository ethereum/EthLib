module

public import EthLib.Cryptography.Proofs.Vrf.AdaptiveIndex
public import EthLib.Cryptography.Proofs.Vrf.KeyGen
public import EthLib.Cryptography.Proofs.DerivationTable

/-!
# Proofs: an output is unpredictable when the secrets come from a seed

Key generation derives secret `i` as the hash of a prefix, a uniform seed and `i`.

Here the hash is a random oracle, and the adversary chooses the index, as for uniform secrets.

It wins with probability at most `2^32 (1 + 2 Q) / 2^256 + Q / 2^256`.

Here `Q = q_H + (q_O + 1) 2^33`, as for uniform secrets.

The last term is one hidden-seed step.

The secrets act as independent uniform values until a hash query hits a secret input of the seed.

A hash input fixes the seed it encodes, so each query hits with probability at most `2^-256`.

The game then has uniform secrets, and the bound for uniform secrets applies.

The tree, the openings and the output are written once, over a source of secrets.

The seed, a table of derivations and a fixed table of secrets are three such sources.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

namespace EthLib.Cryptography

/-- Answering the queries of a recording run through a handler records the same keys. -/
theorem simulateQ_run_logKeys {ι ι' ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {K : Type} [DecidableEq K] (so : QueryImpl spec' (OracleComp spec''))
    (impl : QueryImpl spec (OracleComp spec')) (key : spec.Domain → Option K) {α : Type}
    (oa : OracleComp spec α) (S : Finset K) :
    simulateQ so ((simulateQ (logKeys impl key) oa).run S) =
      (simulateQ (logKeys (so ∘ₛ impl) key) oa).run S := by
  induction oa using OracleComp.inductionOn generalizing S with
  | pure x => simp
  | query_bind t k ih =>
    simp [logKeys, QueryImpl.apply_compose, ih]

end EthLib.Cryptography

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-! ## The tree over a source of secrets -/

section Source

variable {m : Type → Type} [Monad m] (H : ByteArray → m Digest) (sec : UInt32 → m Digest)

/-- Leaf `j`: the hash of the leaf input of the secret that the source gives at `j`. -/
def leafOf (j : Nat) : m Digest := do
  let s ← sec (UInt32.ofNat j)
  H (leafInput s)

/-- The root of the tree over a source of secrets. -/
def rootOf : m Digest :=
  Merkle.root (nodeWith H) (leafOf H sec) VRF_TREE_HEIGHT

/-- The opening at index `i` over a source of secrets. -/
def openingOf (i : UInt32) : m Opening := do
  let path ← Merkle.path (nodeWith H) (leafOf H sec) VRF_TREE_HEIGHT i.toNat
  let s ← sec i
  return ⟨s, path⟩

end Source

/-- With Keccak-256 as `H` and the secrets of a seed, the root is the published root. -/
theorem rootOf_secret (seed : Seed) :
    (rootOf (m := Id) (fun x => pure (hash x)) (fun i => pure (secret seed i))).run =
      keyGen seed :=
  rfl

/-- With Keccak-256 as `H` and the secrets of a seed, the opening is the holder's opening. -/
theorem openingOf_secret (seed : Seed) (i : UInt32) :
    (openingOf (m := Id) (fun x => pure (hash x)) (fun i => pure (secret seed i)) i).run =
      prove seed i :=
  rfl

section Game

variable {ι : Type} {spec : OracleSpec ι}

/-- The holder over a source of secrets: it passes other queries on and answers every opening. -/
def holderOf (pass : QueryImpl (unifSpec + HashSpec) (OracleComp spec))
    (sec : UInt32 → OracleComp spec Digest) : QueryImpl AdversarySpec (OracleComp spec)
  | .inl t => pass t
  | .inr i => some <$> openingOf (fun x => pass (.inr x)) sec i

/-- The game of an index the adversary chooses, over a source of secrets. -/
def gameOf (pass : QueryImpl (unifSpec + HashSpec) (OracleComp spec))
    (sec : UInt32 → OracleComp spec Digest) (adversary : AdaptiveAdversary) :
    OracleComp spec Bool := do
  let r ← rootOf (fun x => pass (.inr x)) sec
  let z ← (simulateQ (logKeys (holderOf pass sec) openedIndex) (adversary r)).run ∅
  let s ← sec z.1.1
  let output ← pass (.inr (outputInput s))
  return decide (z.1.1 ∉ z.2 ∧ z.1.2 = output)

/-- Answering the queries of the game through a handler gives the game over the answered source. -/
theorem simulateQ_gameOf {ι' : Type} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec'))
    (pass : QueryImpl (unifSpec + HashSpec) (OracleComp spec))
    (sec : UInt32 → OracleComp spec Digest) (adversary : AdaptiveAdversary) :
    simulateQ so (gameOf pass sec adversary) =
      gameOf (so ∘ₛ pass) (fun i => simulateQ so (sec i)) adversary := by
  have hbind : ∀ {β γ : Type} (x : OracleComp spec β) (f : β → OracleComp spec γ),
      simulateQ so (x >>= f) = simulateQ so x >>= fun b => simulateQ so (f b) :=
    fun x f => simulateQ_bind _ _ _
  have hleaf : ∀ j, simulateQ so (leafOf (fun x => pass (.inr x)) sec j) =
      leafOf (fun x => (so ∘ₛ pass) (.inr x)) (fun i => simulateQ so (sec i)) j := fun j => by
    simp [leafOf, QueryImpl.apply_compose]
  have hnode : ∀ (l j : Nat) (a b : Digest),
      simulateQ so (nodeWith (fun x => pass (.inr x)) l j a b) =
        nodeWith (fun x => (so ∘ₛ pass) (.inr x)) l j a b :=
    fun _ _ _ _ => by simp [nodeWith, QueryImpl.apply_compose]
  have hroot : simulateQ so (rootOf (fun x => pass (.inr x)) sec) =
      rootOf (fun x => (so ∘ₛ pass) (.inr x)) (fun i => simulateQ so (sec i)) := by
    rw [rootOf, Merkle.root, Merkle.node_map _ _ hbind]
    simp only [hnode, hleaf]
    rfl
  have hopen : ∀ i, simulateQ so (openingOf (fun x => pass (.inr x)) sec i) =
      openingOf (fun x => (so ∘ₛ pass) (.inr x)) (fun i => simulateQ so (sec i)) i := fun i => by
    simp only [openingOf, simulateQ_bind, simulateQ_pure]
    rw [Merkle.path_map _ _ (fun b => simulateQ_pure _ b) hbind]
    simp only [hnode, hleaf]
  have hholder : so ∘ₛ holderOf pass sec =
      holderOf (so ∘ₛ pass) (fun i => simulateQ so (sec i)) := by
    funext t
    rcases t with t | i
    · rfl
    · simp only [QueryImpl.apply_compose, holderOf, simulateQ_map, hopen]
  simp only [gameOf, simulateQ_bind, simulateQ_pure, hroot, simulateQ_run_logKeys, hholder,
    QueryImpl.apply_compose]

end Game

/-! ## Three sources of secrets -/

/-- The game of key generation: each secret is the hash of its secret input under the seed. -/
def seedGame (seed : Seed) (adversary : AdaptiveAdversary) :
    OracleComp (unifSpec + HashSpec) Bool :=
  gameOf (QueryImpl.id' _) (fun i => queryHash (secretInput seed i)) adversary

/-- With a fixed table of secrets, the game is the game of uniform secrets. -/
theorem gameOf_pure (secrets : UInt32 → Digest) (adversary : AdaptiveAdversary) :
    gameOf (QueryImpl.id' _) (fun i => pure (secrets i)) adversary =
      adaptiveGame secrets adversary := by
  have hH : (fun x => (QueryImpl.id' (unifSpec + HashSpec)) (.inr x)) = queryHash := rfl
  have hleaf : leafOf queryHash (fun i => pure (secrets i)) = leafWith queryHash secrets := by
    funext j
    simp [leafOf, leafWith]
  have hholder : holderOf (QueryImpl.id' _) (fun i => pure (secrets i)) = honestImpl secrets := by
    funext t
    rcases t with t | i
    · rfl
    · simp only [holderOf, hH, openingOf, hleaf, honestImpl, openingWith, pure_bind]
  simp only [gameOf, adaptiveGame, hH, rootOf, rootWith, hleaf, hholder, pure_bind]
  rfl

/-- The hash beside one derivation per index: the secret at that index. -/
abbrev SeedSpec := HashSpec.withDerivations UInt32 Digest

/-- The game with each secret as a derivation. -/
def seedGameD (adversary : AdaptiveAdversary) : OracleComp SeedSpec Bool :=
  gameOf (HashSpec.withDerivationsLift UInt32 Digest) (fun i => SeedSpec.query (.inr i)) adversary

/-- The secret at index `i` is the hash at the secret input of the seed and `i`. -/
def secretEncoding : SecretEncoding HashSpec Seed UInt32 Digest where
  enc := secretInput
  range_eq _ _ := rfl
  injective _ _ _ h := (secretInput_inj.mp h).2

/-- Answering the derivations with the hash at the secret inputs gives the game of the seed. -/
theorem simulateQ_deriveImpl_seedGameD (seed : Seed) (adversary : AdaptiveAdversary) :
    simulateQ (secretEncoding.deriveImpl seed) (seedGameD adversary) =
      seedGame seed adversary := by
  rw [seedGameD, simulateQ_gameOf, SecretEncoding.deriveImpl_comp_withDerivationsLift]
  rfl

/-- Answering the derivations from a table gives the game of that table. -/
theorem simulateQ_fixDerivations_seedGameD (secrets : UInt32 → Digest)
    (adversary : AdaptiveAdversary) :
    simulateQ (fixDerivations secrets) (seedGameD adversary) = adaptiveGame secrets adversary := by
  rw [seedGameD, simulateQ_gameOf, ← gameOf_pure]
  congr 1

/-! ## The budget of hash queries -/

attribute [local irreducible] VRF_TREE_HEIGHT

/-- A hash query of the game with derived secrets. -/
def IsHashS : SeedSpec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred IsHashS := fun t => by
  rcases t with (_ | _) | _ <;> simp only [IsHashS] <;> infer_instance

/-- The hash of the game with derived secrets. -/
abbrev hashS (x : ByteArray) : OracleComp SeedSpec Digest :=
  (HashSpec.withDerivationsLift UInt32 Digest) (.inr x)

/-- The secret at index `i`, as a derivation. -/
abbrev secretS (i : UInt32) : OracleComp SeedSpec Digest :=
  SeedSpec.query (.inr i)

/-- A leaf is one derivation and one hash query. -/
theorem isQueryBoundP_leafOf (j : Nat) : IsQueryBoundP (leafOf hashS secretS j) IsHashS 1 :=
  (isQueryBoundP_bind (n := 0) (m := 1) (by simp [IsHashS]) fun _ _ => by
    simp [IsHashS, OracleSpec.withDerivationsLift]).mono (by omega)

/-- A node hash is one hash query. -/
theorem isQueryBoundP_nodeWith (l j : Nat) (a b : Digest) :
    IsQueryBoundP (nodeWith hashS l j a b) IsHashS 1 := by
  simp [nodeWith, IsHashS, OracleSpec.withDerivationsLift]

/-- Answering an adversary of `qh` hash queries and `qo` requests costs `qh + qo 2^33` queries. -/
theorem isQueryBoundP_run_logKeys_holderOf {α : Type} (oa : OracleComp AdversarySpec α)
    (S : Finset UInt32) {qh qo : ℕ} (hh : IsQueryBoundP oa IsHashQuery qh)
    (ho : IsQueryBoundP oa IsOpenQuery qo) :
    IsQueryBoundP ((simulateQ (logKeys (holderOf (HashSpec.withDerivationsLift UInt32 Digest)
      secretS) openedIndex) oa).run S) IsHashS (qh + qo * 2 ^ 33) := by
  induction oa using OracleComp.inductionOn generalizing qh qo S with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hh ho
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [logKeys, StateT.run_mk, bind_map_left]
    rcases t with (n | x) | i
    · simp only [IsHashQuery, IsOpenQuery, ite_false] at hh ho
      refine (isQueryBoundP_bind (n := 0) ?_ fun u _ => ih u _ (hh.2 u) (ho.2 u)).mono
        (by omega)
      simp [holderOf, IsHashS, OracleSpec.withDerivationsLift]
    · simp only [IsHashQuery, IsOpenQuery, ite_true, ite_false] at hh ho
      have : 0 < qh := by simpa using hh.1
      refine (isQueryBoundP_bind (n := 1) ?_ fun u _ => ih u _ (hh.2 u) (ho.2 u)).mono
        (by omega)
      simp [holderOf, IsHashS, OracleSpec.withDerivationsLift]
    · simp only [IsHashQuery, IsOpenQuery, ite_true, ite_false] at hh ho
      have : 0 < qo := by simpa using ho.1
      refine (isQueryBoundP_bind (n := 2 ^ 33) ?_ fun u _ => ih u _ (hh.2 u) (ho.2 u)).mono ?_
      · simp only [holderOf]
        rw [isQueryBoundP_map_iff]
        have hpath := isQueryBoundP_siblings (hash := nodeWith hashS)
          (leaves := leafOf hashS secretS)
          isQueryBoundP_leafOf isQueryBoundP_nodeWith 0 i.toNat VRF_TREE_HEIGHT
        exact (isQueryBoundP_bind hpath fun _ _ => isQueryBoundP_bind (n := 0)
          (by simp [IsHashS]) fun _ _ => isQueryBoundP_pure _ _ 0).mono
          (by simp [VRF_TREE_HEIGHT])
      · have : (qo - 1) * 2 ^ 33 + 2 ^ 33 = qo * 2 ^ 33 := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel this]
        omega

/-- The game with derived secrets makes at most `qh + (qo + 1) 2^33` hash queries. -/
theorem isQueryBoundP_seedGameD (adversary : AdaptiveAdversary) {qh qo : ℕ}
    (hh : ∀ r, IsQueryBoundP (adversary r) IsHashQuery qh)
    (ho : ∀ r, IsQueryBoundP (adversary r) IsOpenQuery qo) :
    IsQueryBoundP (seedGameD adversary) IsHashS (qh + (qo + 1) * 2 ^ 33) := by
  have hroot := isQueryBoundP_node (hash := nodeWith hashS) (leaves := leafOf hashS secretS)
    isQueryBoundP_leafOf isQueryBoundP_nodeWith VRF_TREE_HEIGHT 0
  rw [seedGameD, gameOf, rootOf, Merkle.root]
  refine (isQueryBoundP_bind hroot fun r _ =>
    isQueryBoundP_bind (isQueryBoundP_run_logKeys_holderOf (adversary r) ∅ (hh r) (ho r))
      fun z _ => isQueryBoundP_bind (n := 0) (by simp [IsHashS])
        fun s _ => isQueryBoundP_bind (n := 1)
          (by simp [IsHashS, OracleSpec.withDerivationsLift])
          fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
  simp only [VRF_TREE_HEIGHT]
  omega

/-! ## Unpredictability for secrets derived from a seed -/

/-- There are `2^256` seeds of 32 bytes. -/
theorem natCard_seed : Nat.card Seed = 2 ^ 256 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun,
    Fintype.card_fin, ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, VRF_SEED_SIZE]
  norm_num

/-- A given input is a secret input of a uniform seed with probability at most `2^-256`. -/
theorem prEvent_mem_range_secretInput_le (t : ByteArray) :
    Pr{let s ← $ᵗ Seed}[t ∈ Set.range (secretEncoding.enc s)] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have h := Sphincs.Unforgeability.prEvent_mem_range_enc_le secretEncoding
    (fun _ _ _ _ h => (secretInput_inj.mp h).1) t
  rwa [natCard_seed, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **An output is unpredictable when the secrets come from a uniform seed.**

The hash is a lazily sampled random oracle on byte strings, with 32-byte answers.

The seed is uniform, and secret `i` is the hash of its secret input under the seed.

The adversary makes at most `q_H` hash queries and `q_O` requests for an opening on every path.

It names an index and guesses its output there.

It wins if the guess is right and it never asked for the opening at that index.

It wins with probability at most `2^32 (1 + 2 Q) / 2^256 + Q / 2^256`.

Here `Q = q_H + (q_O + 1) 2^33`.

With `q_H = 2^64` and `q_O = 2^32`, the bound is below `2^-157`. -/
theorem prEvent_seedGame_le (adversary : AdaptiveAdversary) {qh qo : ℕ}
    (hh : ∀ r, IsQueryBoundP (adversary r) IsHashQuery qh)
    (ho : ∀ r, IsQueryBoundP (adversary r) IsOpenQuery qo) :
    Pr{let seed ← $ᵗ Seed
       let win ← (simulateQ HashSpec.romImpl (seedGame seed adversary)).run' ∅}[win]
      ≤ 2 ^ 32 * ((2 ^ 256 : ℝ≥0∞)⁻¹ +
          ((qh + (qo + 1) * 2 ^ 33 : ℕ) : ℝ≥0∞) * (2 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        ((qh + (qo + 1) * 2 ^ 33 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hop := Sphincs.Unforgeability.prEvent_romImpl_deriveImpl_le secretEncoding
    (ms := $ᵗ Seed) prEvent_mem_range_secretInput_le (p := IsHashS) (fun _ _ => trivial)
    (isQueryBoundP_seedGameD adversary hh ho) fun _ w => w = true
  have hideal : Pr{
      let seed ← $ᵗ Seed
      let z ← (simulateQ (SecretEncoding.idealImpl HashSpec UInt32 Digest)
        (seedGameD adversary)).run (∅, ∅)}[z.1 = true] ≤
      2 ^ 32 * ((2 ^ 256 : ℝ≥0∞)⁻¹ +
        ((qh + (qo + 1) * 2 ^ 33 : ℕ) : ℝ≥0∞) * (2 * (2 ^ 256 : ℝ≥0∞)⁻¹)) := by
    rw [OracleComp.prEvent_bind_const]
    refine (prEvent_idealImpl_eq_bind_fixDerivations (pub := HashSpec) (X := UInt32)
      (R := Digest) (seedGameD adversary) fun w => w = true).trans_le ?_
    simp only [simulateQ_fixDerivations_seedGameD]
    refine le_of_eq_of_le ?_ (prEvent_adaptiveGame_le adversary hh ho)
    simp [StateT.run'_eq]
  refine le_of_eq_of_le ?_ (hop.trans (add_le_add hideal le_rfl))
  simp [StateT.run'_eq, simulateQ_deriveImpl_seedGameD]

end EthLib.Cryptography.Vrf

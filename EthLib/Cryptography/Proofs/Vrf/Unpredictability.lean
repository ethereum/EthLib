module

public import EthLib.Cryptography.Proofs.Vrf.Verify
public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Proofs: an output is unpredictable to anyone without its secret

Here the hash is a random oracle.

The holder's secret at index `c` is uniform, and independent of its other secrets.

The adversary gets the root, queries the hash, and asks for openings at any index but `c`.

It then guesses the output at `c`.

It wins with probability at most `(1 + 2 Q) / 2^256`, where `Q = q_H + (q_O + 1) 2^33`.

Here `q_H` counts its hash queries and `q_O` its requests for an opening.

The term `1 / 2^256` is the blind guess of a 32-byte output.

The term `2 Q / 2^256` covers a hash query at an input that holds the challenge secret.

It counts every hash call of the game, so it also covers another secret equal to the challenge one.

The other secrets are arbitrary, so the adversary may even know them.

The property is the residual unpredictability of Micali, Rabin and Vadhan, §3.2.

Source: "Verifiable Random Functions", [FOCS 1999](https://doi.org/10.1109/SFFCS.1999.814584).

There the adversary chooses the index after its queries; here the index is fixed in advance.

A separate theorem covers an adaptive index, with uniform secrets, at the cost of a factor `2^32`.

A challenge secret derived from a seed is not covered.

A separate theorem covers secrets derived from a seed, but only at an adaptive index.

The theorem does not cover a holder who chooses its secrets.

Such a holder can bias its own outputs, because verification accepts any tree.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants
open OracleSpec OracleComp ENNReal

/-! ## The tree over a hash oracle -/

section Oracle

variable {m : Type → Type} [Monad m] (H : ByteArray → m Digest)

/-- The node hash of the tree, with `H` in place of Keccak-256. -/
def nodeWith (_level _j : Nat) (left right : Digest) : m Digest :=
  H (nodeInput left right)

/-- Leaf `j` of the tree over the secrets, with `H` in place of Keccak-256. -/
def leafWith (secrets : UInt32 → Digest) (j : Nat) : m Digest :=
  H (leafInput (secrets (UInt32.ofNat j)))

/-- The root of the tree over the secrets, with `H` in place of Keccak-256. -/
def rootWith (secrets : UInt32 → Digest) : m Digest :=
  Merkle.root (nodeWith H) (leafWith H secrets) VRF_TREE_HEIGHT

/-- The opening at index `i`, with `H` in place of Keccak-256. -/
def openingWith (secrets : UInt32 → Digest) (i : UInt32) : m Opening := do
  let path ← Merkle.path (nodeWith H) (leafWith H secrets) VRF_TREE_HEIGHT i.toNat
  return ⟨secrets i, path⟩

end Oracle

/-- With Keccak-256 as `H`, the root is the root of the specification. -/
theorem rootWith_hash (secrets : UInt32 → Digest) :
    (rootWith (m := Id) (fun x => pure (hash x)) secrets).run = root secrets :=
  rfl

/-- With Keccak-256 as `H`, the opening is the opening of the specification. -/
theorem openingWith_hash (secrets : UInt32 → Digest) (i : UInt32) :
    (openingWith (m := Id) (fun x => pure (hash x)) secrets i).run = opening secrets i :=
  rfl

/-! ## The game -/

/-- The hash as an oracle from byte strings to 32-byte values. -/
abbrev HashSpec := ByteArray →ₒ Digest

/-- The holder's opening oracle: an index in, an opening or nothing out. -/
abbrev OpenSpec := UInt32 →ₒ Option Opening

/-- What the adversary may query: private uniform sampling, the hash, and the opening oracle. -/
abbrev AdversarySpec := unifSpec + HashSpec + OpenSpec

/-- An adversary: from the root, it queries the hash and asks for openings, then guesses. -/
abbrev Adversary := Digest → OracleComp AdversarySpec Digest

/-- One query to the hash oracle. -/
def queryHash (x : ByteArray) : OracleComp (unifSpec + HashSpec) Digest :=
  (unifSpec + HashSpec).query (.inr x)

/-- The holder answers the adversary: sampling and hash queries pass through.

An opening at index `i` is the honest opening, except at the challenge index `c`. -/
def openImpl (secrets : UInt32 → Digest) (c : UInt32) :
    QueryImpl AdversarySpec (OracleComp (unifSpec + HashSpec))
  | .inl t => (unifSpec + HashSpec).query t
  | .inr i => if i = c then pure none else some <$> openingWith queryHash secrets i

/-- The game of the output at index `c`, in the random oracle model.

The secret at `c` is `s`, and the other secrets are those of `others`.

The adversary gets the root, queries the hash, and asks for openings at indices other than `c`.

It returns a guess, and the game returns the guess with the output at `c`. -/
def game (others : UInt32 → Digest) (c : UInt32) (s : Digest) (adversary : Adversary) :
    OracleComp (unifSpec + HashSpec) (Digest × Digest) := do
  let secrets := Function.update others c s
  let r ← rootWith queryHash secrets
  let guess ← simulateQ (openImpl secrets c) (adversary r)
  let output ← queryHash (outputInput s)
  return (guess, output)

/-! ## The game with the challenge leaf and output as derivations

The challenge leaf and the output are the hash at two inputs that contain the secret.

Read as derivations of the secret, they fit the hidden-seed argument of VCVio.

That argument replaces them by independent values, until a hash query hits one of the two inputs. -/

/-- The hash beside two derivations: `false` is the challenge leaf, `true` its output. -/
abbrev DerivedSpec := HashSpec.withDerivations Bool Digest

/-- One query to the hash, in the derivation world. -/
def hashD (x : ByteArray) : OracleComp DerivedSpec Digest := DerivedSpec.query (.inl (.inr x))

/-- One derivation query. -/
def deriveD (b : Bool) : OracleComp DerivedSpec Digest := DerivedSpec.query (.inr b)

/-- Leaf `j`, with the challenge leaf as a derivation. -/
def leafD (others : UInt32 → Digest) (c : UInt32) (j : Nat) : OracleComp DerivedSpec Digest :=
  if UInt32.ofNat j = c then deriveD false else hashD (leafInput (others (UInt32.ofNat j)))

/-- The holder's answers, with the challenge leaf as a derivation. -/
def openImplD (others : UInt32 → Digest) (c : UInt32) :
    QueryImpl AdversarySpec (OracleComp DerivedSpec)
  | .inl t => DerivedSpec.query (.inl t)
  | .inr i => if i = c then pure none else some <$> (do
      let path ← Merkle.path (nodeWith hashD) (leafD others c) VRF_TREE_HEIGHT i.toNat
      return ⟨others i, path⟩)

/-- The game, with the challenge leaf and the output as derivations. -/
def gameD (others : UInt32 → Digest) (c : UInt32) (adversary : Adversary) :
    OracleComp DerivedSpec (Digest × Digest) := do
  let r ← Merkle.root (nodeWith hashD) (leafD others c) VRF_TREE_HEIGHT
  let guess ← simulateQ (openImplD others c) (adversary r)
  let output ← deriveD true
  return (guess, output)

/-- The challenge leaf and the output are the hash at two points of the secret. -/
def encoding : SecretEncoding HashSpec Digest Bool Digest where
  enc s b := if b then outputInput s else leafInput s
  range_eq _ _ := rfl
  injective s b b' h := by
    cases b <;> cases b' <;>
      simp_all [leafInput_ne_outputInput, (leafInput_ne_outputInput _ _).symm]

/-- Answering the derivations with the hash at the secret's points gives the game. -/
theorem simulateQ_deriveImpl_gameD (others : UInt32 → Digest) (c : UInt32) (s : Digest)
    (adversary : Adversary) :
    simulateQ (encoding.deriveImpl s) (gameD others c adversary) = game others c s adversary := by
  have hhash : ∀ x, simulateQ (encoding.deriveImpl s) (hashD x) = queryHash x := fun x => by
    simp [hashD, queryHash, SecretEncoding.deriveImpl]
  have hderive : ∀ b, simulateQ (encoding.deriveImpl s) (deriveD b) =
      queryHash (encoding.enc s b) := fun b => by
    simp [deriveD, queryHash, SecretEncoding.deriveImpl]
  have hleaf : ∀ j, simulateQ (encoding.deriveImpl s) (leafD others c j) =
      leafWith queryHash (Function.update others c s) j := fun j => by
    unfold leafD leafWith
    split
    · rename_i h
      rw [hderive, h, Function.update_self]
      rfl
    · rename_i h
      rw [hhash, Function.update_of_ne h]
  have hbind : ∀ {β γ : Type} (x : OracleComp DerivedSpec β) (f : β → OracleComp DerivedSpec γ),
      simulateQ (encoding.deriveImpl s) (x >>= f) =
        simulateQ (encoding.deriveImpl s) x >>= fun b => simulateQ (encoding.deriveImpl s) (f b) :=
    fun x f => simulateQ_bind _ _ _
  have hnode : ∀ (l j : Nat) (a b : Digest),
      simulateQ (encoding.deriveImpl s) (nodeWith hashD l j a b) = nodeWith queryHash l j a b :=
    fun _ _ _ _ => hhash _
  have hpath : ∀ i : UInt32, simulateQ (encoding.deriveImpl s)
      (Merkle.path (nodeWith hashD) (leafD others c) VRF_TREE_HEIGHT i.toNat) =
      Merkle.path (nodeWith queryHash) (leafWith queryHash (Function.update others c s))
        VRF_TREE_HEIGHT i.toNat := fun i => by
    rw [Merkle.path_map _ _ (fun b => simulateQ_pure _ b) hbind]
    simp only [hnode, hleaf]
  have hroot : simulateQ (encoding.deriveImpl s)
      (Merkle.root (nodeWith hashD) (leafD others c) VRF_TREE_HEIGHT) =
      rootWith queryHash (Function.update others c s) := by
    rw [Merkle.root, Merkle.node_map _ _ hbind]
    simp only [hnode, hleaf]
    rfl
  have himpl : encoding.deriveImpl s ∘ₛ openImplD others c =
      openImpl (Function.update others c s) c := by
    funext t
    rcases t with t | i
    · simp [QueryImpl.apply_compose, openImplD, openImpl, SecretEncoding.deriveImpl]
    · simp only [QueryImpl.apply_compose, openImplD, openImpl]
      split_ifs with h
      · simp
      · simp only [openingWith, simulateQ_map, simulateQ_bind, simulateQ_pure, hpath,
          Function.update_of_ne h]
  simp only [gameD, game, simulateQ_bind, simulateQ_pure, hderive, hroot,
    ← QueryImpl.simulateQ_compose, himpl]
  rfl

/-! ## Counting hash queries

A node of level `l` hashes its `2^l` leaves and its `2^l - 1` inner nodes. -/

section Count

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p] {α : Type}
  {hash : Nat → Nat → α → α → OracleComp spec α} {leaves : Nat → OracleComp spec α}

/-- A node of level `l` makes at most `2^(l + 1) - 1` queries, one per leaf and per hash. -/
theorem isQueryBoundP_node (hleaves : ∀ j, IsQueryBoundP (leaves j) p 1)
    (hhash : ∀ l j a b, IsQueryBoundP (hash l j a b) p 1) :
    ∀ level j, IsQueryBoundP (Merkle.node hash leaves level j) p (2 ^ (level + 1) - 1)
  | 0, j => hleaves j
  | level + 1, j => by
    rw [Merkle.node_succ]
    have h1 : 1 ≤ 2 ^ (level + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (level + 1 + 1) = 2 * 2 ^ (level + 1) := by rw [pow_succ]; ring
    refine (isQueryBoundP_bind (isQueryBoundP_node hleaves hhash level _) fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_node hleaves hhash level _) fun _ _ =>
        hhash _ _ _ _).mono ?_
    omega

/-- The `n` siblings above a node of level `l` make at most `2^(l + n + 1) - 2^(l + 1)` queries. -/
theorem isQueryBoundP_siblings (hleaves : ∀ j, IsQueryBoundP (leaves j) p 1)
    (hhash : ∀ l j a b, IsQueryBoundP (hash l j a b) p 1) :
    ∀ level j n, IsQueryBoundP (Merkle.siblings hash leaves level j n) p
      (2 ^ (level + n + 1) - 2 ^ (level + 1))
  | level, j, 0 => by simp [Merkle.siblings]
  | level, j, n + 1 => by
    simp only [Merkle.siblings]
    have h1 : 1 ≤ 2 ^ (level + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (level + 1 + 1) = 2 * 2 ^ (level + 1) := by rw [pow_succ]; ring
    have h3 : 2 ^ (level + 1 + 1) ≤ 2 ^ (level + 1 + n + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : level + (n + 1) + 1 = level + 1 + n + 1 := by omega
    rw [h4]
    refine (isQueryBoundP_bind (isQueryBoundP_node hleaves hhash level _) fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_siblings hleaves hhash (level + 1) (j / 2) n) fun _ _ =>
        isQueryBoundP_pure _ _ 0).mono ?_
    omega

end Count

/-! ## The budgets -/

attribute [local irreducible] VRF_TREE_HEIGHT

/-- A query of the derivation world to the hash. -/
def IsHashD : DerivedSpec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred IsHashD := fun t => by
  rcases t with (_ | _) | _ <;> simp only [IsHashD] <;> infer_instance

/-- An adversary's query to the hash. -/
def IsHashQuery : AdversarySpec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred IsHashQuery := fun t => by
  rcases t with (_ | _) | _ <;> simp only [IsHashQuery] <;> infer_instance

/-- An adversary's request for an opening. -/
def IsOpenQuery : AdversarySpec.Domain → Prop
  | .inr _ => True
  | _ => False

instance : DecidablePred IsOpenQuery := fun t => by
  rcases t with (_ | _) | _ <;> simp only [IsOpenQuery] <;> infer_instance

/-- A hash query is one hash query. -/
theorem isQueryBoundP_hashD (x : ByteArray) : IsQueryBoundP (hashD x) IsHashD 1 := by
  simp [hashD, IsHashD]

/-- A derivation is no hash query. -/
theorem isQueryBoundP_deriveD (b : Bool) : IsQueryBoundP (deriveD b) IsHashD 0 := by
  simp [deriveD, IsHashD]

/-- A leaf is at most one hash query. -/
theorem isQueryBoundP_leafD (others : UInt32 → Digest) (c : UInt32) (j : Nat) :
    IsQueryBoundP (leafD others c j) IsHashD 1 := by
  unfold leafD
  split
  · exact (isQueryBoundP_deriveD _).mono (by omega)
  · exact isQueryBoundP_hashD _

/-- The path of an opening in a tree of height `n` makes fewer than `2^(n + 1)` hash queries. -/
theorem isQueryBoundP_pathD (others : UInt32 → Digest) (c : UInt32) (n i : Nat) :
    IsQueryBoundP (Merkle.path (nodeWith hashD) (leafD others c) n i) IsHashD (2 ^ (n + 1)) := by
  have h := isQueryBoundP_siblings (hash := nodeWith hashD) (leaves := leafD others c)
    (isQueryBoundP_leafD others c) (fun _ _ a b => isQueryBoundP_hashD (nodeInput a b)) 0 i n
  exact h.mono (by simp)

/-- The root of a tree of height `n` makes fewer than `2^(n + 1)` hash queries. -/
theorem isQueryBoundP_rootD (others : UInt32 → Digest) (c : UInt32) (n : Nat) :
    IsQueryBoundP (Merkle.root (nodeWith hashD) (leafD others c) n) IsHashD (2 ^ (n + 1)) := by
  have h := isQueryBoundP_node (hash := nodeWith hashD) (leaves := leafD others c)
    (isQueryBoundP_leafD others c) (fun _ _ a b => isQueryBoundP_hashD (nodeInput a b)) n 0
  exact h.mono (Nat.sub_le _ _)

/-- Answering an adversary of `qh` hash queries and `qo` requests costs `qh + qo 2^33` queries. -/
theorem isQueryBoundP_simulateQ_openImplD (others : UInt32 → Digest) (c : UInt32) {α : Type}
    (oa : OracleComp AdversarySpec α) {qh qo : ℕ} (hh : IsQueryBoundP oa IsHashQuery qh)
    (ho : IsQueryBoundP oa IsOpenQuery qo) :
    IsQueryBoundP (simulateQ (openImplD others c) oa) IsHashD (qh + qo * 2 ^ 33) := by
  induction oa using OracleComp.inductionOn generalizing qh qo with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hh ho
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with (n | x) | i
    · simp only [IsHashQuery, IsOpenQuery, ite_false] at hh ho
      refine (isQueryBoundP_bind (n := 0) ?_ fun u _ => ih u (hh.2 u) (ho.2 u)).mono (by omega)
      simp [openImplD, IsHashD]
    · simp only [IsHashQuery, IsOpenQuery, ite_true, ite_false] at hh ho
      have : 0 < qh := by simpa using hh.1
      refine (isQueryBoundP_bind (n := 1) ?_ fun u _ => ih u (hh.2 u) (ho.2 u)).mono (by omega)
      simp [openImplD, IsHashD]
    · simp only [IsHashQuery, IsOpenQuery, ite_true, ite_false] at hh ho
      have : 0 < qo := by simpa using ho.1
      refine (isQueryBoundP_bind (n := 2 ^ 33) ?_ fun u _ => ih u (hh.2 u) (ho.2 u)).mono ?_
      · simp only [openImplD]
        split
        · exact isQueryBoundP_pure _ _ _
        · rw [isQueryBoundP_map_iff]
          exact (isQueryBoundP_bind (isQueryBoundP_pathD others c VRF_TREE_HEIGHT _) fun _ _ =>
            isQueryBoundP_pure _ _ 0).mono (by simp [VRF_TREE_HEIGHT])
      · have : (qo - 1) * 2 ^ 33 + 2 ^ 33 = qo * 2 ^ 33 := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel this]
        omega

/-- The game makes at most `qh + (qo + 1) 2^33` hash queries. -/
theorem isQueryBoundP_gameD (others : UInt32 → Digest) (c : UInt32) (adversary : Adversary)
    {qh qo : ℕ} (hh : ∀ r, IsQueryBoundP (adversary r) IsHashQuery qh)
    (ho : ∀ r, IsQueryBoundP (adversary r) IsOpenQuery qo) :
    IsQueryBoundP (gameD others c adversary) IsHashD (qh + (qo + 1) * 2 ^ 33) := by
  have h2 : ∀ r, IsQueryBoundP (do
      let guess ← simulateQ (openImplD others c) (adversary r)
      let output ← deriveD true
      return (guess, output)) IsHashD (qh + qo * 2 ^ 33) := fun r =>
    (isQueryBoundP_bind (isQueryBoundP_simulateQ_openImplD others c _ (hh r) (ho r)) fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_deriveD true) fun _ _ =>
        isQueryBoundP_pure _ _ 0).mono (by omega)
  have h := isQueryBoundP_bind (isQueryBoundP_rootD others c VRF_TREE_HEIGHT) fun r _ => h2 r
  rw [gameD]
  exact h.mono (by simp only [VRF_TREE_HEIGHT]; omega)

/-! ## One point of the secret -/

/-- There are `2^256` values of 32 bytes. -/
theorem natCard_digest : Nat.card Digest = 2 ^ 256 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun,
    Fintype.card_fin, ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, VRF_HASH_SIZE]
  norm_num

/-- A given input is one of the two points of a uniform secret with probability `<= 2 / 2^256`. -/
theorem prEvent_mem_range_enc_le (t : ByteArray) :
    Pr{let s ← $ᵗ Digest}[t ∈ Set.range (encoding.enc s)] ≤ 2 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hone : ∀ {f : Digest → ByteArray}, Function.Injective f →
      Pr{let s ← $ᵗ Digest}[f s = t] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := fun hf => by
    have := SampleableType.prEvent_uniformSample_apply_eq_le hf t
    rwa [natCard_digest, Nat.cast_pow, Nat.cast_ofNat] at this
  calc Pr{let s ← $ᵗ Digest}[t ∈ Set.range (encoding.enc s)]
      ≤ Pr{let s ← $ᵗ Digest}[leafInput s = t ∨ outputInput s = t] :=
        prEvent_mono _ _ _ fun s ⟨b, hb⟩ => by
          cases b
          · exact Or.inl hb
          · exact Or.inr hb
    _ ≤ Pr{let s ← $ᵗ Digest}[leafInput s = t] + Pr{let s ← $ᵗ Digest}[outputInput s = t] :=
        prEvent_or_le _ _ _
    _ ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ + (2 ^ 256 : ℝ≥0∞)⁻¹ :=
        add_le_add (hone fun _ _ h => leafInput_inj.mp h) (hone fun _ _ h => outputInput_inj.mp h)
    _ = 2 * (2 ^ 256 : ℝ≥0∞)⁻¹ := (two_mul _).symm

/-! ## The ideal game -/

/-- Every query of a program over the adversary's oracles is allowed by the trivial predicate. -/
theorem allQueriesSatisfy_true {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) : AllQueriesSatisfy oa fun _ => True := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨trivial, ih⟩

/-- A query other than the derivation of the output. -/
def NotOutput (t : DerivedSpec.Domain) : Prop := t ≠ .inr true

/-- Before the output, the game never queries the output's derivation. -/
theorem allQueriesSatisfy_beforeOutput (others : UInt32 → Digest) (c : UInt32)
    (adversary : Adversary) :
    AllQueriesSatisfy (do
      let r ← Merkle.root (nodeWith hashD) (leafD others c) VRF_TREE_HEIGHT
      simulateQ (openImplD others c) (adversary r)) NotOutput := by
  have hleaf : ∀ j, AllQueriesSatisfy (leafD others c j) NotOutput := fun j => by
    unfold leafD hashD deriveD
    split <;> simp [NotOutput]
  have hnode : ∀ l j a b, AllQueriesSatisfy (nodeWith hashD l j a b) NotOutput :=
    fun _ _ _ _ => by simp [nodeWith, hashD, NotOutput]
  refine allQueriesSatisfy_bind ?_ fun r => (allQueriesSatisfy_true (adversary r)).simulateQ ?_
  · rw [Merkle.root]
    exact Merkle.node_rec (nodeWith hashD)
      (fun {β} (x : OracleComp DerivedSpec β) => AllQueriesSatisfy x NotOutput)
      allQueriesSatisfy_bind _ hleaf hnode _ _
  · rintro (t | i) -
    · simp [openImplD, NotOutput]
    · simp only [openImplD]
      split
      · exact allQueriesSatisfy_pure _ _
      · rw [map_eq_bind_pure_comp]
        refine allQueriesSatisfy_bind ?_ fun _ => allQueriesSatisfy_pure _ _
        exact allQueriesSatisfy_bind (Merkle.siblings_rec (nodeWith hashD)
          (fun {β} (x : OracleComp DerivedSpec β) => AllQueriesSatisfy x NotOutput)
          (fun _ => allQueriesSatisfy_pure _ _) allQueriesSatisfy_bind _ hleaf hnode _ _ _)
          fun _ => allQueriesSatisfy_pure _ _

/-- In the ideal game, the fresh uniform output is guessed with chance at most `2^-256`. -/
theorem prEvent_idealImpl_gameD_le (others : UInt32 → Digest) (c : UInt32)
    (adversary : Adversary) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl HashSpec Bool Digest)
        (gameD others c adversary)).run (∅, ∅)}[
      z.1.1 = z.1.2] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hg : gameD others c adversary = (do
      let r ← Merkle.root (nodeWith hashD) (leafD others c) VRF_TREE_HEIGHT
      simulateQ (openImplD others c) (adversary r)) >>= fun guess =>
        deriveD true >>= fun output => pure (guess, output) := by
    simp only [gameD, bind_assoc]
  rw [hg, simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun w hw => ?_
  have hnone : w.2.2 true = none := by
    have := (allQueriesSatisfy_beforeOutput others c adversary).holds_of_mem_support_run_simulateQ
      (fun st : SecretEncoding.SplitCache HashSpec Bool Digest => st.2 true = none)
      (fun t ht st hst z hz => by
        have h := SecretEncoding.isSome_snd_apply_iff_of_mem_support_idealImpl hz true
        rw [hst] at h
        simp only [Option.isSome_none, Bool.false_eq_true, false_or] at h
        exact Option.not_isSome_iff_eq_none.mp fun hs => ht (h.mp hs).symm)
      rfl hw
    exact this
  simp only [deriveD, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
    SecretEncoding.idealImpl, StateT.run_mk, randomOracle.run_eq, hnone]
  simp only [StateT.run_pure, bind_pure_comp,
    prEvent_map]
  calc _ ≤ Pr{let u ← $ᵗ Digest}[id u = w.1] := prEvent_mono _ _ _ fun _ h => h.symm
    _ ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
      have := SampleableType.prEvent_uniformSample_apply_eq_le Function.injective_id w.1
      rwa [natCard_digest, Nat.cast_pow, Nat.cast_ofNat] at this

/-! ## Unpredictability -/

/-- **An output is unpredictable to anyone without its secret.**

The hash is a lazily sampled random oracle on byte strings, with 32-byte answers.

The secret at `c` is uniform, and the secrets at the other indices are any fixed values.

The adversary makes at most `q_H` hash queries and `q_O` requests for an opening on every path.

It never gets the opening at `c`.

Then its guess equals the output at `c` with probability at most `(1 + 2 Q) / 2^256`.

Here `Q = q_H + (q_O + 1) 2^33`.

With `q_H = 2^64` and `q_O = 2^32`, the bound is below `2^-189`. -/
theorem prEvent_guess_le (others : UInt32 → Digest) (c : UInt32) (adversary : Adversary)
    {qh qo : ℕ} (hh : ∀ r, IsQueryBoundP (adversary r) IsHashQuery qh)
    (ho : ∀ r, IsQueryBoundP (adversary r) IsOpenQuery qo) :
    Pr{let s ← $ᵗ Digest
       let z ← (simulateQ HashSpec.romImpl (game others c s adversary)).run' ∅}[z.1 = z.2]
      ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ + ((qh + (qo + 1) * 2 ^ 33 : ℕ) : ℝ≥0∞) * (2 * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  have hreal : ∀ s, (simulateQ HashSpec.romImpl (game others c s adversary)).run' ∅ =
      Prod.fst <$> (simulateQ (encoding.realImpl s) (gameD others c adversary)).run ∅ := by
    intro s
    rw [← simulateQ_deriveImpl_gameD, SecretEncoding.realImpl, QueryImpl.simulateQ_compose]
    rfl
  have hideal : Pr{let s ← $ᵗ Digest; let z ← (simulateQ
      (SecretEncoding.idealImpl HashSpec Bool Digest) (gameD others c adversary)).run (∅, ∅)}[
        z.1.1 = z.1.2] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    rw [OracleComp.prEvent_bind_const]
    exact prEvent_idealImpl_gameD_le others c adversary
  calc _ = Pr{let s ← $ᵗ Digest; let z ← (simulateQ (encoding.realImpl s)
          (gameD others c adversary)).run ∅}[z.1.1 = z.1.2] := by
        simp only [hreal, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
        rfl
    _ ≤ _ := (encoding.prEvent_realImpl_le_add_mul (ms := $ᵗ Digest) prEvent_mem_range_enc_le
        (p := IsHashD) (fun _ _ => trivial) (isQueryBoundP_gameD others c adversary hh ho)
        fun _ z => z.1.1 = z.1.2).trans (add_le_add hideal le_rfl)

end EthLib.Cryptography.Vrf

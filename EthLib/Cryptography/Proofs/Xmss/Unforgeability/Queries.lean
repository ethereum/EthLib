module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Game

/-!
# Proofs: the leanXMSS bound, with the adversary's queries and requests apart

The bound of the game counts every hash call, the signer's included.

This file restates it with the adversary's hash queries `qH` and signing requests `qS` apart.

Take an adversary with at most `qH` hash queries and `qS` signing requests.

It forges with probability at most `(qH + 8,630,239,199 * qS + 13,435,265) / 2^127`.

The proof bounds the hash calls of each part of the game, then applies the bound of the game.

- A signing request makes at most `8,630,239,199` calls, about `2^33.007`.
  These are `S`, `P`, up to `2^32` randomizer trials on each layer, the chains, two paths and the
  root of the bottom tree.
- Key generation makes `13,434,881` calls, and a verification at most `384`.

The coefficient of `qS` is the most calls the signer can make, not what the adversary learns.

So with all `2^32` leaf indices signed, the bound is still above `2^-62`.

The leanSig paper counts a signing request in the same way.

Its random-oracle bound for the message hash counts `q' = q + p * K` calls.

There `q` counts the adversary's queries, `p` its signing queries, and `K` the calls of each one.

Source: Drake, Khovratovich, Kudinov and Wagner, IACR Communications in Cryptology 2(1), 2025.

Its title is "Hash-Based Multi-Signatures for Post-Quantum Ethereum".

The bound is Table 1 of section 3.1, applied in Corollary 2 of section 5.2.

<https://eprint.iacr.org/2025/055>
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open XmssSecurity (HashSpec OracleWorld)
open XmssSecurity.Bridge (QueryCount nodeQueries queryCount_queryH queryCount_th queryCount_chain
  queryCount_chainStarts queryCount_node)

/-! ## Counting the adversary's queries

The bound below counts only what the adversary asks for, as Bellare and Rogaway do.

Source: Bellare and Rogaway, "The Exact Security of Digital Signatures", EUROCRYPT 1996.

The forger is defined in its section 2.2.

<https://web.cs.ucdavis.edu/~rogaway/papers/exact.pdf>

A forger there makes at most `q_sig` signing queries and `q_hash` hash queries of its own. -/

/-- A query of the adversary to `H`. -/
abbrev IsHashQuery (t : (OracleWorld + SigningSpec).Domain) : Prop :=
  (t matches .inl (.inr _)) = true

/-- A signing request of the adversary. -/
abbrev IsSignRequest (t : (OracleWorld + SigningSpec).Domain) : Prop :=
  (t matches .inr _) = true

/-- Whatever the public key and the answers, the adversary makes at most `qH` hash queries.

It also makes at most `qS` signing requests.

Its coins are free. -/
def MakesAtMost (adversary : Adversary) (qH qS : Nat) : Prop :=
  ∀ pk, (adversary.main pk).IsQueryBoundP IsHashQuery qH ∧
    (adversary.main pk).IsQueryBoundP IsSignRequest qS

/-- An adversary with at most `qH` hash queries and `qS` signing requests forges rarely.

Its probability is at most `(qH + perRequest * qS + fixed) / 2^bits`.

`perRequest` is what one signing request costs, and `fixed` what the game costs once. -/
def HasQuerySecurityBits (bits perRequest fixed : Nat) : Prop :=
  ∀ qH qS adversary, MakesAtMost adversary qH qS →
    forgeAdvantage adversary ≤ ((qH + perRequest * qS + fixed : Nat) : ℝ≥0∞) /
      ((2 ^ bits : Nat) : ℝ≥0∞)

/-! ## Counting the hash calls of EthLib's algorithms -/

/-- At most `n` calls of `H` on every path. -/
abbrev AtMost {α : Type} (c : OracleComp HashSpec α) (n : Nat) : Prop :=
  c.IsQueryBoundP (fun _ => True) n

theorem atMost_of_queryCount {α : Type} {c : OracleComp HashSpec α} {n : Nat}
    (h : QueryCount c n) : AtMost c n := by
  induction h with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query x next n _ ih =>
    rw [AtMost, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr (Nat.succ_pos _), fun a => by simpa using ih a⟩

theorem AtMost.bind {α β : Type} {c : OracleComp HashSpec α} {f : α → OracleComp HashSpec β}
    {n m : Nat} (hc : AtMost c n) (hf : ∀ a, AtMost (f a) m) : AtMost (c >>= f) (n + m) :=
  isQueryBoundP_bind hc fun a _ => hf a

theorem AtMost.mono {α : Type} {c : OracleComp HashSpec α} {n m : Nat} (hc : AtMost c n)
    (h : n ≤ m) : AtMost c m :=
  IsQueryBoundP.mono hc h

theorem atMost_pure {α : Type} (a : α) (n : Nat) : AtMost (pure a : OracleComp HashSpec α) n :=
  isQueryBoundP_pure _ _ _

theorem AtMost.map {α β : Type} {c : OracleComp HashSpec α} {n : Nat} (hc : AtMost c n)
    (g : α → β) : AtMost (g <$> c) n :=
  (isQueryBoundP_map_iff c g n).2 hc

/-- `k` computations in order, each with at most `n` calls, make at most `k * n`. -/
theorem AtMost.ofFnInOrder {α : Type} {k n : Nat} {c : Fin k → OracleComp HashSpec α}
    (h : ∀ i, AtMost (c i) n) : AtMost (Xmss.ofFnInOrder k c) (k * n) := by
  rw [ofFnInOrder_eq_map_sequenceFin]
  refine AtMost.map ?_ _
  induction k with
  | zero =>
    simp only [XmssSecurity.Concrete.sequenceFin, Nat.zero_mul]
    exact atMost_pure _ _
  | succ k ih =>
    simp only [XmssSecurity.Concrete.sequenceFin]
    have h' := (h 0).bind fun head => (ih (c := fun i => c i.succ) fun i => h i.succ).bind
      (f := fun tail => (pure (Fin.cases head tail) : OracleComp HashSpec (Fin (k + 1) → α)))
      fun tail => atMost_pure _ 0
    exact h'.mono (by rw [Nat.succ_mul]; omega)

/-! ## Signing -/

/-- Each randomizer trial makes one call. -/
theorem atMost_findCodeword (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) : ∀ (c fuel : Nat),
    AtMost (Internal.findCodeword (queryH (m := OracleComp HashSpec)) pp layer e msg base c fuel)
      fuel
  | _, 0 => by
    rw [Internal.findCodeword]
    exact atMost_pure _ _
  | c, fuel + 1 => by
    rw [Internal.findCodeword, show fuel + 1 = 1 + fuel from Nat.add_comm _ _]
    unfold messageDigest
    refine (atMost_of_queryCount (queryCount_th _ _ _)).bind fun digest => ?_
    split
    · exact atMost_pure _ _
    · exact atMost_findCodeword pp layer e msg base (c + 1) fuel

theorem atMost_node (pp : PublicParam) (s : Seed) (layer : Layer) (level j : Nat) :
    AtMost (node (queryH (m := OracleComp HashSpec)) pp s layer level j) (nodeQueries level) :=
  atMost_of_queryCount (queryCount_node pp s layer level j)

/-- The hash calls of `n` siblings, from `level` up. -/
def siblingQueries : Nat → Nat → Nat
  | _, 0 => 0
  | level, n + 1 => nodeQueries level + siblingQueries (level + 1) n

theorem queryCount_siblings (pp : PublicParam) (s : Seed) (layer : Layer) :
    ∀ (level j n : Nat),
      QueryCount (Merkle.siblings (nodeHash (queryH (m := OracleComp HashSpec)) pp layer)
        (leaves queryH pp s layer) level j n) (siblingQueries level n)
  | _, _, 0 => by
    rw [Merkle.siblings]
    exact .pure _
  | level, j, n + 1 => by
    rw [Merkle.siblings, siblingQueries, ← Nat.add_zero (siblingQueries (level + 1) n)]
    exact (queryCount_node pp s layer level _).bind fun _ =>
      (queryCount_siblings pp s layer (level + 1) _ n).bind fun _ => .pure _

/-- The hash calls of a path: every sibling's subtree is rebuilt. -/
def pathQueries : Nat := siblingQueries 0 LAYER_HEIGHT

theorem queryCount_path (pp : PublicParam) (s : Seed) (layer : Layer) (e : Nat) :
    QueryCount (path (queryH (m := OracleComp HashSpec)) pp s layer e) pathQueries :=
  queryCount_siblings pp s layer 0 e LAYER_HEIGHT

/-- The most hash calls of one layer's signature.

The randomizer base, every trial, the chain starts, every chain walked to its end, and the path. -/
def layerSignQueries : Nat := 1 + MAX_RANDOMIZER_TRIALS + 29 + V * 3 + pathQueries

/-- The randomizer base, the trials, the chain starts, and each chain walked at most 3 steps. -/
theorem atMost_otsSign (pp : PublicParam) (s : Seed) (layer : Layer) (e : UInt32)
    (msg : ByteArray) :
    AtMost (otsSign (queryH (m := OracleComp HashSpec)) pp s layer e msg)
      (1 + MAX_RANDOMIZER_TRIALS + 29 + V * 3) := by
  unfold otsSign randomizerBase
  rw [show 1 + MAX_RANDOMIZER_TRIALS + 29 + V * 3
    = 1 + (MAX_RANDOMIZER_TRIALS + (29 + (V * 3 + 0))) by omega]
  refine (atMost_of_queryCount (queryCount_th _ _ _)).bind fun base => ?_
  refine (atMost_findCodeword _ _ _ _ _ 0 _).bind fun found => ?_
  split
  · refine (atMost_of_queryCount (queryCount_chainStarts _ _ _ _)).bind fun starts => ?_
    refine (AtMost.ofFnInOrder fun i => ?_).bind fun _ => atMost_pure _ _
    exact (atMost_of_queryCount (queryCount_chain _ _ _ _ _ _ _ _)).mono
      (by have := (‹Vector (Fin CHAIN_LENGTH) V›[i]).isLt; simp only [CHAIN_LENGTH] at this; omega)
  · exact atMost_pure _ _

theorem atMost_signLayer (pp : PublicParam) (s : Seed) (layer : Layer) (e : Nat)
    (msg : ByteArray) :
    AtMost (signLayer (queryH (m := OracleComp HashSpec)) pp s layer e msg) layerSignQueries := by
  unfold signLayer
  refine (atMost_otsSign pp s layer _ msg).bind fun signed => ?_
  split
  · exact (atMost_of_queryCount (queryCount_path _ _ _ _)).bind fun _ => atMost_pure _ 0
  · exact atMost_pure _ _

/-- The most hash calls of one signing request.

`S` and `P`, both layers' signatures, and the bottom tree's root. -/
def signQueries : Nat := 2 + 2 * layerSignQueries + nodeQueries LAYER_HEIGHT

theorem atMost_signDerived (s : Seed) (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    AtMost (signDerived (queryH (m := OracleComp HashSpec)) s pp idx msg)
      (2 * layerSignQueries + nodeQueries LAYER_HEIGHT) := by
  unfold signDerived
  rw [show 2 * layerSignQueries + nodeQueries LAYER_HEIGHT
    = layerSignQueries + (nodeQueries LAYER_HEIGHT + (layerSignQueries + 0)) by
      generalize layerSignQueries = a; generalize nodeQueries LAYER_HEIGHT = b; omega]
  refine (atMost_signLayer _ _ _ _ _).bind fun bottom => ?_
  split
  · simp only [pure_bind]
    generalize LAYER_HEIGHT = height
    refine (atMost_node pp s .bottom height (bottomTree idx)).bind fun root => ?_
    refine (atMost_signLayer _ _ _ _ _).bind fun top => ?_
    split <;> exact atMost_pure _ _
  · exact atMost_pure _ _

/-- A signing request makes at most the calls charged to it. -/
theorem atMost_signWith (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    AtMost (signWith (queryH (m := OracleComp HashSpec)) sk idx msg) signQueries := by
  unfold signWith schemeSeed publicParamOf
  rw [signQueries, show 2 + 2 * layerSignQueries + nodeQueries LAYER_HEIGHT
    = 1 + (1 + (2 * layerSignQueries + nodeQueries LAYER_HEIGHT)) by
      generalize layerSignQueries = a; generalize nodeQueries LAYER_HEIGHT = b; omega]
  exact (atMost_of_queryCount (queryCount_queryH _)).bind fun _ =>
    (atMost_of_queryCount (queryCount_th _ _ _)).bind fun _ => atMost_signDerived _ _ _ _

/-! ## Verification -/

/-- The most hash calls of one layer's check: the digest, every chain, the leaf and the path. -/
def layerVerifyQueries : Nat := 1 + V * 3 + 1 + LAYER_HEIGHT

/-- The most hash calls of a verification: both layers' checks. -/
def verifyQueries : Nat := 2 * layerVerifyQueries

theorem queryCount_climb (pp : PublicParam) (layer : Layer) :
    ∀ (level j : Nat) (current : Digest) (siblings : List Digest),
      QueryCount (Merkle.climb (nodeHash (queryH (m := OracleComp HashSpec)) pp layer) level j
        current siblings) siblings.length
  | _, _, _, [] => by
    rw [Merkle.climb]
    exact .pure _
  | level, j, current, sibling :: rest => by
    rw [Merkle.climb, List.length_cons,
      show rest.length + 1 = 1 + rest.length from Nat.add_comm _ _]
    unfold nodeHash
    exact (queryCount_th _ _ _).bind fun _ => queryCount_climb pp layer _ _ _ rest

theorem atMost_layerRoot (pp : PublicParam) (layer : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature) :
    AtMost (layerRoot (queryH (m := OracleComp HashSpec)) pp layer e msg sig)
      layerVerifyQueries := by
  unfold layerRoot otsLeaf messageDigest fold
  rw [layerVerifyQueries, show 1 + V * 3 + 1 + LAYER_HEIGHT
    = 1 + (V * 3 + (1 + (LAYER_HEIGHT + 0))) by omega]
  simp only [bind_assoc]
  refine (atMost_of_queryCount (queryCount_th _ _ _)).bind fun digest => ?_
  split
  · simp only [bind_assoc, pure_bind]
    refine (AtMost.ofFnInOrder fun i => ?_).bind fun ends => ?_
    · exact (atMost_of_queryCount (queryCount_chain _ _ _ _ _ _ _ _)).mono
        (by have := (‹Vector (Fin CHAIN_LENGTH) V›[i]).isLt; simp only [CHAIN_LENGTH] at *; omega)
    refine (atMost_of_queryCount (queryCount_th _ _ _)).bind fun leaf => ?_
    refine ((atMost_of_queryCount (queryCount_climb _ _ _ _ _ sig.path.toList)).mono ?_).bind
      fun _ => atMost_pure _ 0
    simp
  · simp only [pure_bind]
    exact atMost_pure _ _

/-- A verification makes at most `384` calls, whatever the signature. -/
theorem atMost_verifyWith (pk : PublicKey) (msg : Message) (sig : Signature) :
    AtMost (verifyWith (queryH (m := OracleComp HashSpec)) pk msg sig) verifyQueries := by
  unfold verifyWith
  rw [verifyQueries, show 2 * layerVerifyQueries = layerVerifyQueries + (layerVerifyQueries + 0)
    by generalize layerVerifyQueries = a; omega]
  refine (atMost_layerRoot _ _ _ _ _).bind fun root => ?_
  split
  · refine (atMost_layerRoot _ _ _ _ _).bind fun top => ?_
    split <;> exact atMost_pure _ _
  · exact atMost_pure _ _

/-! ## The game -/

/-- A call of `H` in the game, not a coin. -/
abbrev IsHashCall (t : OracleWorld.Domain) : Prop := (t matches .inr _) = true

theorem isQueryBoundP_liftM_hash {α : Type} (c : OracleComp HashSpec α) (n : Nat)
    (h : AtMost c n) : (liftM c : OracleComp OracleWorld α).IsQueryBoundP IsHashCall n := by
  induction c using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind x next ih =>
    rw [AtMost, isQueryBoundP_query_bind_iff] at h
    rw [liftM_bind]
    change IsQueryBoundP ((liftM (OracleWorld.query (.inr x)) : OracleComp OracleWorld _) >>=
      fun u => (liftM (next u) : OracleComp OracleWorld α)) _ n
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr (h.1.resolve_left (by simp)), fun u => ih u _ ?_⟩
    simpa using h.2 u

theorem isQueryBoundP_liftM_prob {α : Type} (c : ProbComp α) :
    (liftM c : OracleComp OracleWorld α).IsQueryBoundP IsHashCall 0 := by
  induction c using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind x next ih =>
    rw [liftM_bind]
    change IsQueryBoundP ((liftM (OracleWorld.query (.inl x)) : OracleComp OracleWorld _) >>=
      fun u => (liftM (next u) : OracleComp OracleWorld α)) _ 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp), fun u => by simpa using ih u⟩

section Simulation

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {ω : Type}
  [EmptyCollection ω] [Append ω] [LawfulAppend ω]

/-- A simulation in which a `p`-query costs at most one `r`-query and a `s`-query at most `c`.

A computation with at most `n` `p`-queries and `m` `s`-queries then makes `n + c * m`. -/
theorem isQueryBoundP_simulateQ_run_writerT_cost {α : Type}
    {p s : ι → Prop} [DecidablePred p] [DecidablePred s] {r : ι' → Prop} [DecidablePred r]
    {impl : QueryImpl spec (WriterT ω (OracleComp spec'))} (c : Nat)
    (hstep : ∀ t, IsQueryBoundP (impl t).run r ((if p t then 1 else 0) + if s t then c else 0))
    {oa : OracleComp spec α} {n m : Nat}
    (hp : IsQueryBoundP oa p n) (hs : IsQueryBoundP oa s m) :
    IsQueryBoundP (simulateQ impl oa).run r (n + c * m) := by
  induction oa using OracleComp.inductionOn generalizing n m with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hp hs
    simp only [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query]
    have hbound : (if p t then 1 else 0) + (if s t then c else 0) +
        ((if p t then n - 1 else n) + c * (if s t then m - 1 else m)) = n + c * m := by
      rcases hp.1 with hpt | hpt <;> rcases hs.1 with hst | hst <;>
        by_cases hp' : p t <;> by_cases hs' : s t <;> simp_all <;>
        first
        | omega
        | (obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hst.ne'
           simp [Nat.mul_add]
           omega)
    rw [← hbound]
    exact isQueryBoundP_bind (hstep t) fun u _ =>
      (isQueryBoundP_map_iff _ _ _).2 (ih u.1 (hp.2 u.1) (hs.2 u.1))

end Simulation

/-- Key generation makes at most its `13,434,881` calls. -/
theorem atMost_keyGenWith (seed : Seed) :
    AtMost (keyGenWith (queryH (m := OracleComp HashSpec)) seed)
      XmssSecurity.Bridge.keygenQueries := by
  unfold keyGenWith publicKeyOf publicParamOf
  rw [show XmssSecurity.Bridge.keygenQueries = 1 + (1 + (nodeQueries LAYER_HEIGHT + 0) + 0) by
    rfl]
  refine (atMost_of_queryCount (queryCount_queryH _)).bind fun s => ?_
  refine AtMost.bind ?_ fun _ => atMost_pure _ 0
  refine (atMost_of_queryCount (queryCount_th _ _ _)).bind fun pp => ?_
  generalize LAYER_HEIGHT = height
  exact (atMost_node _ _ _ height 0).bind fun _ => atMost_pure _ 0

theorem isQueryBoundP_oracles (sk : SecretKey) (t : (OracleWorld + SigningSpec).Domain) :
    IsQueryBoundP ((QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk) t).run
      IsHashCall
      ((if IsHashQuery t then 1 else 0) + if IsSignRequest t then signQueries else 0) := by
  rcases t with t | request
  · simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
    change IsQueryBoundP ((·, ∅) <$> (liftM (OracleWorld.query t) : OracleComp OracleWorld _)) _ _
    rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    rcases t with t | x <;> simp
  · simp only [QueryImpl.add_apply_inr, signingOracle, QueryImpl.run_withLogging_apply]
    simp only [IsHashQuery, ite_true, Bool.false_eq_true, ite_false, Nat.zero_add]
    rw [← Nat.add_zero signQueries]
    exact isQueryBoundP_bind (isQueryBoundP_liftM_hash _ _ ((atMost_signWith _ _ _).map _))
      fun _ _ => isQueryBoundP_pure _ _ _

/-- The game's calls: key generation, the adversary's queries, its requests and verification. -/
theorem isQueryBoundP_gameCore (adversary : Adversary) (qH qS : Nat)
    (h : MakesAtMost adversary qH qS) :
    (gameCore adversary).IsQueryBoundP IsHashCall
      (XmssSecurity.Bridge.keygenQueries + qH + signQueries * qS + verifyQueries) := by
  unfold gameCore
  rw [show XmssSecurity.Bridge.keygenQueries + qH + signQueries * qS + verifyQueries
    = 0 + (XmssSecurity.Bridge.keygenQueries + ((qH + signQueries * qS) + (verifyQueries + 0)))
    by omega]
  refine isQueryBoundP_bind (isQueryBoundP_liftM_prob _) fun seed _ => ?_
  refine isQueryBoundP_bind (isQueryBoundP_liftM_hash _ _ (atMost_keyGenWith _)) fun keys _ => ?_
  refine isQueryBoundP_bind (isQueryBoundP_simulateQ_run_writerT_cost signQueries
    (isQueryBoundP_oracles keys.1) (h keys.2).1 (h keys.2).2) fun result _ => ?_
  exact isQueryBoundP_bind (isQueryBoundP_liftM_hash _ _ (atMost_verifyWith _ _ _))
    fun _ _ => isQueryBoundP_pure _ _ _

theorem hashQueryBound_of_isQueryBoundP {α : Type} (oa : OracleComp OracleWorld α) (n : Nat)
    (h : oa.IsQueryBoundP IsHashCall n) (cache : QueryCache HashSpec) :
    XmssSecurity.HashQueryBound oa cache n := by
  induction oa using OracleComp.inductionOn generalizing n cache with
  | pure a =>
    intro result hresult
    simp [XmssSecurity.countHashQueries_pure] at hresult
    simp [hresult]
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with u | x
    · refine XmssSecurity.Seeded.hashQueryBound_query_bind_of _ next cache n (by simp)
        fun r _ => ?_
      simpa using ih r.1 _ (h.2 r.1) r.2
    · have hn : 0 < n := h.1.resolve_left (by simp)
      refine XmssSecurity.Seeded.hashQueryBound_query_bind_of _ next cache n
        (by simpa using Nat.one_le_iff_ne_zero.2 hn.ne')
        fun r _ => ?_
      simpa using ih r.1 _ (h.2 r.1) r.2

/-- The same budget, counted as the game's bound counts it. -/
theorem hasHashQueryBound_of_makesAtMost (adversary : Adversary) (qH qS : Nat)
    (h : MakesAtMost adversary qH qS) :
    HasHashQueryBound adversary
      (XmssSecurity.Bridge.keygenQueries + qH + signQueries * qS + verifyQueries) := by
  have hbound := hashQueryBound_of_isQueryBoundP _ _ (isQueryBoundP_gameCore adversary qH qS h) ∅
  simp only [XmssSecurity.HashQueryBound, XmssSecurity.simulateQ_countHashQueries] at hbound
  exact hbound

/-! ## The theorem -/

theorem signQueries_eq : signQueries = 8630239199 := by
  decide

theorem verifyQueries_eq : verifyQueries = 384 := by
  decide

/-- leanXMSS as EthLib computes it is strongly unforgeable in the random oracle model.

Take an adversary with at most `qH` hash queries and `qS` signing requests.

It forges with probability at most `(qH + 8,630,239,199 * qS + 13,435,265) / 2^127`.

A signing request is charged the most hash calls the signer can make.

That is `2^32` randomizer trials on each layer, about `2^33.007` calls in all.

The constant is key generation's `13,434,881` calls and verification's `384`. -/
theorem unforgeable_queries : HasQuerySecurityBits 127 8630239199 13435265 := by
  intro qH qS adversary h
  have hK := XmssSecurity.Bridge.keygenQueries_eq
  refine (unforgeable _ ?_ adversary (hasHashQueryBound_of_makesAtMost adversary qH qS h)).trans_eq
    ?_
  · omega
  · rw [hK, signQueries_eq, verifyQueries_eq]
    congr 2
    omega

end EthLib.Cryptography.Xmss.Unforgeability

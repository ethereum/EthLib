module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Graph
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Ghost

/-!
# Proofs: the game where the scheme skips the halves it throws away

A tweakable hash keeps half 0 of its answer and throws half 1 away.

In the game of halves, the scheme still asks half 1, at a point made of the hashed values.

Some of these values stay hidden from the adversary, such as the inner values of a chain.

So no later game could make that query without reading the hidden value.

This file drops those queries, with the generic fact on thrown-away queries.

The scheme computes the same values, because a tweakable hash reads only half 0.

The adversary still asks both halves of each of its queries.

The game where the scheme skips half 1 of each tweakable hash has the same chance of a forgery.

The scheme here means key generation, signing and the final verification.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open EthLib.Cryptography.Xmss.Unforgeability (ofOutput)
open OracleSpec OracleComp

/-! ## The scheme reads a tweakable hash only through half 0

Two hashes that agree on every tweakable hash, and on the message digest, give the same scheme.

The tweakable hashes are those at every address other than the message digest's. -/

/-- An address other than those of the message digest. -/
def NotDigestAddress (A : Address) : Prop :=
  ∀ c, A ≠ addrMsg c

/-- An address of another type than the message digest's is not one of its addresses. -/
theorem notDigestAddress {type : AddressType} (htype : type ≠ .msg) (step : Fin 8)
    (layer : Fin 256) (tree : UInt32) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    NotDigestAddress (encodeAddress type.code step layer tree hi lo) := fun _ =>
  encodeAddress_ne_of_type_ne _ _ _ _ _ _ _ _ _ _ fun h => htype (AddressType.code_injective h)

section CongrH

variable {m : Type → Type} [Monad m] {H H' : ByteArray → m (Vector UInt8 32)}
  (hth : ∀ pp A payload, NotDigestAddress A → th H pp A payload = th H' pp A payload)

include hth

/-- A chain step reads the hash only through a tweakable hash. -/
theorem chainStep_congrH (pp : PublicParam) (key : OtsKey) (i : Fin V) :
    chainStep H pp key i = chainStep H' pp key i :=
  funext fun _ => funext fun _ =>
    hth _ _ _ (notDigestAddress (type := .chain) (by decide) _ _ _ _ _)

/-- A chain reads the hash only through tweakable hashes. -/
theorem chain_congrH (pp : PublicParam) (key : OtsKey) (i : Fin V) :
    chain H pp key i = chain H' pp key i := by
  funext start steps h v
  simp only [chain, chainStep_congrH hth]

/-- A key's leaf from its chain ends reads the hash only through a tweakable hash. -/
theorem otsLeafHash_congrH (pp : PublicParam) (key : OtsKey) :
    otsLeafHash H pp key = otsLeafHash H' pp key :=
  funext fun _ => hth _ _ _ (notDigestAddress (type := .leaf) (by decide) _ _ _ _ _)

/-- A key's leaf reads the hash only through tweakable hashes. -/
theorem otsPublicLeaf_congrH (pp : PublicParam) (prf : SeedPrf m) (key : OtsKey) :
    otsPublicLeaf H pp prf key = otsPublicLeaf H' pp prf key := by
  simp only [otsPublicLeaf, chain_congrH hth, otsLeafHash_congrH hth]

/-- An encoding reads the hash only through a tweakable hash. -/
theorem encode_congrH (pp : PublicParam) (key : OtsKey) :
    encode H pp key = encode H' pp key := by
  funext msg counter
  rw [encode, encode,
    hth pp (addrEncoding key) _ (notDigestAddress (type := .encoding) (by decide) _ _ _ _ _)]

/-- A one-time signature reads the hash only through tweakable hashes. -/
theorem otsSign_congrH (pp : PublicParam) (prf : SeedPrf m) (key : OtsKey) (msg : ByteArray) :
    otsSign H pp prf key msg = otsSign H' pp prf key msg := by
  simp only [otsSign, Internal.findCounter, encode_congrH hth, chain_congrH hth]

/-- The leaf a one-time signature leads to reads the hash only through tweakable hashes. -/
theorem otsLeaf_congrH (pp : PublicParam) (key : OtsKey) :
    otsLeaf H pp key = otsLeaf H' pp key := by
  funext msg counter y
  simp only [otsLeaf, encode_congrH hth, chain_congrH hth, otsLeafHash_congrH hth]

/-- A tree node reads the hash only through a tweakable hash. -/
theorem nodeHash_congrH (pp : PublicParam) (layer : Layer) (tree : Nat) :
    nodeHash H pp layer tree = nodeHash H' pp layer tree :=
  funext fun _ => funext fun _ => funext fun _ => funext fun _ =>
    hth _ _ _ (notDigestAddress (type := .node) (by decide) _ _ _ _ _)

/-- The leaves of a tree read the hash only through tweakable hashes. -/
theorem leaves_congrH (pp : PublicParam) (prf : SeedPrf m) (layer : Layer) (tree : Nat) :
    leaves H pp prf layer tree = leaves H' pp prf layer tree :=
  funext fun _ => otsPublicLeaf_congrH hth _ _ _

/-- A tree's root reads the hash only through tweakable hashes. -/
theorem treeRoot_congrH (pp : PublicParam) (prf : SeedPrf m) (layer : Layer) (tree : Nat) :
    treeRoot H pp prf layer tree = treeRoot H' pp prf layer tree := by
  rw [treeRoot, treeRoot, nodeHash_congrH hth, leaves_congrH hth]

/-- A key's path reads the hash only through tweakable hashes. -/
theorem path_congrH (pp : PublicParam) (prf : SeedPrf m) (layer : Layer) (tree e : Nat) :
    path H pp prf layer tree e = path H' pp prf layer tree e := by
  rw [path, path, nodeHash_congrH hth, leaves_congrH hth]

/-- Climbing a path reads the hash only through tweakable hashes. -/
theorem fold_congrH (pp : PublicParam) (layer : Layer) (tree : Nat) :
    fold H pp layer tree = fold H' pp layer tree := by
  funext e leaf pi
  rw [fold, fold, nodeHash_congrH hth]

/-- A FORS leaf reads the hash only through a tweakable hash. -/
theorem forsLeafHash_congrH (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) :
    forsLeafHash H pp idx kappa = forsLeafHash H' pp idx kappa :=
  funext fun _ => funext fun _ =>
    hth _ _ _ (notDigestAddress (type := .forsLeaf) (by decide) _ _ _ _ _)

/-- A FORS node reads the hash only through a tweakable hash. -/
theorem forsNodeHash_congrH (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) :
    forsNodeHash H pp idx kappa = forsNodeHash H' pp idx kappa :=
  funext fun _ => funext fun _ => funext fun _ => funext fun _ =>
    hth _ _ _ (notDigestAddress (type := .forsNode) (by decide) _ _ _ _ _)

/-- The FORS leaves read the hash only through tweakable hashes. -/
theorem forsLeaves_congrH (pp : PublicParam) (prf : SeedPrf m) (idx : Nat)
    (kappa : Fin FORS_TREES) : forsLeaves H pp prf idx kappa = forsLeaves H' pp prf idx kappa :=
  funext fun _ => by simp only [forsLeaves, forsLeafHash_congrH hth]

/-- A FORS key reads the hash only through tweakable hashes. -/
theorem forsKey_congrH (pp : PublicParam) (prf : SeedPrf m) (idx : Nat) :
    forsKey H pp prf idx = forsKey H' pp prf idx := by
  simp only [forsKey, forsNode, forsNodeHash_congrH hth, forsLeaves_congrH hth]

/-- The FORS openings read the hash only through tweakable hashes. -/
theorem forsSign_congrH (pp : PublicParam) (prf : SeedPrf m) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    forsSign H pp prf idx leaves = forsSign H' pp prf idx leaves := by
  simp only [forsSign, treeOpen, forsNodeHash_congrH hth, forsLeaves_congrH hth]

/-- The FORS key the openings lead to reads the hash only through tweakable hashes. -/
theorem forsRecover_congrH (pp : PublicParam) (idx : Nat) :
    forsRecover H pp idx = forsRecover H' pp idx := by
  funext leaves openings
  simp only [forsRecover, treeRecover, forsLeafHash_congrH hth, forsNodeHash_congrH hth]

/-- What a layer's key signs reads the hash only through tweakable hashes. -/
theorem layerMessage_congrH (pp : PublicParam) (prf : SeedPrf m) (layer : Layer) (idx : Nat) :
    layerMessage H pp prf layer idx = layerMessage H' pp prf layer idx := by
  cases layer <;> simp only [layerMessage, forsKey_congrH hth, treeRoot_congrH hth]

/-- A layer's signature reads the hash only through tweakable hashes. -/
theorem signLayer_congrH (pp : PublicParam) (prf : SeedPrf m) (layer : Layer) (idx : Nat)
    (msg : ByteArray) : signLayer H pp prf layer idx msg = signLayer H' pp prf layer idx msg := by
  simp only [signLayer, otsSign_congrH hth, path_congrH hth]

/-- The root a layer's signature leads to reads the hash only through tweakable hashes. -/
theorem layerRoot_congrH (pp : PublicParam) (layer : Layer) (idx : Nat) :
    layerRoot H pp layer idx = layerRoot H' pp layer idx := by
  funext msg sig
  simp only [layerRoot, otsLeaf_congrH hth, fold_congrH hth]

/-- The public key reads the hash only through tweakable hashes. -/
theorem publicKeyOf_congrH (prf : SeedPrf m) : publicKeyOf H prf = publicKeyOf H' prf := by
  simp only [publicKeyOf, treeRoot_congrH hth]

variable (hmsg : ∀ pp c payload, thFull H pp (addrMsg c) payload = thFull H' pp (addrMsg c) payload)

include hmsg

omit hth in
/-- The message digest reads the hash only at its own addresses. -/
theorem messageDigest_congrH (pp : PublicParam) :
    messageDigest H pp = messageDigest H' pp := by
  funext msg rho
  simp only [messageDigest, hmsg]

/-- Signing reads the hash only through tweakable hashes and the message digest. -/
theorem signDerived_congrH (prf : SeedPrf m) (pp : PublicParam) (msg : Message) :
    signDerived H prf pp msg = signDerived H' prf pp msg := by
  simp only [signDerived, messageDigest_congrH hmsg, forsSign_congrH hth,
    layerMessage_congrH hth, signLayer_congrH hth]

/-- Verification reads the hash only through tweakable hashes and the message digest. -/
theorem verifyWith_congrH (pk : PublicKey) (msg : Message) (sig : Signature) :
    verifyWith H pk msg sig = verifyWith H' pk msg sig := by
  simp only [verifyWith, messageDigest_congrH hmsg, forsRecover_congrH hth, layerRoot_congrH hth]

end CongrH

/-! ## Ghost queries at the halves a tweakable hash throws away -/

/-- The bytes of a tweakable hash's input: at an address other than the message digest's. -/
def IsThBytes (b : List UInt8) : Prop :=
  ∃ pp A payload, NotDigestAddress A ∧ b = (thInput pp A payload).data.toList

/-- Half 1 of a tweakable hash's input: the half the hash throws away. -/
def IsThHalf (t : List UInt8 × Fin 2) : Prop :=
  t.2 = 1 ∧ IsThBytes t.1

/-- A tweakable hash's input is one. -/
theorem isThBytes_thInput (pp : PublicParam) {A : Address} (hA : NotDigestAddress A)
    (payload : ByteArray) : IsThBytes (thInput pp A payload).data.toList :=
  ⟨pp, A, payload, hA, rfl⟩

/-- An input of the message digest is not a tweakable hash's input. -/
theorem not_isThBytes_addrMsg (pp : PublicParam) (c : Fin DIGEST_CALLS) (payload : ByteArray) :
    ¬IsThBytes (thInput pp (addrMsg c) payload).data.toList := by
  rintro ⟨pp', A, payload', hA, h⟩
  exact hA c (thInput_inj (byteArray_eq_of_toList_eq h)).2.1.symm

/-- The world of halves with ghost queries at the halves a tweakable hash throws away. -/
abbrev SkipWorld :=
  GhostWorld (List UInt8 × Fin 2 →ₒ Digest) (DerivationInput × Fin 2) Digest IsThHalf

open Classical in
/-- Ask every query half by half, but a tweakable hash's half 1 as a ghost query.

The answer then has half 1 zero, which a tweakable hash throws away. -/
noncomputable def ghostHalves : QueryImpl (World DerivationInput) (OracleComp SkipWorld)
  | .inl (.inl n) => SkipWorld.query (.inl (.inl (.inl n)))
  | .inl (.inr a) =>
      if h : IsThBytes a then do
        let u ← SkipWorld.query (.inl (.inl (.inr (a, 0))))
        SkipWorld.query (.inr ⟨(a, 1), rfl, h⟩)
        return hashHalves.symm (u, default)
      else do
        let u ← SkipWorld.query (.inl (.inl (.inr (a, 0))))
        let v ← SkipWorld.query (.inl (.inl (.inr (a, 1))))
        return hashHalves.symm (u, v)
  | .inr x => do
      let u ← SkipWorld.query (.inl (.inr (x, 0)))
      let v ← SkipWorld.query (.inl (.inr (x, 1)))
      return hashHalves.symm (u, v)

/-- Ask every query half by half, but skip a tweakable hash's half 1. -/
noncomputable abbrev skipHalves : QueryImpl (World DerivationInput) (OracleComp HalvedWorld) :=
  skipGhost IsThHalf ∘ₛ ghostHalves

/-- leanSPHINCS with every derivation a derivation query, asked half by half.

Each tweakable hash asks half 0 only. -/
noncomputable def skipScheme :
    SignatureAlg (OracleComp HalvedWorld) Message PublicKey Unit (Option Signature) :=
  hiddenSeedScheme.map (simulateQ' skipHalves)

/-! ## Asking the ghost queries gives the game of halves -/

/-- The game of halves seen in the world with ghost queries. -/
def liftGhost : QueryImpl HalvedWorld (OracleComp SkipWorld) :=
  fun t => SkipWorld.query (.inl t)

/-- Asking the ghost queries undoes the lift. -/
theorem askGhost_comp_liftGhost : askGhost IsThHalf ∘ₛ liftGhost = QueryImpl.id' HalvedWorld := by
  funext t
  simp [liftGhost, askGhost]

/-- Skipping the ghost queries undoes the lift. -/
theorem skipGhost_comp_liftGhost : skipGhost IsThHalf ∘ₛ liftGhost = QueryImpl.id' HalvedWorld := by
  funext t
  simp [liftGhost, skipGhost]

/-- With the ghost queries asked, a derivation is asked half by half. -/
theorem askGhost_ghostHalves_inr (x : DerivationInput) :
    simulateQ (askGhost IsThHalf) (ghostHalves (.inr x)) = halves (.inr x) := by
  simp [ghostHalves, askGhost, halvesImpl]

/-- With the ghost queries asked, a tweakable hash's input is asked half by half.

Its half 1 is thrown away, and the answer has half 1 zero. -/
theorem askGhost_ghostHalves_of_isThBytes {a : List UInt8} (h : IsThBytes a) :
    simulateQ (askGhost IsThHalf) (ghostHalves (.inl (.inr a))) = (do
      let u ← HalvedWorld.query (.inl (.inr (a, 0)))
      let _ ← HalvedWorld.query (.inl (.inr (a, 1)))
      return hashHalves.symm (u, default)) := by
  simp [ghostHalves, askGhost, h]

/-- With the ghost queries asked, any other public input is asked half by half. -/
theorem askGhost_ghostHalves_of_not_isThBytes {a : List UInt8} (h : ¬IsThBytes a) :
    simulateQ (askGhost IsThHalf) (ghostHalves (.inl (.inr a))) = halves (.inl (.inr a)) := by
  simp [ghostHalves, askGhost, halvesImpl, h]

/-- The derivations, with the ghost queries asked, are the derivations asked half by half. -/
theorem mapPrf_askGhost_ghostHalves :
    mapPrf (simulateQ (askGhost IsThHalf ∘ₛ ghostHalves)) derivationPrf =
      mapPrf (simulateQ halves) derivationPrf := by
  funext pp A suffix
  simp only [mapPrf, derivationPrf]
  split
  · simp only [simulateQ_map, simulateQ_spec_query, QueryImpl.apply_compose,
      askGhost_ghostHalves_inr]
  · simp only [simulateQ_pure]

/-- With the ghost queries asked, a tweakable hash asks both halves and keeps half 0. -/
theorem simulateQ_askGhost_ghostHalves_th (pp : PublicParam) {A : Address}
    (hA : NotDigestAddress A) (payload : ByteArray) :
    simulateQ (askGhost IsThHalf ∘ₛ ghostHalves) (th (liftH DerivationInput) pp A payload) = (do
      let u ← HalvedWorld.query (.inl (.inr ((thInput pp A payload).data.toList, 0)))
      let _ ← HalvedWorld.query (.inl (.inr ((thInput pp A payload).data.toList, 1)))
      return u) := by
  change simulateQ _ (liftH DerivationInput (thInput pp A payload) >>= fun x =>
    pure (halfOf 0 x)) = _
  rw [simulateQ_bind, liftH_eq, simulateQ_map, simulateQ_spec_query, QueryImpl.apply_compose,
    askGhost_ghostHalves_of_isThBytes (isThBytes_thInput pp hA payload)]
  simp only [map_bind, map_pure, bind_assoc, pure_bind, simulateQ_pure,
    halfOf_zero_hashHalves_symm]

/-- With the ghost queries asked, a tweakable hash reads what it reads in the game of halves. -/
theorem th_askGhost_ghostHalves (pp : PublicParam) {A : Address} (hA : NotDigestAddress A)
    (payload : ByteArray) :
    th (fun x => simulateQ (askGhost IsThHalf ∘ₛ ghostHalves) (liftH DerivationInput x)) pp A
        payload =
      th (fun x => simulateQ halves (liftH DerivationInput x)) pp A payload := by
  rw [← th_map_monad (simulateQ (askGhost IsThHalf ∘ₛ ghostHalves)) (fun b => simulateQ_pure _ b)
      (fun x f => simulateQ_bind _ x f),
    ← th_map_monad (simulateQ halves) (fun b => simulateQ_pure _ b)
      (fun x f => simulateQ_bind _ x f),
    simulateQ_askGhost_ghostHalves_th pp hA payload, simulateQ_halves_th]

/-- With the ghost queries asked, the message digest reads what it reads in the game of halves. -/
theorem thFull_askGhost_ghostHalves_addrMsg (pp : PublicParam) (c : Fin DIGEST_CALLS)
    (payload : ByteArray) :
    thFull (fun x => simulateQ (askGhost IsThHalf ∘ₛ ghostHalves) (liftH DerivationInput x)) pp
        (addrMsg c) payload =
      thFull (fun x => simulateQ halves (liftH DerivationInput x)) pp (addrMsg c) payload := by
  simp only [thFull, liftH_eq, simulateQ_map, simulateQ_spec_query, QueryImpl.apply_compose,
    askGhost_ghostHalves_of_not_isThBytes (not_isThBytes_addrMsg pp c payload)]
  rfl

/-- With the ghost queries asked, the scheme is the scheme of the game of halves. -/
theorem hiddenSeedScheme_map_askGhost_ghostHalves :
    hiddenSeedScheme.map (simulateQ' (askGhost IsThHalf ∘ₛ ghostHalves)) = halvedScheme := by
  have hth := fun pp A payload (hA : NotDigestAddress A) => th_askGhost_ghostHalves pp hA payload
  have hmsg := thFull_askGhost_ghostHalves_addrMsg
  refine SignatureAlg.ext ?_ (funext fun pk => funext fun _ => funext fun msg => ?_)
    (funext fun pk => funext fun msg => funext fun sig => ?_)
  · rw [halvedScheme, SignatureAlg.map_keygen, SignatureAlg.map_keygen]
    dsimp only [hiddenSeedScheme]
    rw [simulateQ_bind, simulateQ_bind,
      publicKeyOf_map_monad (simulateQ (askGhost IsThHalf ∘ₛ ghostHalves))
        (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
      publicKeyOf_map_monad (simulateQ halves)
        (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
      mapPrf_askGhost_ghostHalves, publicKeyOf_congrH hth]
    simp only [simulateQ_pure]
  · rw [halvedScheme, SignatureAlg.map_sign, SignatureAlg.map_sign]
    dsimp only [hiddenSeedScheme]
    rw [simulateQ_bind, simulateQ_bind,
      publicParamOf_map_monad (simulateQ (askGhost IsThHalf ∘ₛ ghostHalves))
        (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
      publicParamOf_map_monad (simulateQ halves)
        (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
      mapPrf_askGhost_ghostHalves]
    refine bind_congr fun pp => ?_
    rw [simulateQ_map, simulateQ_map,
      signDerived_map_monad (simulateQ (askGhost IsThHalf ∘ₛ ghostHalves))
        (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
      signDerived_map_monad (simulateQ halves)
        (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
      mapPrf_askGhost_ghostHalves, signDerived_congrH hth hmsg]
  · rw [halvedScheme, SignatureAlg.map_verify, SignatureAlg.map_verify]
    cases sig with
    | none => rfl
    | some sig =>
      refine (verifyWith_map_monad (simulateQ (askGhost IsThHalf ∘ₛ ghostHalves))
        (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f) _ pk msg sig).trans ?_
      refine Eq.trans ?_ (verifyWith_map_monad (simulateQ halves)
        (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f) _ pk msg sig).symm
      exact verifyWith_congrH hth hmsg pk msg sig

/-! ## The hop -/

/-- The experiment in the world with ghost queries. -/
noncomputable def ghostExperiment (adversary : Adversary) :
    OracleComp SkipWorld (SignatureAlg.UnforgeableTranscript Message PublicKey Unit
      (Option Signature)) :=
  SignatureAlg.unforgeableTranscriptExperiment (sigAlg := hiddenSeedScheme.map
    (simulateQ' ghostHalves)) ((halvedAdversary adversary).mapOracles liftGhost)

/-- Asking the ghost queries gives the experiment of the game of halves. -/
theorem simulateQ_askGhost_ghostExperiment (adversary : Adversary) :
    simulateQ (askGhost IsThHalf) (ghostExperiment adversary) =
      SignatureAlg.unforgeableTranscriptExperiment (halvedAdversary adversary) := by
  rw [ghostExperiment, SignatureAlg.simulateQ_unforgeableTranscriptExperiment,
    SignatureAlg.map_simulateQ'_map_simulateQ', hiddenSeedScheme_map_askGhost_ghostHalves,
    SignatureAlg.UnforgeableAdversary.mapOracles_mapOracles, askGhost_comp_liftGhost]
  exact congrArg _ (congrArg SignatureAlg.UnforgeableAdversary.mk
    (SignatureAlg.UnforgeableAdversary.mapOracles_id'_main _))

/-- Skipping the ghost queries gives the experiment of the scheme that skips them. -/
theorem simulateQ_skipGhost_ghostExperiment (adversary : Adversary) :
    simulateQ (skipGhost IsThHalf) (ghostExperiment adversary) =
      SignatureAlg.unforgeableTranscriptExperiment
        (⟨(halvedAdversary adversary).main⟩ : SignatureAlg.UnforgeableAdversary skipScheme) := by
  rw [ghostExperiment, SignatureAlg.simulateQ_unforgeableTranscriptExperiment,
    SignatureAlg.map_simulateQ'_map_simulateQ',
    SignatureAlg.UnforgeableAdversary.mapOracles_mapOracles, skipGhost_comp_liftGhost]
  exact congrArg _ (congrArg SignatureAlg.UnforgeableAdversary.mk
    (SignatureAlg.UnforgeableAdversary.mapOracles_id'_main _))

/-- **The game where the scheme skips half 1 of each tweakable hash.**

In the ideal game, the scheme asking or skipping those halves gives a forgery the same chance. -/
theorem prEvent_halved_eq_skip (adversary : Adversary) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (List UInt8 × Fin 2 →ₒ Digest)
        (DerivationInput × Fin 2) Digest) (SignatureAlg.unforgeableTranscriptExperiment
          (halvedAdversary adversary))).run (∅, ∅)}[z.1.strongWins = true] =
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl (List UInt8 × Fin 2 →ₒ Digest)
        (DerivationInput × Fin 2) Digest) (SignatureAlg.unforgeableTranscriptExperiment
          (⟨(halvedAdversary adversary).main⟩ : SignatureAlg.UnforgeableAdversary skipScheme))).run
          (∅, ∅)}[z.1.strongWins = true] := by
  rw [← simulateQ_askGhost_ghostExperiment, ← simulateQ_skipGhost_ghostExperiment]
  exact prEvent_askGhost_eq_skipGhost (pub := List UInt8 × Fin 2 →ₒ Digest)
    (X := DerivationInput × Fin 2) (R := Digest) IsThHalf (ghostExperiment adversary)
    fun z => z.strongWins = true

end EthLib.Cryptography.Sphincs.Unforgeability

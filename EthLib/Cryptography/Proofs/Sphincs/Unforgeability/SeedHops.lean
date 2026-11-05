module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Game
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.HonestQueries
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.HiddenSeed
public import EthLib.Cryptography.Proofs.Sphincs.TweakableHash

/-!
# Proofs: the seeds of leanSPHINCS are hidden

Every secret of leanSPHINCS comes from the key's seed `S_0` in two steps.

1. The scheme seed is `S = H("leanSPHINCS" | S_0)`.
2. Every secret is a derivation `H(P' | A | S | suffix)` at a derivation address `A`: the public
   parameter, the chain starts, the FORS secrets and the randomizer.

Two hops replace both seeds by independent uniform answers.

- The first hop makes the scheme seed the one derivation from `S_0`.
  An input of 43 bytes fixes `S_0`, so a query hits it with probability `2^-256`.
- The second hop makes every derivation from `S` a derivation of its own.
  Bytes 32 to 63 of a derivation input fix `S`, so a query hits one with probability `2^-256`.
- Between the hops, the scheme seed is drawn first instead of on its first query.

Only the adversary's own hash queries are charged.

Key generation, signing and verification never query an input of 43 bytes, nor an input at a
derivation address with a 32-byte seed after it.

So each hop costs `qH / 2^256`.

At the end, the derivations are answered by an independent table, and no seed is left.

The honest algorithms call the derivations only at derivation addresses.

So the derivations may be anything at other addresses, and the algorithms do not change.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open EthLib.Cryptography.Xmss.Unforgeability (ofOutput queryH)
open OracleSpec OracleComp

/-! ## Only the derivation addresses matter

Two families of derivations that agree at every derivation address give the same algorithms. -/

section Congr

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32)) {prf prf' : SeedPrf m}
  (hprf : ∀ pp A suffix, IsDerivationAddress A → prf pp A suffix = prf' pp A suffix)

include hprf

/-- The chain starts read the derivations only at derivation addresses. -/
theorem chainStarts_congr (pp : PublicParam) (key : OtsKey) :
    chainStarts pp prf key = chainStarts pp prf' key := by
  simp only [chainStarts, hprf _ _ _ (isDerivationAddress_addrPrf key _)]

/-- A one-time key's leaf reads the derivations only at derivation addresses. -/
theorem otsPublicLeaf_congr (pp : PublicParam) (key : OtsKey) :
    otsPublicLeaf H pp prf key = otsPublicLeaf H pp prf' key := by
  rw [otsPublicLeaf, otsPublicLeaf, chainStarts_congr hprf]

/-- A one-time signature reads the derivations only at derivation addresses. -/
theorem otsSign_congr (pp : PublicParam) (key : OtsKey) (msg : ByteArray) :
    otsSign H pp prf key msg = otsSign H pp prf' key msg := by
  simp only [otsSign, chainStarts_congr hprf]

/-- The leaves of a tree read the derivations only at derivation addresses. -/
theorem leaves_congr (pp : PublicParam) (layer : Layer) (tree : Nat) :
    leaves H pp prf layer tree = leaves H pp prf' layer tree :=
  funext fun _ => otsPublicLeaf_congr H hprf _ _

/-- A tree's root reads the derivations only at derivation addresses. -/
theorem treeRoot_congr (pp : PublicParam) (layer : Layer) (tree : Nat) :
    treeRoot H pp prf layer tree = treeRoot H pp prf' layer tree := by
  rw [treeRoot, treeRoot, leaves_congr H hprf]

/-- A key's path reads the derivations only at derivation addresses. -/
theorem path_congr (pp : PublicParam) (layer : Layer) (tree e : Nat) :
    path H pp prf layer tree e = path H pp prf' layer tree e := by
  rw [path, path, leaves_congr H hprf]

/-- A FORS secret reads the derivations only at derivation addresses. -/
theorem forsSecret_congr (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) :
    forsSecret pp prf idx kappa l = forsSecret pp prf' idx kappa l := by
  simp only [forsSecret, hprf _ _ _ (isDerivationAddress_addrForsPrf idx kappa _)]

/-- The FORS leaves read the derivations only at derivation addresses. -/
theorem forsLeaves_congr (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) :
    forsLeaves H pp prf idx kappa = forsLeaves H pp prf' idx kappa :=
  funext fun _ => by simp only [forsLeaves, forsSecret_congr hprf]

/-- A FORS key reads the derivations only at derivation addresses. -/
theorem forsKey_congr (pp : PublicParam) (idx : Nat) :
    forsKey H pp prf idx = forsKey H pp prf' idx := by
  simp only [forsKey, forsNode, forsLeaves_congr H hprf]

/-- The FORS openings read the derivations only at derivation addresses. -/
theorem forsSign_congr (pp : PublicParam) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    forsSign H pp prf idx leaves = forsSign H pp prf' idx leaves := by
  simp only [forsSign, treeOpen, forsSecret_congr hprf, forsLeaves_congr H hprf]

/-- The randomizer reads the derivations only at a derivation address. -/
theorem randomizer_congr (pp : PublicParam) (msg : Message) :
    randomizer pp prf msg = randomizer pp prf' msg := by
  rw [randomizer, randomizer, hprf _ _ _ isDerivationAddress_addrRnd]

/-- The public parameter reads the derivations only at a derivation address. -/
theorem publicParamOf_congr : publicParamOf prf = publicParamOf prf' := by
  rw [publicParamOf, publicParamOf, hprf _ _ _ isDerivationAddress_addrParam]

/-- What a layer's key signs reads the derivations only at derivation addresses. -/
theorem layerMessage_congr (pp : PublicParam) (layer : Layer) (idx : Nat) :
    layerMessage H pp prf layer idx = layerMessage H pp prf' layer idx := by
  cases layer <;> simp only [layerMessage, forsKey_congr H hprf, treeRoot_congr H hprf]

/-- A layer's signature reads the derivations only at derivation addresses. -/
theorem signLayer_congr (pp : PublicParam) (layer : Layer) (idx : Nat) (msg : ByteArray) :
    signLayer H pp prf layer idx msg = signLayer H pp prf' layer idx msg := by
  simp only [signLayer, otsSign_congr H hprf, path_congr H hprf]

/-- The public key reads the derivations only at derivation addresses. -/
theorem publicKeyOf_congr : publicKeyOf H prf = publicKeyOf H prf' := by
  simp only [publicKeyOf, publicParamOf_congr hprf, treeRoot_congr H hprf]

/-- Signing reads the derivations only at derivation addresses. -/
theorem signDerived_congr (pp : PublicParam) (msg : Message) :
    signDerived H prf pp msg = signDerived H prf' pp msg := by
  simp only [signDerived, randomizer_congr hprf, forsSign_congr H hprf,
    layerMessage_congr H hprf, signLayer_congr H hprf]

end Congr

/-! ## Oracle worlds with derivations

A world with derivations adds derivation queries to the game's oracle.

The schemes of this section run in such worlds, and map back to the game's scheme. -/

/-- The game's oracle with derivation queries `X`, each answered with 32 bytes. -/
abbrev World (X : Type) :=
  XmssSecurity.HashSpec.withDerivations X XmssSecurity.HashOutput

/-- `H` in a world with derivations: the game's query, passed on. -/
def liftH (X : Type) (x : ByteArray) : OracleComp (World X) (Vector UInt8 32) :=
  simulateQ (XmssSecurity.HashSpec.withDerivationsLift X XmssSecurity.HashOutput) (H x)

/-- In the game, `H` is the oracle's answer to the input's bytes. -/
theorem H_eq (x : ByteArray) :
    H x = ofOutput <$> (liftM (XmssSecurity.OracleWorld.query (.inr x.data.toList)) :
      OracleComp XmssSecurity.OracleWorld _) := by
  unfold H queryH XmssSecurity.Concrete.oracleHash
  rfl

/-- A handler that undoes the lift turns the lifted `H` back into `H`. -/
theorem simulateQ_liftH {X : Type}
    (G : QueryImpl (World X) (OracleComp XmssSecurity.OracleWorld))
    (hG : G ∘ₛ XmssSecurity.HashSpec.withDerivationsLift X XmssSecurity.HashOutput =
      QueryImpl.id' _) (x : ByteArray) :
    simulateQ G (liftH X x) = H x := by
  rw [liftH, ← QueryImpl.simulateQ_compose, hG, simulateQ_id']

/-- A 32-byte answer read as a seed. -/
def seedOf (u : XmssSecurity.HashOutput) : Seed :=
  ofOutput u

/-- The verifier of the game over a hash: no signature never verifies. -/
def verifyOption {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))
    (pk : PublicKey) (msg : Message) : Option Signature → m Bool
  | none => pure false
  | some sig => verifyWith H pk msg sig

/-- leanSPHINCS with its derivations fixed: the scheme seed `s` is known. -/
noncomputable def seededScheme (s : Seed) :
    SignatureAlg (OracleComp XmssSecurity.OracleWorld) Message PublicKey Unit (Option Signature)
    where
  keygen := do
    let pk ← publicKeyOf H (seedPrf H s)
    return (pk, ())
  sign _ _ msg := do
    let pp ← publicParamOf (seedPrf H s)
    Except.toOption <$> signDerived H (seedPrf H s) pp msg
  verify := verifyOption H

/-- leanSPHINCS with the scheme seed as the one derivation. -/
noncomputable def seedScheme :
    SignatureAlg (OracleComp (World Unit)) Message PublicKey Unit (Option Signature) where
  keygen := do
    let u ← (World Unit).query (.inr ())
    let pk ← publicKeyOf (liftH Unit) (seedPrf (liftH Unit) (seedOf u))
    return (pk, ())
  sign _ _ msg := do
    let u ← (World Unit).query (.inr ())
    let pp ← publicParamOf (seedPrf (liftH Unit) (seedOf u))
    Except.toOption <$> signDerived (liftH Unit) (seedPrf (liftH Unit) (seedOf u)) pp msg
  verify := verifyOption (liftH Unit)

/-! ## The first hop: the key's seed -/

/-- The scheme seed `S = H("leanSPHINCS" | S_0)`, as the one derivation from the key's seed. -/
def seedEncoding :
    SecretEncoding XmssSecurity.HashSpec Seed Unit XmssSecurity.HashOutput where
  enc s _ := (seedInput s).data.toList
  range_eq _ _ := rfl
  injective _ _ _ _ := rfl

/-- The adversary in a world with derivations: its queries passed on, none of them a
derivation. -/
noncomputable def liftAdversary (X : Type)
    {A : SignatureAlg (OracleComp (World X)) Message PublicKey Unit (Option Signature)}
    (adversary : Adversary) : SignatureAlg.UnforgeableAdversary A :=
  adversary.toUnforgeableAdversary.mapOracles
    (XmssSecurity.HashSpec.withDerivationsLift X XmssSecurity.HashOutput)

section SeedMap

variable (seed : Seed)

local notation "φ" => simulateQ (seedEncoding.deriveImpl seed)

/-- Answering the scheme seed at its point sends the lifted `H` back to `H`. -/
theorem simulateQ_seedEncoding_liftH :
    (fun x => φ (liftH Unit x)) = H :=
  funext (simulateQ_liftH _ (SecretEncoding.deriveImpl_comp_withDerivationsLift _ seed))

/-- The derivations from a seed, mapped back, are the derivations from that seed. -/
theorem mapPrf_seedEncoding (s : Seed) :
    mapPrf (simulateQ (seedEncoding.deriveImpl seed)) (seedPrf (liftH Unit) s) = seedPrf H s := by
  rw [mapPrf_seedPrf, simulateQ_seedEncoding_liftH]

/-- The derivation of the scheme seed, answered at its point, is the hash that grows it. -/
theorem simulateQ_seedEncoding_query {β : Type} (k : Seed → OracleComp (World Unit) β) :
    φ ((World Unit).query (.inr ()) >>= fun u => k (seedOf u)) =
      schemeSeed H seed >>= fun s => φ (k s) := by
  rw [simulateQ_bind, schemeSeed_eq, H_eq]
  erw [bind_map_left]
  rfl

/-- Key generation of the derivation world, mapped back: the scheme seed, then the public key. -/
theorem simulateQ_seedEncoding_keygen :
    φ seedScheme.keygen = (fun pk => (pk, ())) <$>
      (schemeSeed H seed >>= fun s => publicKeyOf H (seedPrf H s)) := by
  refine (simulateQ_seedEncoding_query seed fun s =>
    publicKeyOf (liftH Unit) (seedPrf (liftH Unit) s) >>= fun pk => pure (pk, ())).trans ?_
  rw [map_bind]
  refine bind_congr fun s => ?_
  rw [simulateQ_bind, publicKeyOf_map_monad (simulateQ (seedEncoding.deriveImpl seed))
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f)]
  erw [mapPrf_seedEncoding]
  rw [simulateQ_seedEncoding_liftH]
  simp only [simulateQ_pure, map_eq_bind_pure_comp, Function.comp_def]

/-- Signing in the derivation world, mapped back, is the game's signing. -/
theorem simulateQ_seedEncoding_sign (pk : PublicKey) (msg : Message) :
    φ (seedScheme.sign pk () msg) = scheme.sign pk ⟨seed⟩ msg := by
  refine (simulateQ_seedEncoding_query seed fun s =>
    publicParamOf (seedPrf (liftH Unit) s) >>= fun pp =>
      Except.toOption <$> signDerived (liftH Unit) (seedPrf (liftH Unit) s) pp msg).trans ?_
  change _ = Except.toOption <$> signWith H ⟨seed⟩ msg
  rw [signWith, map_bind]
  refine bind_congr fun s => ?_
  rw [simulateQ_bind, publicParamOf_map_monad (simulateQ (seedEncoding.deriveImpl seed))
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f)]
  erw [mapPrf_seedEncoding]
  rw [map_bind]
  refine bind_congr fun pp => ?_
  rw [simulateQ_map, signDerived_map_monad (simulateQ (seedEncoding.deriveImpl seed))
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f)]
  erw [mapPrf_seedEncoding]
  rw [simulateQ_seedEncoding_liftH]

/-- Verification in the derivation world, mapped back, is the game's verification. -/
theorem simulateQ_seedEncoding_verify (pk : PublicKey) (msg : Message) (sig : Option Signature) :
    φ (seedScheme.verify pk msg sig) = scheme.verify pk msg sig := by
  cases sig with
  | none => rfl
  | some sig =>
    exact (verifyWith_map_monad (simulateQ (seedEncoding.deriveImpl seed))
      (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f) _ pk msg sig).trans
      (by rw [simulateQ_seedEncoding_liftH]; rfl)

end SeedMap

/-- **The first hop, as an equation.**

The game draws the key's seed, then runs the world where the scheme seed is the one derivation.

That derivation is answered at its point, and the secret key is put back in the transcript. -/
theorem unforgeableTranscriptExperiment_eq_seedEncoding (adversary : Adversary) :
    SignatureAlg.unforgeableTranscriptExperiment adversary.toUnforgeableAdversary =
      (liftM sampleSeed >>= fun seed =>
        SignatureAlg.UnforgeableTranscript.mapSk (fun _ => (⟨seed⟩ : SecretKey)) <$>
          simulateQ (seedEncoding.deriveImpl seed)
            (SignatureAlg.unforgeableTranscriptExperiment
              (liftAdversary Unit (A := seedScheme) adversary))) := by
  rw [SignatureAlg.unforgeableTranscriptExperiment_eq_bind_mapSk_of_keygen_eq_map scheme
    (fun seed => seedScheme.map (simulateQ' (seedEncoding.deriveImpl seed))) (liftM sampleSeed)
    (fun seed => schemeSeed H seed >>= fun s => publicKeyOf H (seedPrf H s))
    (fun _ pk => (pk, ())) (fun seed _ => ⟨seed⟩) ?hkg ?hkgA ?hsign ?hver]
  · refine bind_congr fun seed => ?_
    rw [liftAdversary, simulateQ_unforgeableTranscriptExperiment_withDerivationsLift _
      (SecretEncoding.deriveImpl_comp_withDerivationsLift _ seed)]
  case hkg =>
    simp only [scheme, keyGenWith, bind_assoc, pure_bind]
  case hkgA =>
    intro seed
    rw [SignatureAlg.map_keygen]
    exact simulateQ_seedEncoding_keygen seed
  case hsign =>
    intro seed pk msg
    rw [SignatureAlg.map_sign]
    exact (simulateQ_seedEncoding_sign seed pk msg).symm
  case hver =>
    intro seed
    funext pk msg sig
    rw [SignatureAlg.map_verify]
    exact (simulateQ_seedEncoding_verify seed pk msg sig).symm

/-! ## The second hop: the scheme seed -/

/-- Two inputs with the same bytes are equal. -/
theorem byteArray_eq_of_toList_eq {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

/-- The key's seed is fixed by the input that grows the scheme seed. -/
theorem seedInput_injective : Function.Injective seedInput := fun _ _ h =>
  Base.packBytes_injective (Xmss.byteArray_append_inj h rfl).2

/-- A 32-byte answer read as a seed: the seed fixes the answer. -/
theorem seedOf_injective : Function.Injective seedOf := fun _ _ h =>
  Xmss.Unforgeability.ofBV_inj (by decide) h

/-- An input of a derivation: the parameter, a derivation address and the suffix. -/
abbrev DerivationInput : Type :=
  {x : PublicParam × Address × ByteArray // IsDerivationAddress x.2.1}

/-- Every derivation `H(P' | A | S | suffix)` from the scheme seed `S`, as a derivation from `S`.

The secret is the 32-byte answer that the scheme seed reads. -/
def hiddenSeedEncoding :
    SecretEncoding XmssSecurity.HashSpec XmssSecurity.HashOutput DerivationInput
      XmssSecurity.HashOutput where
  enc u x := (thInput x.1.1 x.1.2.1 (packBytes (seedOf u) ++ x.1.2.2)).data.toList
  range_eq _ _ := rfl
  injective u x y h := by
    obtain ⟨hpp, hA, hpay⟩ := thInput_inj (byteArray_eq_of_toList_eq h)
    exact Subtype.ext (Prod.ext hpp (Prod.ext hA (Xmss.byteArray_append_inj hpay rfl).2))

/-- An encoded point fixes the secret: its bytes 32 to 63 are the scheme seed. -/
theorem hiddenSeedEncoding_fix (u u' : XmssSecurity.HashOutput) (x x' : DerivationInput)
    (h : hiddenSeedEncoding.enc u x = hiddenSeedEncoding.enc u' x') : u = u' := by
  obtain ⟨-, -, hpay⟩ := thInput_inj (byteArray_eq_of_toList_eq h)
  have hsize : (packBytes (seedOf u)).size = (packBytes (seedOf u')).size := by
    rw [Base.size_packBytes, Base.size_packBytes]
  exact seedOf_injective (Base.packBytes_injective (Xmss.byteArray_append_inj hpay hsize).1)

/-- A 32-byte answer as the output of a derivation. -/
def outputOf (u : XmssSecurity.HashOutput) : HashOutput :=
  ofOutput u

open Classical in
/-- The derivations as derivation queries.

The honest algorithms derive only at derivation addresses, so the value elsewhere is never read. -/
noncomputable def derivationPrf : SeedPrf (OracleComp (World DerivationInput)) :=
  fun pp A suffix =>
    if h : IsDerivationAddress A then
      outputOf <$> (World DerivationInput).query (.inr ⟨(pp, A, suffix), h⟩)
    else pure (outputOf 0)

/-- leanSPHINCS with every derivation a derivation query. -/
noncomputable def hiddenSeedScheme :
    SignatureAlg (OracleComp (World DerivationInput)) Message PublicKey Unit (Option Signature)
    where
  keygen := do
    let pk ← publicKeyOf (liftH DerivationInput) derivationPrf
    return (pk, ())
  sign _ _ msg := do
    let pp ← publicParamOf derivationPrf
    Except.toOption <$> signDerived (liftH DerivationInput) derivationPrf pp msg
  verify := verifyOption (liftH DerivationInput)

/-! ## Both hops end at the scheme with a known seed -/

section Seeded

variable (u : XmssSecurity.HashOutput)

/-- Fixing the scheme seed sends the lifted `H` back to `H`. -/
theorem simulateQ_fixDerivation_liftH :
    (fun x => simulateQ (fixDerivation u) (liftH Unit x)) = H :=
  funext (simulateQ_liftH _ (fixDerivation_comp_withDerivationsLift u))

/-- Answering the derivations at their points sends the lifted `H` back to `H`. -/
theorem simulateQ_hiddenSeedEncoding_liftH :
    (fun x => simulateQ (hiddenSeedEncoding.deriveImpl u) (liftH DerivationInput x)) = H :=
  funext (simulateQ_liftH _ (SecretEncoding.deriveImpl_comp_withDerivationsLift _ u))

/-- At a derivation address, a derivation query answered at its point is the derivation from the
scheme seed. -/
theorem simulateQ_hiddenSeedEncoding_derivationPrf (pp : PublicParam) (A : Address)
    (suffix : ByteArray) (h : IsDerivationAddress A) :
    simulateQ (hiddenSeedEncoding.deriveImpl u) (derivationPrf pp A suffix) =
      seedPrf H (seedOf u) pp A suffix := by
  simp only [derivationPrf, h, ↓reduceDIte, simulateQ_map, simulateQ_spec_query, seedPrf, thFull]
  exact Eq.trans rfl (H_eq _).symm

/-- The derivations from a seed, with the scheme seed fixed, are the derivations from that
seed. -/
theorem mapPrf_fixDerivation (s : Seed) :
    mapPrf (simulateQ (fixDerivation u)) (seedPrf (liftH Unit) s) = seedPrf H s := by
  rw [mapPrf_seedPrf, simulateQ_fixDerivation_liftH]

/-- Fixing the scheme seed to `u` gives leanSPHINCS with the scheme seed `u`. -/
theorem seedScheme_map_fixDerivation :
    seedScheme.map (simulateQ' (fixDerivation u)) = seededScheme (seedOf u) := by
  refine SignatureAlg.ext ?_ (funext fun pk => funext fun _ => funext fun msg => ?_)
    (funext fun pk => funext fun msg => funext fun sig => ?_)
  · rw [SignatureAlg.map_keygen]
    dsimp only [seedScheme, seededScheme]
    rw [simulateQ_bind, simulateQ_spec_query]
    simp only [fixDerivation, pure_bind]
    rw [simulateQ_bind, publicKeyOf_map_monad (simulateQ (fixDerivation u))
      (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f)]
    erw [mapPrf_fixDerivation]
    rw [simulateQ_fixDerivation_liftH]
    simp only [simulateQ_pure]
  · rw [SignatureAlg.map_sign]
    dsimp only [seedScheme, seededScheme]
    rw [simulateQ_bind, simulateQ_spec_query]
    simp only [fixDerivation, pure_bind]
    rw [simulateQ_bind, publicParamOf_map_monad (simulateQ (fixDerivation u))
      (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f)]
    erw [mapPrf_fixDerivation]
    refine bind_congr fun pp => ?_
    rw [simulateQ_map, signDerived_map_monad (simulateQ (fixDerivation u))
      (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f)]
    erw [mapPrf_fixDerivation]
    rw [simulateQ_fixDerivation_liftH]
  · rw [SignatureAlg.map_verify]
    cases sig with
    | none => rfl
    | some sig =>
      exact (verifyWith_map_monad (simulateQ (fixDerivation u))
        (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f) _ pk msg sig).trans
        (by rw [simulateQ_fixDerivation_liftH]; rfl)

/-- Answering every derivation at its point under `u` gives leanSPHINCS with the scheme seed
`u`. -/
theorem hiddenSeedScheme_map_deriveImpl :
    hiddenSeedScheme.map (simulateQ' (hiddenSeedEncoding.deriveImpl u)) =
      seededScheme (seedOf u) := by
  have hprf := simulateQ_hiddenSeedEncoding_derivationPrf u
  refine SignatureAlg.ext ?_ (funext fun pk => funext fun _ => funext fun msg => ?_)
    (funext fun pk => funext fun msg => funext fun sig => ?_)
  · rw [SignatureAlg.map_keygen]
    dsimp only [hiddenSeedScheme, seededScheme]
    rw [simulateQ_bind, publicKeyOf_map_monad (simulateQ (hiddenSeedEncoding.deriveImpl u))
      (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
      simulateQ_hiddenSeedEncoding_liftH, publicKeyOf_congr H hprf]
    simp only [simulateQ_pure]
  · rw [SignatureAlg.map_sign]
    dsimp only [hiddenSeedScheme, seededScheme]
    rw [simulateQ_bind, publicParamOf_map_monad (simulateQ (hiddenSeedEncoding.deriveImpl u))
      (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f), publicParamOf_congr hprf]
    refine bind_congr fun pp => ?_
    rw [simulateQ_map, signDerived_map_monad (simulateQ (hiddenSeedEncoding.deriveImpl u))
      (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
      simulateQ_hiddenSeedEncoding_liftH, signDerived_congr H hprf]
  · rw [SignatureAlg.map_verify]
    cases sig with
    | none => rfl
    | some sig =>
      exact (verifyWith_map_monad (simulateQ (hiddenSeedEncoding.deriveImpl u))
        (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f) _ pk msg sig).trans
        (by rw [simulateQ_hiddenSeedEncoding_liftH]; rfl)

end Seeded

/-! ## The budgets of the hops -/

section Budget

variable {X : Type}

/-- A public query at an input that satisfies `q`. -/
def IsPublicQuery (q : List UInt8 → Prop) : (World X).Domain → Prop
  | .inl (.inr x) => q x
  | _ => False

/-- A public query in `q` is decidable when `q` is. -/
instance (q : List UInt8 → Prop) [DecidablePred q] :
    DecidablePred (IsPublicQuery (X := X) q) := by
  rintro ((_ | _) | _) <;> simp only [IsPublicQuery] <;> infer_instance

variable {q : List UInt8 → Prop} [DecidablePred q]

/-- In a world with derivations, `H` is a public query at the input's bytes. -/
theorem liftH_eq (x : ByteArray) :
    liftH X x = ofOutput <$> ((World X).query (.inl (.inr x.data.toList)) :
      OracleComp (World X) _) := by
  rw [liftH, H_eq, simulateQ_map, simulateQ_spec_query]
  rfl

/-- `H` at an input outside `q` makes no query in `q`. -/
theorem liftH_isQueryBoundP_zero {x : ByteArray} (hx : ¬q x.data.toList) :
    IsQueryBoundP (liftH X x) (IsPublicQuery q) 0 := by
  rw [liftH_eq]
  exact (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => absurd h hx)

/-- A derivation query is not a public query. -/
theorem derivation_isQueryBoundP_zero (x : X) :
    IsQueryBoundP ((World X).query (.inr x) : OracleComp (World X) _) (IsPublicQuery q) 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => h.elim

/-- The adversary's hash budget bounds the public queries of the whole experiment in `q`, when
key generation, signing and verification make none. -/
theorem isQueryBoundP_liftAdversary
    {A : SignatureAlg (OracleComp (World X)) Message PublicKey Unit (Option Signature)}
    {adversary : Adversary} {qH qS : Nat} (hadversary : adversary.RomQueryBound qH qS)
    (hkeygen : IsQueryBoundP A.keygen (IsPublicQuery q) 0)
    (hsign : ∀ pk sk msg, IsQueryBoundP (A.sign pk sk msg) (IsPublicQuery q) 0)
    (hverify : ∀ pk msg sig, IsQueryBoundP (A.verify pk msg sig) (IsPublicQuery q) 0) :
    IsQueryBoundP (SignatureAlg.unforgeableTranscriptExperiment
      (liftAdversary X (A := A) adversary)) (IsPublicQuery q) qH :=
  SignatureAlg.isQueryBoundP_unforgeableTranscriptExperiment_mapOracles _
    (fun pk => (hadversary pk).1)
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun t ht => (isQueryBoundP_query_iff _ _ _).2 fun h => by
      rcases t with n | t
      · exact h.elim
      · exact absurd trivial ht)
    hkeygen hsign hverify

/-- Verification with the lifted `H` makes no query in `q` when no honest call input is in `q`. -/
theorem verifyOption_isQueryBoundP_zero
    (hH : ∀ pp A payload, ¬IsDerivationAddress A → 16 ≤ payload.size →
      ¬q (thInput pp A payload).data.toList) (pk : PublicKey) (msg : Message)
    (sig : Option Signature) :
    IsQueryBoundP (verifyOption (liftH X) pk msg sig) (IsPublicQuery q) 0 := by
  cases sig with
  | none => exact isQueryBoundP_pure _ _ _
  | some sig =>
    exact verifyWith_isQueryBoundP_zero _
      (fun pp A payload hA hsize => liftH_isQueryBoundP_zero (hH pp A payload hA hsize)) pk msg sig

end Budget

/-- An input that grows the scheme seed has 43 bytes. -/
def IsSeedLength (x : List UInt8) : Prop :=
  x.length = 43

/-- The length of an input is decidable. -/
instance : DecidablePred IsSeedLength :=
  fun x => inferInstanceAs (Decidable (x.length = 43))

/-- The bytes of an input are as many as its size. -/
theorem length_toList (x : ByteArray) : x.data.toList.length = x.size :=
  Array.length_toList

/-- No honest hash outside the derivations has 43 bytes. -/
theorem not_isSeedLength_thInput (pp : PublicParam) (A : Address) (payload : ByteArray)
    (_ : ¬IsDerivationAddress A) (h : 16 ≤ payload.size) :
    ¬IsSeedLength (thInput pp A payload).data.toList := by
  rw [IsSeedLength, length_toList, size_thInput]
  omega

/-- The first hop's experiment makes at most `qH` queries of 43 bytes: the adversary's own. -/
theorem isQueryBoundP_seedScheme {adversary : Adversary} {qH qS : Nat}
    (hadversary : adversary.RomQueryBound qH qS) :
    IsQueryBoundP (SignatureAlg.unforgeableTranscriptExperiment
      (liftAdversary Unit (A := seedScheme) adversary)) (IsPublicQuery IsSeedLength) qH := by
  have hH := fun pp A payload hA hsize =>
    liftH_isQueryBoundP_zero (X := Unit) (not_isSeedLength_thInput pp A payload hA hsize)
  have hprf : ∀ s pp A suffix, IsQueryBoundP (seedPrf (liftH Unit) s pp A suffix)
      (IsPublicQuery IsSeedLength) 0 := fun s pp A suffix =>
    liftH_isQueryBoundP_zero (by
      rw [IsSeedLength, length_toList, size_thInput, ByteArray.size_append, Base.size_packBytes]
      simp only [SEED_LEN]
      omega)
  refine isQueryBoundP_liftAdversary (A := seedScheme) hadversary ?_ (fun pk _ msg => ?_)
    (verifyOption_isQueryBoundP_zero not_isSeedLength_thInput)
  · exact isQueryBoundP_bind_zero _ _ (derivation_isQueryBoundP_zero ()) fun u =>
      isQueryBoundP_bind_zero _ _ (publicKeyOf_isQueryBoundP_zero _ _ hH (hprf _)) fun _ =>
        isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_bind_zero _ _ (derivation_isQueryBoundP_zero ()) fun u =>
      isQueryBoundP_bind_zero _ _ (publicParamOf_isQueryBoundP_zero _ (hprf _)) fun pp =>
        (isQueryBoundP_map_iff _ _ _).2 (signDerived_isQueryBoundP_zero _ _ hH (hprf _) pp msg)

/-- A public input that some scheme seed encodes as a derivation. -/
def IsDerivationPoint (x : List UInt8) : Prop :=
  ∃ u y, hiddenSeedEncoding.enc u y = x

open Classical in
/-- Being a derivation point is decided classically. -/
noncomputable instance : DecidablePred IsDerivationPoint :=
  Classical.decPred _

/-- No honest hash outside the derivations is at a derivation point. -/
theorem not_isDerivationPoint_thInput (pp : PublicParam) (A : Address) (payload : ByteArray)
    (hA : ¬IsDerivationAddress A) (_ : 16 ≤ payload.size) :
    ¬IsDerivationPoint (thInput pp A payload).data.toList := fun ⟨_, y, h⟩ =>
  hA ((thInput_inj (byteArray_eq_of_toList_eq h)).2.1 ▸ y.2)

/-- The second hop's experiment makes at most `qH` queries at derivation points: the
adversary's own. -/
theorem isQueryBoundP_hiddenSeedScheme {adversary : Adversary} {qH qS : Nat}
    (hadversary : adversary.RomQueryBound qH qS) :
    IsQueryBoundP (SignatureAlg.unforgeableTranscriptExperiment
      (liftAdversary DerivationInput (A := hiddenSeedScheme) adversary))
      (IsPublicQuery IsDerivationPoint) qH := by
  have hH := fun pp A payload hA hsize => liftH_isQueryBoundP_zero (X := DerivationInput)
    (q := IsDerivationPoint) (not_isDerivationPoint_thInput pp A payload hA hsize)
  have hprf : ∀ pp A suffix, IsQueryBoundP (derivationPrf pp A suffix)
      (IsPublicQuery IsDerivationPoint) 0 := fun pp A suffix => by
    rw [derivationPrf]
    split
    · exact (isQueryBoundP_map_iff _ _ _).2 (derivation_isQueryBoundP_zero _)
    · exact isQueryBoundP_pure _ _ _
  refine isQueryBoundP_liftAdversary (A := hiddenSeedScheme) hadversary ?_
    (fun pk _ msg => ?_) (verifyOption_isQueryBoundP_zero not_isDerivationPoint_thInput)
  · exact isQueryBoundP_bind_zero _ _ (publicKeyOf_isQueryBoundP_zero _ _ hH hprf) fun _ =>
      isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_bind_zero _ _ (publicParamOf_isQueryBoundP_zero _ hprf) fun pp =>
      (isQueryBoundP_map_iff _ _ _).2 (signDerived_isQueryBoundP_zero _ _ hH hprf pp msg)

/-! ## The two hops -/

/-- The forging advantage is the chance that the transcript of the game wins. -/
theorem forgeAdvantage_eq (adversary : Adversary) :
    forgeAdvantage adversary =
      Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
        (SignatureAlg.unforgeableTranscriptExperiment adversary.toUnforgeableAdversary)).run ∅}[
        z.1.strongWins = true] := by
  rw [forgeAdvantage, SignatureAlg.strongUnforgeableAdvantage, ProbCompRuntime.rom_evalDist,
    ← SignatureAlg.map_strongWins_unforgeableTranscriptExperiment, simulateQ_map,
    ← prEvent_eq_evalDist_singleton, StateT.run'_eq, StateT.run_map, Functor.map_map,
    prEvent_map]

/-- There are `2^256` seeds. -/
theorem natCard_seed : Nat.card Seed = 2 ^ 256 := by
  change Nat.card (Vector UInt8 32) = 2 ^ 256
  rw [Nat.card_congr (arrayVectorEquivFin UInt8 32), Nat.card_fun, Nat.card_eq_fintype_card,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, Nat.card_eq_fintype_card,
    Fintype.card_fin, ← pow_mul]

/-- There are `2^256` answers of the oracle. -/
theorem natCard_hashOutput : Nat.card XmssSecurity.HashOutput = 2 ^ 256 := by
  rw [Nat.card_eq_fintype_card, ← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  rfl

/-- A uniform seed is encoded at a given point with probability at most `2^-256`. -/
theorem prEvent_seedEncoding_le (t : List UInt8) :
    Pr{let s ← sampleSeed}[t ∈ Set.range (seedEncoding.enc s)] ≤ ((2 : ENNReal) ^ 256)⁻¹ := by
  let _ : SampleableType Seed := SampleableType.ofFintype Seed
  refine (prEvent_mem_range_enc_le seedEncoding
    (fun _ _ _ _ h => seedInput_injective (byteArray_eq_of_toList_eq h)) t).trans_eq ?_
  rw [natCard_seed, Nat.cast_pow, Nat.cast_ofNat]

/-- A uniform answer is the scheme seed of a given derivation point with probability at most
`2^-256`. -/
theorem prEvent_hiddenSeedEncoding_le (t : List UInt8) :
    Pr{let u ← $ᵗ XmssSecurity.HashOutput}[t ∈ Set.range (hiddenSeedEncoding.enc u)] ≤
      ((2 : ENNReal) ^ 256)⁻¹ := by
  refine (prEvent_mem_range_enc_le hiddenSeedEncoding hiddenSeedEncoding_fix t).trans_eq ?_
  rw [natCard_hashOutput, Nat.cast_pow, Nat.cast_ofNat]

/-- A transcript wins as strongly with its secret key replaced. -/
theorem strongWins_mapSk {M PK SK SK' S : Type} (g : SK' → SK)
    (z : SignatureAlg.UnforgeableTranscript M PK SK' S) :
    (z.mapSk g).strongWins = z.strongWins := by
  rw [Bool.eq_iff_iff, SignatureAlg.UnforgeableTranscript.strongWins_eq_true_iff,
    SignatureAlg.UnforgeableTranscript.strongWins_eq_true_iff,
    SignatureAlg.UnforgeableTranscript.mapSk_log, SignatureAlg.UnforgeableTranscript.mapSk_sig,
    SignatureAlg.UnforgeableTranscript.mapSk_verified, SignatureAlg.UnforgeableTranscript.mapSk_msg]

/-- **The two seeds are hidden.**

The forging advantage is at most the chance of a forgery in the ideal game, plus `qH / 2^256` for
each of the two seeds.

In the ideal game, every derivation is an independent uniform answer, and no seed is left.

The budget counts only the adversary's hash queries, `qH`. -/
theorem forgeAdvantage_le_hiddenSeed (adversary : Adversary) {qH qS : Nat}
    (hadversary : adversary.RomQueryBound qH qS) :
    forgeAdvantage adversary ≤
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl XmssSecurity.HashSpec DerivationInput
          XmssSecurity.HashOutput) (SignatureAlg.unforgeableTranscriptExperiment
            (liftAdversary DerivationInput (A := hiddenSeedScheme) adversary))).run (∅, ∅)}[
          z.1.strongWins = true] +
        qH * ((2 : ENNReal) ^ 256)⁻¹ + qH * ((2 : ENNReal) ^ 256)⁻¹ := by
  rw [forgeAdvantage_eq, unforgeableTranscriptExperiment_eq_seedEncoding, simulateQ_bind,
    StateT.run_bind, OracleSpec.simulateQ_romImpl_liftM_run, bind_map_left]
  simp only [simulateQ_map, StateT.run_map]
  have hT : ∀ u, simulateQ (fixDerivation u) (SignatureAlg.unforgeableTranscriptExperiment
        (liftAdversary Unit (A := seedScheme) adversary)) =
      simulateQ (hiddenSeedEncoding.deriveImpl u) (SignatureAlg.unforgeableTranscriptExperiment
        (liftAdversary DerivationInput (A := hiddenSeedScheme) adversary)) := fun u => by
    rw [liftAdversary, liftAdversary,
      simulateQ_unforgeableTranscriptExperiment_withDerivationsLift _
        (fixDerivation_comp_withDerivationsLift u),
      simulateQ_unforgeableTranscriptExperiment_withDerivationsLift _
        (SecretEncoding.deriveImpl_comp_withDerivationsLift _ u),
      SignatureAlg.unforgeableTranscriptExperiment_congr (seedScheme_map_fixDerivation u),
      SignatureAlg.unforgeableTranscriptExperiment_congr (hiddenSeedScheme_map_deriveImpl u)]
  have h1 := prEvent_romImpl_deriveImpl_le seedEncoding (ms := sampleSeed)
    (ε := ((2 : ENNReal) ^ 256)⁻¹) prEvent_seedEncoding_le (p := IsPublicQuery IsSeedLength)
    (fun s _ => by
      change ((seedInput s).data.toList).length = 43
      rw [length_toList, size_seedInput])
    (isQueryBoundP_seedScheme hadversary) (fun _ z => z.strongWins = true)
  have h2 := prEvent_romImpl_deriveImpl_le hiddenSeedEncoding
    (ms := $ᵗ XmssSecurity.HashOutput)
    (ε := ((2 : ENNReal) ^ 256)⁻¹) prEvent_hiddenSeedEncoding_le
    (p := IsPublicQuery IsDerivationPoint)
    (fun u y => ⟨u, y, rfl⟩)
    (isQueryBoundP_hiddenSeedScheme hadversary) (fun _ z => z.strongWins = true)
  have h3 := prEvent_idealImpl_eq_bind_fixDerivation
    (SignatureAlg.unforgeableTranscriptExperiment (liftAdversary Unit (A := seedScheme) adversary))
    (fun z => z.strongWins = true)
  simp only [hT] at h3
  simp only [prEvent_norm, strongWins_mapSk] at h1 h2 h3 ⊢
  rw [OracleComp.prEvent_bind_const, h3] at h1
  rw [OracleComp.prEvent_bind_const] at h2
  exact h1.trans (add_le_add_left h2 _)

end EthLib.Cryptography.Sphincs.Unforgeability

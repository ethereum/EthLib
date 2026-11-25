module

public import EthLib.Cryptography.Proofs.SupportBind
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Game
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Seeded.Presampling

/-!
# From the real experiment to the table game

This file reaches the real game from a uniform scheme seed `S`, the inner game.

The scheme-seed step reaches the inner game from the real experiment.

Presampling every derivation and the model's key generation before it changes nothing.

Afterwards the real key generation is cached.

The rest of the real game wins as the model's game with the table signer, with fewer hash calls.

A budget of `q - 1` from `S` leaves `q - K` hash calls after key generation.
-/

@[expose] public section

open OracleComp OracleSpec
open EthLib.Cryptography.Xmss.Unforgeability (toModelAdversary ofPublicKey ofSeed ofParam scheme)
open EthLib.Cryptography.SufCma (gameAfterKeys)

open EthLib.Cryptography.Xmss.Unforgeability renaming Adversary → EthAdversary
namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-- The model's key generation over the table, after programming the derivations. -/
noncomputable def preparation (seed : MasterSeed) :
    OracleComp HashSpec (Derivations × ((Digest × (TopIndex → Option (Randomness × Encoding))) ×
      QueryLog HashSpec)) := do
  let d ← programDerivations seed
  let result ← (honestRun d).withQueryLog
  return (d, result)

theorem run_preparation (seed : MasterSeed) :
    ((simulateQ randomOracle (preparation seed)).run ∅) =ᵈ
      (do
        let d ← drawDerivations
        let r ← (simulateQ randomOracle (honestRun d).withQueryLog).run (progCache seed d)
        pure ((d, r.1), r.2)) := by
  unfold preparation
  rw [simulateQ_bind, StateT.run_bind]
  refine (evalDist_programDerivations_draw seed _).trans (.of_eq ?_)
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]

theorem mem_support_preparation (seed : MasterSeed) (d : Derivations)
    (r : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec)
    (cache : QueryCache HashSpec)
    (hr : (r, cache) ∈ support ((simulateQ randomOracle (honestRun d).withQueryLog).run (progCache seed d))) :
    ((d, r), cache) ∈ support ((simulateQ randomOracle (preparation seed)).run ∅) := by
  -- Step through each bind by an equation: the kernel would run the draw to match two forms.
  rw [OracleComp.support_eq_of_evalDistEq (run_preparation seed)]
  refine mem_support_bind_of_eq _ _ (mem_support_drawDerivations d) fun _ same => same ▸ ?_
  refine mem_support_bind_of_eq _ _ hr fun _ same => same ▸ ?_
  rw [mem_support_pure_iff]

/-- The table game reached from a seed.

It draws the derivations and prepares the model key from the programmed cache.

Then it runs the model's game with the table signer. -/
noncomputable def tableGame (adversary : EthAdversary) (seed : MasterSeed) : ProbComp Bool := do
  let d ← drawDerivations
  let r ← (simulateQ randomOracle (honestRun d).withQueryLog).run (progCache seed d)
  (simulateQ romImpl (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary)
    (modelPublicKey d r.1) (modelSecretKey d r.1))).run' r.2

/-- EthLib's game from the scheme's seed `S`: key generation from `S`, then the rest of the game.

Its signer keeps the key that key generation returned, and each key that signing returns. -/
noncomputable def realAfterSeed (adversary : EthAdversary)
    (seed : MasterSeed) : OracleComp OracleWorld Bool :=
  (liftM (realKeygen seed) : OracleComp OracleWorld _) >>= fun keys =>
    gameAfterKeys scheme adversary keys.1 keys.2

/-- The real game with `S` sampled uniformly rather than hashed from the key's seed. -/
noncomputable def innerGame (adversary : EthAdversary) : OracleComp OracleWorld Bool :=
  (liftM sampleMasterSeed : OracleComp OracleWorld _) >>= realAfterSeed adversary

/-- After the preparation, EthLib's game from `S` wins as the model's game with the table signer.

Key generation is cached, and gives a key that the cache knows. -/
theorem evalDist_afterKeygen (adversary : EthAdversary) {seed : MasterSeed} {d : Derivations}
    {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
    {cache : QueryCache HashSpec} (h : Prepared seed d result cache) :
    (simulateQ romImpl (realAfterSeed adversary seed)).run' cache =ᵈ
      (simulateQ romImpl (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary)
        (modelPublicKey d result) (modelSecretKey d result))).run' cache := by
  obtain ⟨top, htop, hkeys⟩ := h.realKeygen
  have herase :=
    (erases_pure_of_resolves (computation := realKeygen seed) hkeys).lift_hash.bind_known
    (fun keys => gameAfterKeys scheme adversary keys.1 keys.2) _
    (Erases.refl _ (gameAfterKeys scheme adversary (ofPublicKey ⟨result.1.1, d.parameter⟩)
      { schemeSeed := ofSeed seed, publicParam := ofParam d.parameter, top, cache := [] }))
  have hrun := (herase.evalDist_run cache le_rfl).map Prod.fst
  simp only [← StateT.run'_eq] at hrun
  exact hrun.trans (h.evalDist_rest ⟨rfl, rfl, htop, fun _ ht => absurd ht List.not_mem_nil⟩
    adversary)

/-- The inner game's winning distribution is the table game's. -/
theorem evalDist_innerGame (adversary : EthAdversary) :
    ((simulateQ romImpl (innerGame adversary)).run' ∅) =ᵈ (sampleMasterSeed >>= tableGame adversary) := by
  rw [innerGame, run'_lift_sample_bind]
  apply EvalDistEq.bind_right
  intro seed
  refine (evalDist_presample_computation _ (liftM (preparation seed) : OracleComp OracleWorld _) ∅).trans ?_
  rw [lift_hash_romImpl]
  refine ((run_preparation seed).bind_left _).trans ?_
  unfold tableGame
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro d
  apply OracleComp.EvalDistEq.bind_congr_of_support
  -- Name both components: the kernel would run the preparation to match a pair with its parts.
  intro ⟨r, cache⟩ hr
  have h := prepared_of_mem seed d r cache hr
  exact evalDist_afterKeygen adversary h

theorem probOutput_countHashQueries (computation : OracleComp OracleWorld Bool) :
    Pr{let result ← (simulateQ romImpl (countHashQueries computation)).run' ∅}[result.1 = true] =
      Pr{let x ← (simulateQ romImpl computation).run' ∅}[x = true] := by
  have h := congrArg (fun c : OracleComp OracleWorld Bool => (simulateQ romImpl c).run' ∅)
    (countHashQueries_forget computation)
  simp only [simulateQ_map, StateT.run'_map'] at h
  rw [← h]
  exact (prEvent_map _ Prod.fst (· = true)).symm

/-- The inner game's winning probability is the table game's. -/
theorem innerGame_eq_tableGame (adversary : EthAdversary) :
    Pr{let x ← (simulateQ romImpl (innerGame adversary)).run' ∅}[x = true] =
      Pr{let x ← sampleMasterSeed >>= tableGame adversary}[x = true] :=
  (evalDist_innerGame adversary).prEvent_eq (· = true)

/-! ## Budgets -/

/-- The real budget `q` less the seed hash bounds the real game from every scheme seed. -/
def SeededBudget (adversary : EthAdversary) (q : Nat) : Prop :=
  ∀ seed, HashQueryBound (realAfterSeed adversary seed) ∅ (q - 1)

/-- The real budget `q` leaves `q - K` hash calls for the table game after key generation. -/
theorem afterKeygen_budget (adversary : EthAdversary) (q : Nat)
    (hbound : SeededBudget adversary q) (seed : MasterSeed) (d : Derivations)
    (r : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec)
    (cache : QueryCache HashSpec)
    (hr : (r, cache) ∈ support ((simulateQ randomOracle (honestRun d).withQueryLog).run (progCache seed d))) :
    keygenQueries ≤ q ∧
      HashQueryBound (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary) (modelPublicKey d r)
        (modelSecretKey d r)) cache (q - keygenQueries) := by
  have hprep := hashQueryBound_after_preparation _ (liftM (preparation seed) : OracleComp OracleWorld _) ∅
    (q - 1) (hbound seed) ((d, r), cache) (by
      rw [lift_hash_romImpl]
      exact mem_support_preparation seed d r cache hr)
  have h := prepared_of_mem seed d r cache hr
  obtain ⟨top, htop, hkeys⟩ := h.realKeygen
  have hrun := run_countHashQueries_lift_of_resolves (c := realKeygen seed) (queryCount_realKeygen seed)
    hkeys
  have hfirst := hashQueryBound_bind (realKeygen seed)
    (fun keys => gameAfterKeys scheme adversary keys.1 keys.2) cache (q - 1) hprep
    (((ofPublicKey (modelPublicKey d r),
      { schemeSeed := ofSeed seed, publicParam := ofParam d.parameter, top, cache := [] }),
      keygenQueries - 1), cache)
    (by rw [hrun]; simp [modelPublicKey])
  have hK : keygenQueries - 1 ≤ q - 1 := hfirst.1
  have hK' := keygenQueries_eq
  refine ⟨by omega, ?_⟩
  rw [show q - keygenQueries = q - 1 - (keygenQueries - 1) by omega]
  exact h.hashQueryBound_rest ⟨rfl, rfl, htop, fun _ ht => absurd ht List.not_mem_nil⟩ adversary _
    hfirst.2

end XmssSecurity.Bridge

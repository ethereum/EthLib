module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Cost
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.VerifyQueries

/-!
# Proofs: the hash calls of leanSPHINCS key generation, signing and verification

The calls are counted under a fixed answer function, as in the signing cost of the security proof.

Each call of `H` makes exactly one query under that function, as the game's hash does.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Cost

open OracleComp OracleSpec
open EthLib.Cryptography.Sphincs.Constants
open EthLib.Cryptography.Sphincs.Unforgeability
open EthLib.Cryptography.Sphincs.Unforgeability.Bridge
open HashSig (HashSpec queriesWith length_queriesWith_le)
open SphincsSecurity.Security.Prefix (hashCalls hashCalls_bind hashCalls_pure)

variable (f : QueryImpl HashSpec Id)

/-- The hash calls of a computation are the inputs it queries, counted. -/
theorem hashCalls_eq_length_queriesWith {α : Type} (oa : OracleComp HashSpec α) :
    hashCalls f oa = (queriesWith f oa).length := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind input next ih =>
    change (SphincsSecurity.Security.queriedInputs f
      (liftM (HashSpec.query input) >>= next)).length = _
    rw [SphincsSecurity.Security.queriedInputs_query_bind, List.length_cons]
    exact congrArg (· + 1) (ih (f input))

/-- The bound `470595 + 3 * 2^32` of signing is `12885372483`. -/
theorem signCalls_eq : 470595 + 3 * MAX_COUNTER_TRIALS = 12885372483 := by
  decide

variable (H : ByteArray → OracleComp HashSpec (Vector UInt8 32))
  (hH : ∀ input, hashCalls f (H input) = 1)

include hH

/-- Key generation makes exactly `264193` calls. -/
theorem hashCalls_keyGenWith_eq (seed : Seed) : hashCalls f (keyGenWith H seed) = 264193 :=
  (Bridge.hashCalls_keyGenWith f H hH seed).trans keyGenCalls_eq

/-- The counter search of a one-time signature makes at most `2^32` calls.

It tries at most `2^32` counters, one call each. -/
theorem hashCalls_findCounter_le (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) :
    hashCalls f (Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS) ≤
      MAX_COUNTER_TRIALS := by
  rw [Bridge.hashCalls_findCounter f H hH]
  exact searchCalls_le _ 0 _

/-- Signing makes at most `470595 + 3 * 2^32` calls, whatever the answers.

It bounds the calls of one signing request, with a hash of one oracle call as in the game. -/
theorem hashCalls_signWith_le (sk : SecretKey) (msg : Message) :
    hashCalls f (signWith H sk msg) ≤ 470595 + 3 * MAX_COUNTER_TRIALS := by
  let key := evalWithAnswerFn f (expandKey H sk.seed)
  let top := evalWithAnswerFn f (buildTree H key.pkSeed (prf H key.pkSeed sk.seed) .top 0)
  let rho := evalWithAnswerFn f (prfMsg H key.skPrf key.pkSeed msg)
  let idx := digestIndex (evalWithAnswerFn f (hMsg H rho key.pkSeed top.value msg))
  have hsecrets : ∀ adrs, hashCalls f (prf H key.pkSeed sk.seed adrs) = 1 :=
    hashCalls_prf f H hH _ _
  -- A layer makes at most its build, all counters and its chains.
  --
  -- So the signing bound charges each of the three searches all `2^32` counters.
  let bound : Layer → Nat := fun layer => buildCalls layer + MAX_COUNTER_TRIALS + (V + TARGET_SUM)
  have hlayer : ∀ layer, layerCalls f H (prf H key.pkSeed sk.seed) key.pkSeed idx layer ≤
      bound layer := by
    intro layer
    have hsearch : hashCalls f (layerSearch f H (prf H key.pkSeed sk.seed) key.pkSeed idx layer) ≤
        MAX_COUNTER_TRIALS := hashCalls_findCounter_le f H hH _ _ _
    rw [layerCalls_eq f H hH _ hsecrets]
    dsimp only [bound]
    split <;> omega
  have hsum : layersCost (layerSigns f H (prf H key.pkSeed sk.seed) key.pkSeed idx) bound ≤
      bound .bottom + bound .middle + bound .top := by
    unfold layersCost
    split
    · split <;> omega
    · omega
  have hcost := (layersCost_le _ hlayer).trans hsum
  rw [hashCalls_signWith_layers f H hH sk msg key top rho idx rfl rfl rfl rfl, signPrefixCalls_eq]
  obtain ⟨hb, hm, ht⟩ := buildCalls_eq
  have hchains : V + TARGET_SUM = 192 := by decide
  simp only [bound, hb, hm, ht, hchains] at hcost
  omega

omit hH in
/-- Verification makes at most `491` calls, when each call of `H` makes at most one query.

It restates the bound of the verification proofs in the count of the signing proofs.

The hypothesis bounds every path of `H`, so it holds under every answer function. -/
theorem hashCalls_verifyWith_le (hHbound : ∀ input, IsTotalQueryBound (H input) 1)
    (pk : PublicKey) (msg : Message) (sig : Signature) :
    hashCalls f (verifyWith H pk msg sig) ≤ 491 := by
  rw [hashCalls_eq_length_queriesWith, ← verifyCalls_eq]
  exact length_queriesWith_le f (verifyWith_isTotalQueryBound H hHbound pk msg sig)

/-- A signature that verifies is checked with exactly `491` calls.

It restates the exact count of the verification proofs in the count of the signing proofs. -/
theorem hashCalls_verifyWith_of_verify (pk : PublicKey) (msg : Message) (sig : Signature)
    (h : evalWithAnswerFn f (verifyWith H pk msg sig) = true) :
    hashCalls f (verifyWith H pk msg sig) = 491 := by
  rw [hashCalls_eq_length_queriesWith, ← verifyCalls_eq]
  exact length_queriesWith_verifyWith f H
    (fun x => (hashCalls_eq_length_queriesWith f (H x)).symm.trans (hH x)) pk msg sig h

end EthLib.Cryptography.Sphincs.Cost

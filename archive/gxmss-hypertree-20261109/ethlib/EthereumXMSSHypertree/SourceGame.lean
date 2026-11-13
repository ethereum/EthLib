/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.Functional
public import EthereumXMSSHypertree.Representation
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# The deterministic-hash first-request source game

The signer observes source `Except` results through `Except.toOption`. Its verifier checks the
embedded epoch before running the source verifier. The synchronized handler consumes failed
first requests and rejects duplicate epochs before signing. This game does not identify the
EthLib ROM experiment, which executes duplicate requests before its final uniqueness check.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss
open OracleComp OracleSpec SyncSignatureUnforgeability

/-- Source algorithms at fixed deterministic H, with an index-coherent outer epoch. -/
@[expose] def sourceScheme (H : Pure.Hash) :
    SyncSignatureAlg ProbComp Message PublicKey SecretKey Signature Epoch where
  keygen := do
    let raw ← ($ᵗ Seed : ProbComp Seed)
    let ks := (keyGenWith (pureHash H) raw).run
    pure (ks.2, ks.1)
  sign := fun sk e msg =>
    pure (((signWith (pureHash H) sk (leafIndexEquiv.symm e) msg).run).toOption)
  verify := fun pk e msg sig => (verifyAtEpochWith (pureHash H) pk e msg sig).run

/-- The same first-request game expressed through the concrete pure evaluator. -/
@[expose] def pureScheme (H : Pure.Hash) :
    SyncSignatureAlg ProbComp Message PublicKey SecretKey Signature Epoch where
  keygen := do
    let raw ← ($ᵗ Seed : ProbComp Seed)
    let ks := Pure.keys H raw
    pure (ks.2, ks.1)
  sign := fun sk e msg => pure (Pure.sign H sk (leafIndexEquiv.symm e) msg)
  verify := fun pk e msg sig =>
    if leafIndexEquiv sig.leafIndex = e then Pure.verify H pk msg sig else false

/-- The two algorithm records agree on keys, returned failure, and every verification outcome. -/
theorem sourceScheme_eq_pureScheme (H : Pure.Hash) : sourceScheme H = pureScheme H := by
  have hk : (sourceScheme H).keygen = (pureScheme H).keygen := by
    change (do
      let raw ← ($ᵗ Seed : ProbComp Seed)
      let ks := (keyGenWith (pureHash H) raw).run
      pure (ks.2, ks.1)) = _
    apply bind_congr
    intro raw
    rw [keyGenWith_run]
  have hs : (sourceScheme H).sign = (pureScheme H).sign := by
    funext sk e msg
    exact congrArg pure (signWith_toOption H sk (leafIndexEquiv.symm e) msg)
  have hv : (sourceScheme H).verify = (pureScheme H).verify := by
    funext pk e msg sig
    by_cases h : leafIndexEquiv sig.leafIndex = e
    · simp [sourceScheme, pureScheme, verifyAtEpochWith, h, verifyWith_run]
    · simp [sourceScheme, pureScheme, verifyAtEpochWith, h]
  cases hfirst : sourceScheme H
  cases hsecond : pureScheme H
  simp only [hfirst, hsecond] at hk hs hv
  cases hk
  cases hs
  cases hv
  rfl

/-- An index mismatch rejects even when a source signature is otherwise valid. -/
theorem sourceScheme_verify_mismatch (H : Pure.Hash) (pk : PublicKey) (e : Epoch)
    (msg : Message) (sig : Signature) (mismatch : leafIndexEquiv sig.leafIndex ≠ e) :
    (sourceScheme H).verify pk e msg sig = false := by
  simp [sourceScheme, verifyAtEpochWith, mismatch]

/-- The source scheme's optional signing answer is the explicit source returned-failure map. -/
theorem sourceScheme_sign (H : Pure.Hash) (sk : SecretKey) (e : Epoch) (msg : Message) :
    (sourceScheme H).sign sk e msg =
      pure (((signWith (pureHash H) sk (leafIndexEquiv.symm e) msg).run).toOption) := rfl

/-- Failed eligible source requests still consume their epoch in the synchronized history. -/
theorem sourceSigningOracle_failed (H : Pure.Hash) (sk : SecretKey)
    (history : History Epoch Message Signature) (e : Epoch) (msg : Message)
    (unused : history e = none)
    (failed : ((signWith (pureHash H) sk (leafIndexEquiv.symm e) msg).run).toOption = none) :
    signingOracle (sourceScheme H) sk (e, msg) history =
      pure (none, Function.update history e (some (msg, none))) := by
  rw [signingOracle_unused _ _ _ _ _ unused]
  simp only [sourceScheme, failed, pure_bind]
  rfl

/-- Repeated source requests return failure without running the source signer again. -/
theorem sourceSigningOracle_duplicate (H : Pure.Hash) (sk : SecretKey)
    (history : History Epoch Message Signature) (e : Epoch) (msg first : Message)
    (answer : Option Signature) (used : history e = some (first, answer)) :
    signingOracle (sourceScheme H) sk (e, msg) history = pure (none, history) :=
  signingOracle_used _ _ _ _ _ _ _ used

/-- The complete first-request strong game, preserving both returned Booleans and missing mass. -/
@[expose] noncomputable def sourceStrongGame (H : Pure.Hash)
    (adv : Adversary unifSpec PublicKey Epoch Message Signature) : MeasureTheory.Measure Bool :=
  strongUnforgeableExp (sourceScheme H) ProbCompRuntime.probComp adv

/-- Whole returned-output measures agree with the pure source first-request game. -/
theorem sourceStrongGame_eq_pure (H : Pure.Hash)
    (adv : Adversary unifSpec PublicKey Epoch Message Signature) :
    sourceStrongGame H adv =
      strongUnforgeableExp (pureScheme H) ProbCompRuntime.probComp adv := by
  rw [sourceStrongGame, sourceScheme_eq_pureScheme]

/-- Strong freshness is exactly source message/signature-pair freshness at its outer epoch. -/
theorem sourceStrongFresh_iff (history : History Epoch Message Signature)
    (e : Epoch) (msg : Message) (sig : Signature) :
    strongFresh history (e, msg, sig) = true ↔ history e ≠ some (msg, some sig) := by
  simp [strongFresh]

end EthereumXMSSHypertree

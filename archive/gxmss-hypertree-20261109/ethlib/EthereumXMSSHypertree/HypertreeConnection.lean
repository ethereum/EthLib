/-
Copyright (c) 2026 Matthias Meijers.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.HypertreeSourceGame
public import EthereumXMSSHypertree.HypertreeRecovery
public import EthereumXMSSHypertree.HypertreeSigning
public import EthereumXMSSHypertree.HypertreeGameTransport

/-!
# Source observations of the concrete reviewed hypertree

These equations bind the actual generic algorithms to source computation at a fixed deterministic
hash. The full source-signature interface retains its embedded index guard and returned failures.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss ConcreteHypertree HypertreeStrategies

/-- The generic source-signature wrapper has exactly the guarded source verification result. -/
theorem source_verify_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (pk : PublicKey)
    (ep : Epoch) (msg : Message) (sig : Signature) :
    (hypertreeSourceScheme H seedGen).verify pk ep msg sig =
      (verifyAtEpochWith (pureHash H) pk ep msg sig).run := by
  by_cases coherent : leafIndexEquiv sig.leafIndex = ep
  · rw [verifyAtEpochWith_eq _ _ _ _ _ coherent, verifyWith_run]
    simp only [hypertreeSourceScheme, concreteHypertreeScheme,
      GXMSS.Hypertree.PRFDerived.scheme, ite_eq_left coherent]
    have hv := HypertreeCorrespondence.source_verify_eq H seedGen pk msg sig
    simpa only [sourceEpoch, coherent] using hv
  · rw [hypertreeSourceScheme_verify_mismatch H seedGen pk ep msg sig coherent,
      verifyAtEpochWith_mismatch _ _ _ _ _ coherent]
    rfl

/-- The wrapper and source first-request schemes use exactly the same all-input verifier. -/
theorem hypertreeSourceScheme_verify_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) :
    (hypertreeSourceScheme H seedGen).verify = (sourceScheme H).verify := by
  funext pk ep msg sig
  exact source_verify_eq H seedGen pk ep msg sig

/-- The actual generic wrapper has exactly the selected source returned-failure signing result. -/
theorem source_sign_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (sk : SecretKey)
    (ep : Epoch) (msg : Message) :
    (hypertreeSourceScheme H seedGen).sign sk ep msg =
      pure (((signWith (pureHash H) sk (leafIndexEquiv.symm ep) msg).run).toOption) := by
  cases sk with
  | mk raw =>
    have hs := HypertreeSigning.source_sign_eq H seedGen raw (leafIndexEquiv.symm ep) msg
    simp only [sourceEpoch, Equiv.apply_symm_apply] at hs
    simp only [hypertreeSourceScheme, concreteHypertreeScheme,
      GXMSS.Hypertree.PRFDerived.scheme, HypertreePRF.sourcePRF]
    rw [hs, map_pure, signWith_toOption]
    exact congrArg pure (source_sign_reconstruction H ⟨raw⟩ ep msg)

/-- Every algorithm field of the concrete generic wrapper is the corresponding source field. -/
theorem hypertreeSourceScheme_eq_sourceScheme (H : Pure.Hash) (seedGen : ProbComp PublicParam) :
    hypertreeSourceScheme H seedGen = sourceScheme H := by
  have hk := hypertreeSourceScheme_keygen_eq H seedGen
  have hs : (hypertreeSourceScheme H seedGen).sign = (sourceScheme H).sign := by
    funext sk ep msg
    exact source_sign_eq H seedGen sk ep msg
  have hv := hypertreeSourceScheme_verify_eq H seedGen
  cases hg : hypertreeSourceScheme H seedGen
  cases hsour : sourceScheme H
  simp only [hg, hsour] at hk hs hv
  cases hk
  cases hs
  cases hv
  rfl

/-- The complete source first-request game equals the guarded generic wrapper's Boolean measure. -/
theorem sourceStrongGame_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec PublicKey Epoch Message Signature) :
    sourceStrongGame H adv = hypertreeSourceStrongGame H seedGen adv := by
  unfold sourceStrongGame hypertreeSourceStrongGame
  rw [hypertreeSourceScheme_eq_sourceScheme]

/-- Source winning mass is bounded by the actual generic game under the explicit adversary lift. -/
theorem sourceStrongGame_le_generic (H : Pure.Hash) (seedGen : ProbComp PublicParam)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec PublicKey Epoch Message Signature) :
    sourceStrongGame H adv {true} ≤
      SyncSignatureUnforgeability.strongUnforgeableExp (concreteHypertreeScheme H seedGen)
        ProbCompRuntime.probComp (HypertreeGameTransport.liftedAdversary adv) {true} := by
  rw [sourceStrongGame_eq H seedGen adv]
  exact HypertreeGameTransport.strong_success_mass_le H seedGen adv

end EthereumXMSSHypertree

module

public import EthLib.Consensus.KeymanagerApi.VoluntaryExit
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Base.Proofs.Uint64
public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: signing a voluntary exit through the Keymanager API

A key whose public key is that of its secret key signs exits that the chain accepts.

The signature verifies, under the key of the validator, against the signing root of the exit.

That root is under the domain of a voluntary exit in the state of the call.

From Deneb the domain depends only on the genesis validators root.

So the signature also verifies in every state of the same chain at a fork from Deneb on.

That state must keep the key of the validator at the index of the exit.
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-- A validator index that a key reads names a validator of the state that holds that key. -/
theorem getValidator_of_validatorIndexOfPubkey {state : BeaconState preset fork}
    {pubkey : BLSPubkey} {index : ValidatorIndex}
    (found : validatorIndexOfPubkey state pubkey = .ok index) :
    ∃ validator, getValidator state index = .ok validator ∧ validator.pubkey = pubkey := by
  unfold validatorIndexOfPubkey at found
  split at found
  · rename_i position located
    simp only [liftAccessor_ok, liftArith, mapError_ok_iff] at found
    obtain ⟨there, keyed⟩ := Array.findIdx?_eq_some_iff_getElem.mp located
    have named := (Uint64.ofNatChecked_ok_iff.mp found).2
    refine ⟨state.validators.data[position], ?_, beq_iff_eq.mp keyed.1⟩
    simp [getValidator, named, Array.getElem?_eq_getElem there]
  · cases found

/-- The domain of a voluntary exit from Deneb: that of the Capella fork version and the chain. -/
theorem voluntaryExitDomain_of_dencun_le {config : Config} {state : BeaconState preset fork}
    (deneb : .dencun ≤ fork) (epoch : Epoch) :
    voluntaryExitDomain config state epoch = liftSsz (computeDomain config DOMAIN_VOLUNTARY_EXIT
      config.CAPELLA_FORK_VERSION state.genesisValidatorsRoot) := by
  simp [voluntaryExitDomain, deneb]

variable {config : Config} {state : BeaconState preset fork} {keys : KeyState}
  {pubkey : BLSPubkey} {epoch : Option Epoch} {signed : SignedVoluntaryExit}

/-- A key held under a public key has that public key. -/
theorem pubkey_of_localKey? {key : LocalKey} (found : keys.localKey? pubkey = some key) :
    key ∈ keys.localKeys ∧ key.pubkey = pubkey := by
  obtain ⟨keyed, member⟩ := List.find?_some found, List.mem_of_find?_eq_some found
  exact ⟨member, by simpa using keyed⟩

/-- A signed exit is a signature, by the key of the validator, of the signing root of the exit.

The root is under the domain of a voluntary exit in the state, at the epoch of the exit.

So the signature check of the processing of a voluntary exit passes, in that state. -/
theorem verify_of_signVoluntaryExit
    (keyed : ∀ key ∈ keys.localKeys, key.pubkey = Signatures.skToPk key.secretKey)
    (call : signVoluntaryExit config state keys pubkey epoch = .ok signed) :
    ∃ validator domain root, getValidator state signed.message.validatorIndex = .ok validator ∧
      voluntaryExitDomain config state signed.message.epoch = .ok domain ∧
      computeSigningRoot signed.message domain = .ok root ∧
      Signatures.verify validator.pubkey (packBytes root) signed.signature = true := by
  unfold signVoluntaryExit at call
  split at call
  · rename_i key found
    obtain ⟨member, same⟩ := pubkey_of_localKey? found
    split at call
    · rename_i index indexed
      obtain ⟨validator, validated, holds⟩ := getValidator_of_validatorIndexOfPubkey indexed
      dsimp only at call
      split at call
      · rename_i domain domained
        split at call
        · rename_i root rooted
          split at call
          · rename_i signature signs
            simp only [pure, Except.pure, Except.ok.injEq] at call
            subst call
            obtain ⟨signature', signs', verifies⟩ := Signatures.verify_sign key.secretKey
              (packBytes root)
            rw [signs', Except.ok.injEq] at signs
            subst signs
            refine ⟨validator, domain, root, validated, domained, rooted, ?_⟩
            rw [holds, ← same, keyed key member]
            exact verifies
          · simp [throw, throwThe, MonadExceptOf.throw] at call
        · simp [throw, throwThe, MonadExceptOf.throw] at call
      · simp [throw, throwThe, MonadExceptOf.throw] at call
    · simp [throw, throwThe, MonadExceptOf.throw] at call
  · simp [throw, throwThe, MonadExceptOf.throw] at call

/-- From Deneb, a signed exit verifies in every state of the same chain and configuration.

That state may be at any fork from Deneb on.

Its validator at the index of the exit must keep the key, an assumption about the chain. -/
theorem verify_of_signVoluntaryExit_of_dencun_le
    (keyed : ∀ key ∈ keys.localKeys, key.pubkey = Signatures.skToPk key.secretKey)
    (call : signVoluntaryExit config state keys pubkey epoch = .ok signed)
    (deneb : .dencun ≤ fork) {preset' : Preset} {fork' : Fork} (later : BeaconState preset' fork')
    (deneb' : .dencun ≤ fork')
    (sameChain : later.genesisValidatorsRoot = state.genesisValidatorsRoot)
    (registry : ∀ validator, getValidator state signed.message.validatorIndex = .ok validator →
      ∃ validator', getValidator later signed.message.validatorIndex = .ok validator' ∧
        validator'.pubkey = validator.pubkey) :
    ∃ validator domain root, getValidator later signed.message.validatorIndex = .ok validator ∧
      voluntaryExitDomain config later signed.message.epoch = .ok domain ∧
      computeSigningRoot signed.message domain = .ok root ∧
      Signatures.verify validator.pubkey (packBytes root) signed.signature = true := by
  obtain ⟨validator, domain, root, validated, domained, rooted, verifies⟩ :=
    verify_of_signVoluntaryExit keyed call
  obtain ⟨validator', validated', kept⟩ := registry validator validated
  refine ⟨validator', domain, root, validated', ?_, rooted, by rw [kept]; exact verifies⟩
  rw [voluntaryExitDomain_of_dencun_le deneb', sameChain,
    ← voluntaryExitDomain_of_dencun_le deneb signed.message.epoch]
  exact domained

end EthLib.Consensus.KeymanagerApi

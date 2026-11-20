module

public import EthLib.Consensus.RemoteSigningApi.Response
public import EthLib.Consensus.Proofs.BeaconApi.Encoding
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic
public import EthLib.Serialization.Proofs.Ssz.Typed.Container

/-!
# Proofs: the responses of a remote signer read back as written

The JSON response to a request to sign is a lawful container, so it reads back as written.

The writer of a list of public keys never fails, and the list reads back as the same keys.
-/

@[expose] public section

namespace EthLib.Consensus.RemoteSigningApi

open Lean Base Serialization.Ssz BeaconApi Cryptography.Bls

instance : LawfulSszType SigningResponse := .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-- The writer never fails on a list of keys. -/
theorem publicKeysJson_total (keys : List BLSPubkey) :
    ∃ document, publicKeysJson keys = .ok document := by
  -- Each key is written on its own, and no key fails.
  have each : ∀ keys : List BLSPubkey, ∃ written, keys.mapM toApiJson = .ok written := by
    intro keys
    induction keys with
    | nil => exact ⟨[], rfl⟩
    | cons key rest ih =>
      obtain ⟨j, hj⟩ := toApiJson_total key
      obtain ⟨js, hjs⟩ := ih
      exact ⟨j :: js, by simp [List.mapM_cons, hj, hjs, bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨written, hw⟩ := each keys
  simp [publicKeysJson, hw, bind, Except.bind, pure, Except.pure]

/-- The reader gives back every list of keys that the writer writes. -/
theorem readPublicKeys_publicKeysJson {keys : List BLSPubkey} {document : Json}
    (wrote : publicKeysJson keys = .ok document) : readPublicKeys document = .ok keys := by
  -- Each key is written on its own, so the list reads back key by key.
  have each : ∀ (keys : List BLSPubkey) (written : List Json),
      keys.mapM toApiJson = .ok written → written.mapM (ofApiJson BLSPubkey) = .ok keys := by
    intro keys
    induction keys with
    | nil => intro written h; simp_all [pure, Except.pure]
    | cons key rest ih =>
      intro written h
      obtain ⟨j, hj⟩ := toApiJson_total key
      obtain ⟨js, hjs⟩ : ∃ js, rest.mapM toApiJson = .ok js := by
        cases hr : rest.mapM toApiJson with
        | error e => simp [List.mapM_cons, hj, hr, bind, Except.bind] at h
        | ok js => exact ⟨js, rfl⟩
      simp only [List.mapM_cons, hj, hjs, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at h
      subst h
      simp [List.mapM_cons, ofApiJson_toApiJson hj, ih js hjs, bind, Except.bind, pure,
        Except.pure]
  cases hk : keys.mapM toApiJson with
  | error e => simp [publicKeysJson, hk, bind, Except.bind] at wrote
  | ok written =>
    simp only [publicKeysJson, hk, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at wrote
    subst wrote
    simpa [readPublicKeys] using each keys written hk

end EthLib.Consensus.RemoteSigningApi

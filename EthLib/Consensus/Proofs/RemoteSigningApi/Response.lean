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
  obtain ⟨written, hw⟩ := mapM_exists_ok fun key (_ : key ∈ keys) => toApiJson_total key
  simp [publicKeysJson, hw, bind, Except.bind, pure, Except.pure]

/-- The reader gives back every list of keys that the writer writes. -/
theorem readPublicKeys_publicKeysJson {keys : List BLSPubkey} {document : Json}
    (wrote : publicKeysJson keys = .ok document) : readPublicKeys document = .ok keys := by
  cases hk : keys.mapM toApiJson with
  | error e => simp [publicKeysJson, hk, bind, Except.bind] at wrote
  | ok written =>
    simp only [publicKeysJson, hk, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at wrote
    subst wrote
    -- Each key is written on its own, so the list reads back key by key.
    obtain ⟨length, each⟩ := mapM_eq_ok_iff.mp hk
    simpa [readPublicKeys] using mapM_eq_ok_iff.mpr
      ⟨length.symm, fun i hi => ofApiJson_toApiJson (each i (length ▸ hi))⟩

end EthLib.Consensus.RemoteSigningApi

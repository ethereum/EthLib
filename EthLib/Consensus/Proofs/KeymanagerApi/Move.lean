module

public import EthLib.Consensus.Proofs.KeymanagerApi.DeleteKeys
public import EthLib.Consensus.Proofs.KeymanagerApi.LocalKeys

/-!
# Proofs: a key moved between two validator clients keeps its slashing protection

A tool moves a key with two calls of the Keymanager API, as the [use case] "Move a key" says.

It deletes the key from the old client, and imports it with the returned data into the new one.

The new client then refuses every block and every vote of the key that the old client refused.

So the move opens no window in which the key can sign a slashable message.

The old client no longer holds the key as a local key.

The statement covers one key and one move, and does not compare the genesis validators root.

The data passes from one call to the other as a value, so the step through JSON text is not covered.

[use case]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/use-cases/README.md#move-a-key
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography Cryptography.Bls

variable {text : JsonText} {limits : Keystore.KdfLimits}
  {old old' new new' : KeyState} {pubkey : BLSPubkey} {response : DeleteKeysResponse}
  {keystore password : String} {key : LocalKey} {statuses : List ImportStatus}

/-- A key that the client holds, and not read-only, is deleted when a request names it alone. -/
theorem data_deleteKeys_singleton (active : old.isActive pubkey = true)
    (notReadonly : old.isReadonly pubkey = false)
    (deleted : deleteKeys old ⟨[pubkey]⟩ = (response, old')) :
    response.data[0]? = some .deleted := by
  rw [getElem?_data_deleteKeys deleted]
  simp [deleteLocalKeys, deleteLocalKey, notReadonly, active, finalStatus]

/-- After a move, the new client accepts a block of the key only if the old client accepted it. -/
theorem checkBlock_of_move {slot : Slot} {root : Root}
    (active : old.isActive pubkey = true) (notReadonly : old.isReadonly pubkey = false)
    (deleted : deleteKeys old ⟨[pubkey]⟩ = (response, old'))
    (imported : importKeystores text limits new
      ⟨[keystore], [password], some (.ok response.slashingProtection)⟩ = .ok (statuses, new'))
    (status : statuses = [.imported])
    (decoded : decodeKeystore text limits keystore password = .ok key) (same : key.pubkey = pubkey)
    (passed : new'.protection.checkBlock pubkey slot root = .ok ()) :
    old.protection.checkBlock pubkey slot root = .ok () := by
  subst same
  have signed := checkBlockSigning_of_importKeystores (i := 0) imported rfl rfl
    (by rw [status]; rfl) rfl decoded passed
  rwa [blocksOf_slashingProtection_deleteKeys deleted (i := 0) rfl
    (data_deleteKeys_singleton active notReadonly deleted) rfl] at signed

/-- After a move, the new client accepts a vote of the key only if the old client accepted it. -/
theorem checkAttestation_of_move {source target : Epoch} {root : Root}
    (active : old.isActive pubkey = true) (notReadonly : old.isReadonly pubkey = false)
    (deleted : deleteKeys old ⟨[pubkey]⟩ = (response, old'))
    (imported : importKeystores text limits new
      ⟨[keystore], [password], some (.ok response.slashingProtection)⟩ = .ok (statuses, new'))
    (status : statuses = [.imported])
    (decoded : decodeKeystore text limits keystore password = .ok key) (same : key.pubkey = pubkey)
    (passed : new'.protection.checkAttestation pubkey source target root = .ok ()) :
    old.protection.checkAttestation pubkey source target root = .ok () := by
  subst same
  have signed := checkAttestationSigning_of_importKeystores (i := 0) imported rfl rfl
    (by rw [status]; rfl) rfl decoded passed
  rwa [attestationsOf_slashingProtection_deleteKeys deleted (i := 0) rfl
    (data_deleteKeys_singleton active notReadonly deleted) rfl] at signed

/-- After a move, the old client no longer holds the key. -/
theorem isActive_of_move (notReadonly : old.isReadonly pubkey = false)
    (deleted : deleteKeys old ⟨[pubkey]⟩ = (response, old')) :
    old'.isActive pubkey = false := by
  cases active : old'.isActive pubkey
  · rfl
  · have := isReadonly_of_isActive_deleteKeys deleted (List.mem_singleton_self pubkey) active
    rw [notReadonly] at this
    cases this

end EthLib.Consensus.KeymanagerApi

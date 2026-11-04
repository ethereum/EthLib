module

public import EthLib.Consensus.Containers.Misc
public import EthLib.Serialization.Ssz.Typed.Collections

/-!
# `Consensus.PqKeys.Containers`

The types, constants and containers of the post-quantum key registry.

A validator registers a leanXMSS public key and the root of a VRF tree.

A builder registers only a leanXMSS public key.

The keys stay unused until a later fork moves duties to them.

[EIP-8450][eip-8450] defines them in "Constants", "Preset", "Custom types" and "Containers".

The EIP is a Draft at that commit, and no fork includes it yet.

So nothing here depends on a fork.

[eip-8450]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8450.md
-/

@[expose] public section

namespace EthLib.Consensus.PqKeys

open Base Cryptography.Bls Serialization.Ssz

/-- A leanXMSS public key, as 32 bytes. -/
abbrev XMSSPublicKey := Vector UInt8 32

/-- A leanXMSS signature, as 2404 bytes. -/
abbrev XMSSSignature := Vector UInt8 2404

/-- The root of a VRF tree. -/
abbrev VRFRoot := Bytes32

/-- The domain type of the BLS signature that authorizes a registration. -/
def DOMAIN_PQ_KEY_REGISTRATION : DomainType := #v[0x12, 0x00, 0x00, 0x00]

/-- The domain type of a proof of possession, signed with the registered leanXMSS key. -/
def DOMAIN_PQ_KEY_POSSESSION : DomainType := #v[0x13, 0x00, 0x00, 0x00]

/-- The leaf index at which a proof of possession is signed. -/
def PQ_POSSESSION_XMSS_INDEX : UInt32 := 0

/-- The values of the registry that a preset fixes. -/
structure PqKeyPreset where
  /-- The most registrations in one beacon block. -/
  MAX_PQ_KEY_REGISTRATIONS : UInt64
  /-- The fewest epochs between two changes of the keys of one index. -/
  MIN_PQ_KEY_CHANGE_DELAY : Epoch
  deriving DecidableEq, Repr

namespace PqKeyPreset

/-- The mainnet values: 8 registrations per block, and 256 epochs between changes. -/
def mainnet : PqKeyPreset where
  MAX_PQ_KEY_REGISTRATIONS := 2 ^ 3
  MIN_PQ_KEY_CHANGE_DELAY := 2 ^ 8

/-- The minimal values: 8 registrations per block, and 8 epochs between changes. -/
def minimal : PqKeyPreset := { mainnet with MIN_PQ_KEY_CHANGE_DELAY := 2 ^ 3 }

end PqKeyPreset

/-- The post-quantum keys of one validator or builder. -/
structure PQKeyMaterial where
  /-- The leanXMSS public key. -/
  xmssPublicKey : XMSSPublicKey
  /-- The root of the VRF tree, or zero for a builder. -/
  vrfRoot : VRFRoot
  deriving DecidableEq, Repr

instance : SszType PQKeyMaterial :=
  .container ["xmss_public_key", "vrf_root"] (fun k => (k.xmssPublicKey, k.vrfRoot))
    (fun (xmssPublicKey, vrfRoot) => ⟨xmssPublicKey, vrfRoot⟩)

/-- The message of a registration: the registrant, its new keys, and the change it follows. -/
structure PQKeyRegistration where
  /-- The validator index, or the builder index with the builder flag set. -/
  index : ValidatorIndex
  /-- The keys to register. -/
  keyMaterial : PQKeyMaterial
  /-- The epoch of the last change of the keys of the index.

  An index that never registered keys has a marker instead.

  The marker is the far future epoch for a validator, and the deposit epoch for a builder. -/
  previousChangeEpoch : Epoch
  deriving DecidableEq, Repr

instance : SszType PQKeyRegistration :=
  .container ["index", "key_material", "previous_change_epoch"]
    (fun r => (r.index, r.keyMaterial, r.previousChangeEpoch))
    (fun (index, keyMaterial, previousChangeEpoch) => ⟨index, keyMaterial, previousChangeEpoch⟩)

/-- The message of a proof of possession: the BLS key of the registrant, and the leanXMSS key. -/
structure PQKeyPossession where
  /-- The BLS public key of the registrant. -/
  pubkey : BLSPubkey
  /-- The leanXMSS public key whose possession the proof shows. -/
  xmssPublicKey : XMSSPublicKey
  deriving DecidableEq, Repr

instance : SszType PQKeyPossession :=
  .container ["pubkey", "xmss_public_key"] (fun p => (p.pubkey, p.xmssPublicKey))
    (fun (pubkey, xmssPublicKey) => ⟨pubkey, xmssPublicKey⟩)

/-- A registration as a beacon block carries it. -/
structure SignedPQKeyRegistration where
  /-- The registration. -/
  message : PQKeyRegistration
  /-- The leanXMSS signature of the proof of possession, at leaf index 0. -/
  possession : XMSSSignature
  /-- The BLS signature of the registration by the signing key of the registrant. -/
  signature : BLSSignature
  deriving DecidableEq, Repr

instance : SszType SignedPQKeyRegistration :=
  .container ["message", "possession", "signature"]
    (fun s => (s.message, s.possession, s.signature))
    (fun (message, possession, signature) => ⟨message, possession, signature⟩)

/-- The keys of each validator, by validator index.

A validator without keys holds the all-zero entry. -/
abbrev ValidatorPQKeyMaterial := ProgressiveList PQKeyMaterial

/-- The epoch of the last change of the keys of each validator, by validator index.

The far future epoch marks a validator that never registered keys. -/
abbrev ValidatorPQKeyChangeEpochs := ProgressiveList Epoch

/-- The keys of each builder, by builder index.

A builder without keys holds the all-zero entry. -/
abbrev BuilderPQKeyMaterial := ProgressiveList PQKeyMaterial

/-- The epoch of the last change of the keys of each builder, by builder index.

The deposit epoch of a builder marks a builder that never registered keys. -/
abbrev BuilderPQKeyChangeEpochs := ProgressiveList Epoch

/-- The registrations in one beacon block. -/
abbrev PQKeyRegistrations := ProgressiveList SignedPQKeyRegistration

end EthLib.Consensus.PqKeys

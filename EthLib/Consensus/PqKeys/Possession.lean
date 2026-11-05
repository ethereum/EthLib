module

public import EthLib.Consensus.PqKeys.Containers
public import EthLib.Consensus.Signing
public import EthLib.Cryptography.Xmss.Serialization

/-!
# `Consensus.PqKeys.Possession`

A proof of possession shows that the holder of a leanXMSS key signed that key for one BLS key.

The signed message names both keys, so a copied leanXMSS key cannot serve another registrant.

The proof is a leanXMSS signature at leaf index 0.

Its domain uses the genesis fork version, so a proof stays valid across forks.

[EIP-8450][eip-8450] defines the check, in its section "Helpers".

[eip-8450]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8450.md#helpers
-/

@[expose] public section

namespace EthLib.Consensus.PqKeys

open Base Cryptography Cryptography.Bls Serialization.Ssz

/-- The leaf index that a leanXMSS signature carries: its first 4 bytes, little-endian. -/
def xmssSignatureIndex (signature : XMSSSignature) : UInt32 :=
  Xmss.decodeLeafIndex (Base.packBytes signature)
    (by simp [Base.packBytes, ByteArray.size, Xmss.Constants.LEAF_INDEX_SIZE])

/-- The root that a proof of possession signs, on the chain with the given genesis validators.

It is the signing root of the message that names both keys.

Its domain is that of a proof of possession at the genesis fork version. -/
def possessionSigningRoot (config : Config) (genesisValidatorsRoot : Root) (pubkey : BLSPubkey)
    (xmssPublicKey : XMSSPublicKey) : Except Err Root := do
  let domain ← computeDomain config DOMAIN_PQ_KEY_POSSESSION config.GENESIS_FORK_VERSION
    genesisValidatorsRoot
  computeSigningRoot (PQKeyPossession.mk pubkey xmssPublicKey) domain

/-- Whether a proof of possession of a leanXMSS key for a BLS key is valid, over a hash `H`.

The proof must carry leaf index 0, and must sign the possession root under the leanXMSS key.

A key or a proof that does not decode is invalid, without an error. -/
def isValidPqPossessionProofWith {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))
    (config : Config) (genesisValidatorsRoot : Root) (pubkey : BLSPubkey)
    (xmssPublicKey : XMSSPublicKey) (proof : XMSSSignature) : m Bool := do
  if xmssSignatureIndex proof ≠ PQ_POSSESSION_XMSS_INDEX then
    return false
  let .ok message := possessionSigningRoot config genesisValidatorsRoot pubkey xmssPublicKey
    | return false
  let .ok key := Xmss.decodePublicKey (Base.packBytes xmssPublicKey) | return false
  let .ok signature := Xmss.decodeSignature (Base.packBytes proof) | return false
  Xmss.verifyWith H key message signature

/-- Whether a proof of possession of a leanXMSS key for a BLS key is valid, with Keccak-256. -/
def isValidPqPossessionProof (config : Config) (genesisValidatorsRoot : Root) (pubkey : BLSPubkey)
    (xmssPublicKey : XMSSPublicKey) (proof : XMSSSignature) : Bool :=
  (isValidPqPossessionProofWith Xmss.hashId config genesisValidatorsRoot pubkey xmssPublicKey
    proof).run

end EthLib.Consensus.PqKeys

module

public import EthLib.Base.LittleEndian
public import EthLib.Consensus.Containers.Signing
public import EthLib.Consensus.ForkSchedule
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Serialization.Ssz.Typed.Class

/-!
# `Consensus.Signing`

A validator signs the root of an object together with a domain.

The domain names the kind of message, the fork version and the chain.

So a signature for one kind, fork or chain is not valid for another.

Peers name a fork and a chain with a shorter fork digest of four bytes.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz SszType

/-- The root of a fork version on the chain with the given validators at genesis. -/
def computeForkDataRoot (currentVersion : Version) (genesisValidatorsRoot : Root) :
    Except Err Root :=
  hashTreeRoot (ForkData.mk currentVersion genesisValidatorsRoot)

/-- The domain of a kind of message at a fork version, on a chain.

Its four first bytes are the domain type, and its last 28 bytes start the root of the fork data.

Without a version, the version of genesis applies.

Without the root of the genesis validators, 32 zero bytes stand for it. -/
def computeDomain (config : Config) (domainType : DomainType)
    (forkVersion : Version := config.GENESIS_FORK_VERSION)
    (genesisValidatorsRoot : Root := Vector.replicate 32 0) : Except Err Domain := do
  let forkDataRoot ← computeForkDataRoot forkVersion genesisValidatorsRoot
  return Vector.ofFn fun i =>
    if h : i.val < 4 then domainType[i.val] else forkDataRoot[i.val - 4]

/-- The root that a validator signs: that of the object's root with the domain. -/
def computeSigningRoot {α : Type} [SszType α] (object : α) (domain : Domain) : Except Err Root := do
  hashTreeRoot (SigningData.mk (← hashTreeRoot object) domain)

/-- The digest of the fork at an epoch, on the chain with the given validators at genesis.

Before Fulu, it is the first four bytes of the root of the fork data.

From Fulu on, those bytes are XORed with the SHA-256 hash of the blob parameters.

So a change of the blob limit alone changes the digest that peers compare.

The hash reads the first epoch of the parameters, then their blob limit.

Each is an 8-byte little-endian integer.

[EIP-7892](https://eips.ethereum.org/EIPS/eip-7892#modified-compute_fork_digest) adds the mask.

Its text masks with the 4-byte big-endian blob limit alone.

This rule also hashes the first epoch, so entries with one limit still differ by their epoch.

The Fulu networks, mainnet among them, compute the digest with this hash. -/
def computeForkDigest (config : Config) (genesisValidatorsRoot : Root) (epoch : Epoch) :
    Except Err ForkDigest := do
  let base ← computeForkDataRoot (config.computeForkVersion epoch) genesisValidatorsRoot
  if epoch < config.FULU_FORK_EPOCH then
    return Vector.ofFn fun i => base[i.val]
  let parameters := config.getBlobParameters epoch
  let mask := Cryptography.Hash.Sha256.hash32
    ⟨(uintToBytes 8 parameters.epoch.toNat).toArray ++
      (uintToBytes 8 parameters.maxBlobsPerBlock.toNat).toArray⟩
  return Vector.ofFn fun i => base[i.val] ^^^ mask[i.val]

end EthLib.Consensus

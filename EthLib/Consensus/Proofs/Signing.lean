module

public import EthLib.Consensus.Proofs.Containers.Signing
public import EthLib.Consensus.Signing
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
import EthLib.Serialization.Proofs.Ssz.Codec.Summary
import EthLib.Serialization.Proofs.Ssz.Codec.RootDomain

/-!
# Proofs: domains, signing roots and fork digests

Each of them exists for every input, since the roots they hash always exist.

A domain starts with its domain type, so two domain types never share a domain.

Before Fulu, a fork digest is the first four bytes of the root of the fork data.

A signing root is also the root of the signing data whose first field holds the object itself.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz SszType

/-- Every fork version on every chain has a root of its fork data. -/
theorem computeForkDataRoot_total (currentVersion : Version) (genesisValidatorsRoot : Root) :
    ∃ root, computeForkDataRoot currentVersion genesisValidatorsRoot = .ok root :=
  hashTreeRoot_total _

/-- The domain is the domain type, then the first 28 bytes of the root of the fork data. -/
theorem computeDomain_eq {config : Config} {domainType : DomainType} {forkVersion : Version}
    {genesisValidatorsRoot forkDataRoot : Root}
    (rooted : computeForkDataRoot forkVersion genesisValidatorsRoot = .ok forkDataRoot) :
    computeDomain config domainType forkVersion genesisValidatorsRoot =
      .ok (Vector.ofFn fun i =>
        if h : i.val < 4 then domainType[i.val] else forkDataRoot[i.val - 4]) := by
  simp only [computeDomain, rooted, bind, Except.bind, pure, Except.pure]

/-- Every domain type, fork version and chain has a domain. -/
theorem computeDomain_total (config : Config) (domainType : DomainType) (forkVersion : Version)
    (genesisValidatorsRoot : Root) :
    ∃ domain, computeDomain config domainType forkVersion genesisValidatorsRoot = .ok domain := by
  obtain ⟨root, rooted⟩ := computeForkDataRoot_total forkVersion genesisValidatorsRoot
  exact ⟨_, computeDomain_eq rooted⟩

/-- The first four bytes of a domain are its domain type. -/
theorem computeDomain_prefix {config : Config} {domainType : DomainType} {forkVersion : Version}
    {genesisValidatorsRoot : Root} {domain : Domain}
    (computed : computeDomain config domainType forkVersion genesisValidatorsRoot = .ok domain)
    (i : Nat) (lt : i < 4) : domain[i] = domainType[i] := by
  obtain ⟨root, rooted⟩ := computeForkDataRoot_total forkVersion genesisValidatorsRoot
  rw [computeDomain_eq rooted, Except.ok.injEq] at computed
  subst computed
  simp [lt]

/-- Two domain types never share a domain, whatever the fork versions and chains. -/
theorem computeDomain_ne {config : Config} {first second : DomainType}
    {firstVersion secondVersion : Version} {firstRoot secondRoot : Root}
    {firstDomain secondDomain : Domain}
    (differ : first ≠ second)
    (firstComputed : computeDomain config first firstVersion firstRoot = .ok firstDomain)
    (secondComputed : computeDomain config second secondVersion secondRoot = .ok secondDomain) :
    firstDomain ≠ secondDomain := by
  intro same
  apply differ
  ext i lt
  rw [← computeDomain_prefix firstComputed i lt, ← computeDomain_prefix secondComputed i lt, same]

/-- Every object of a lawful SSZ type has a signing root under every domain. -/
theorem computeSigningRoot_total {α : Type} [SszType α] [LawfulSszType α] (object : α)
    (domain : Domain) : ∃ root, computeSigningRoot object domain = .ok root := by
  obtain ⟨objectRoot, rooted⟩ := hashTreeRoot_total object
  obtain ⟨root, signed⟩ := hashTreeRoot_total (SigningData.mk objectRoot domain)
  exact ⟨root, by simp [computeSigningRoot, rooted, signed, bind, Except.bind]⟩

/-- The type of the signing data with an object of the given type in place of its root. -/
def signingShape (shape : Desc) : Desc :=
  .container ["object_root", "domain"] [shape, .byteVector bytesPerChunk]

/-- The signing data with the object in place of its root. -/
def signingValue (value : Value) (domain : Domain) : Value :=
  .seq [value, .bytes domain.toArray]

/-- The signing root of an object is the root of one value.

That value is the signing data with the object in place of its root.

The root is cut to one 32-byte node, as every typed root is.

It needs the type of the object to be lawful. -/
theorem computeSigningRoot_eq_hashTreeRoot {α : Type} [SszType α] [LawfulSszType α]
    (object : α) (domain : Domain) :
    computeSigningRoot object domain = (do
      toChunk (← Serialization.Ssz.hashTreeRoot (signingShape (desc α))
        (signingValue (toValue object) domain))) := by
  obtain ⟨root, rooted, width⟩ := Serialization.Ssz.hashTreeRoot_total (desc α)
    (toValue object) LawfulSszType.wellFormed (LawfulSszType.fits object)
  -- A container reads only the root of each field, so the object gives the same root as its root.
  have summary := hashTreeRoot_summary (names := ["object_root", "domain"])
    (fields := [desc α, .byteVector bytesPerChunk])
    (values := [toValue object, .bytes domain.toArray]) (position := 0) rfl rfl rfl rooted
  have objectRooted : SszType.hashTreeRoot object = .ok ⟨root, width⟩ :=
    hashTreeRoot_ok_iff.mpr rooted
  rw [computeSigningRoot, objectRooted]
  show SszType.hashTreeRoot (SigningData.mk ⟨root, width⟩ domain) = _
  rw [SszType.hashTreeRoot_eq]
  exact congrArg (· >>= toChunk) summary

/-- Before Fulu, the fork digest is the first four bytes of the root of the fork data. -/
theorem computeForkDigest_of_lt_fulu {config : Config} {genesisValidatorsRoot root : Root}
    {epoch : Epoch} (beforeFulu : epoch < config.FULU_FORK_EPOCH)
    (rooted : computeForkDataRoot (config.computeForkVersion epoch) genesisValidatorsRoot =
      .ok root) :
    computeForkDigest config genesisValidatorsRoot epoch =
      .ok (Vector.ofFn fun i => root[i.val]) := by
  simp [computeForkDigest, rooted, beforeFulu, bind, Except.bind, pure, Except.pure]

/-- Every chain has a fork digest at every epoch. -/
theorem computeForkDigest_total (config : Config) (genesisValidatorsRoot : Root) (epoch : Epoch) :
    ∃ digest, computeForkDigest config genesisValidatorsRoot epoch = .ok digest := by
  obtain ⟨root, rooted⟩ :=
    computeForkDataRoot_total (config.computeForkVersion epoch) genesisValidatorsRoot
  by_cases beforeFulu : epoch < config.FULU_FORK_EPOCH
  · exact ⟨_, computeForkDigest_of_lt_fulu beforeFulu rooted⟩
  · simp [computeForkDigest, rooted, beforeFulu, bind, Except.bind, pure, Except.pure]

end EthLib.Consensus

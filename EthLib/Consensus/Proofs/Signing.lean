module

public import EthLib.Consensus.Proofs.Containers.Signing
public import EthLib.Consensus.Signing
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
import EthLib.Serialization.Proofs.Ssz.Codec.Summary
import EthLib.Serialization.Proofs.Ssz.Codec.RootDomain
public import EthLib.Serialization.Proofs.Ssz.Codec.ValueMessages
import EthLib.Serialization.Proofs.Ssz.Type.Legality

/-!
# Proofs: domains, signing roots and fork digests

Each of them exists for every input, since the roots they hash always exist.

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
  .seq [value, .bytes ⟨domain.toArray⟩]

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
    (values := [toValue object, .bytes ⟨domain.toArray⟩]) (position := 0) rfl rfl rfl rooted
  have objectRooted : SszType.hashTreeRoot object = .ok ⟨root.data, width⟩ :=
    hashTreeRoot_ok_iff.mpr rooted
  rw [computeSigningRoot, objectRooted]
  show SszType.hashTreeRoot (SigningData.mk ⟨root.data, width⟩ domain) = _
  rw [SszType.hashTreeRoot_eq]
  exact congrArg (· >>= toChunk) summary

/-- The signing type is well formed exactly when the type of the object is. -/
theorem wellFormed_signingShape_iff (shape : Desc) :
    (signingShape shape).wellFormed = .ok () ↔ shape.wellFormed = .ok () := by
  have distinct : ["object_root", "domain"].Nodup := by decide
  rw [signingShape, wellFormed_container_iff]
  cases sound : shape.wellFormed <;>
    simp [sound, distinct, Desc.allWellFormed, Desc.wellFormed, bind, Except.bind]

/-- The signing data fits the signing type exactly when the object fits its type. -/
theorem fits_signingValue_iff {shape : Desc} {value : Value} {domain : Domain} :
    Fits (signingShape shape) (signingValue value domain) ↔ Fits shape value := by
  rw [signingShape, signingValue]
  constructor
  · intro fitted
    cases fitted with
    | container paired each => exact each (shape, value) (by simp)
  · intro fitted
    refine .container rfl fun pair member => ?_
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl
    · exact fitted
    · exact .byteVector (by simp [bytesPerChunk])

/-- Every count of the signing data fits its word exactly when every count of the object does. -/
theorem commitmentSized_signingValue_iff {shape : Desc} {value : Value}
    {domain : Domain} :
    CommitmentSized (signingShape shape) (signingValue value domain) ↔
      CommitmentSized shape value := by
  rw [signingShape, signingValue]
  constructor
  · intro sized
    cases sized with
    | container each => exact each (shape, value) (by simp)
  · intro sized
    refine .container fun pair member => ?_
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl
    · exact sized
    · exact .byteVector _ _

/-- Two signing data values are equal exactly when their objects and domains are. -/
theorem signingValue_inj {first second : Value} {firstDomain secondDomain : Domain} :
    signingValue first firstDomain = signingValue second secondDomain ↔
      first = second ∧ firstDomain = secondDomain := by
  simp [signingValue, Vector.toArray_inj]

/-- Two different pairs of an object and a domain with one signing root have one root of two values.

The two values are the signing data of the pairs, with each object in place of its root.

They differ, and the root of each is the signing root.

It needs the type of the objects to be lawful. -/
theorem signingValues_of_computeSigningRoot_eq {α : Type} [SszType α] [LawfulSszType α]
    {first second : α} {firstDomain secondDomain : Domain} {root : Root}
    (differ : (first, firstDomain) ≠ (second, secondDomain))
    (firstSigned : computeSigningRoot first firstDomain = .ok root)
    (secondSigned : computeSigningRoot second secondDomain = .ok root) :
    signingValue (toValue first) firstDomain ≠ signingValue (toValue second) secondDomain ∧
      Serialization.Ssz.hashTreeRoot (signingShape (desc α))
          (signingValue (toValue first) firstDomain) = .ok ⟨root.toArray⟩ ∧
      Serialization.Ssz.hashTreeRoot (signingShape (desc α))
          (signingValue (toValue second) secondDomain) = .ok ⟨root.toArray⟩ := by
  rw [computeSigningRoot_eq_hashTreeRoot] at firstSigned secondSigned
  -- A signing root is the root of its signing value, cut to one node.
  have rooted : ∀ {value : Value} {domain : Domain},
      (do toChunk (← Serialization.Ssz.hashTreeRoot (signingShape (desc α))
        (signingValue value domain))) = Except.ok root →
      Serialization.Ssz.hashTreeRoot (signingShape (desc α)) (signingValue value domain) =
        .ok ⟨root.toArray⟩ := by
    intro value domain signed
    cases found : Serialization.Ssz.hashTreeRoot (signingShape (desc α))
        (signingValue value domain) with
    | error fault => simp [found, bind, Except.bind] at signed
    | ok bytes =>
      simp only [found, bind, Except.bind] at signed
      rw [toChunk_ok_iff.mp signed]
  refine ⟨fun same => differ ?_, rooted firstSigned, rooted secondSigned⟩
  -- Equal untyped values read back as equal typed values.
  obtain ⟨valued, domained⟩ := signingValue_inj.mp same
  have back := congrArg (ofValue (α := α)) valued
  rw [LawfulSszType.ofValue_toValue, LawfulSszType.ofValue_toValue] at back
  rw [Except.ok.inj back, domained]

/-- The inputs of the binary hashes that the signing root of an object computes in a domain.

They are the messages of the tree of the signing data, with the object in place of its root.

So they hold the messages of the tree of the object too. -/
def signingMessages {α : Type} [SszType α] (object : α) (domain : Domain) : List Bytes :=
  valueMessages (signingShape (desc α)) (signingValue (toValue object) domain)

/-- Two different objects of one type have two different signing roots, or SHA-256 collides.

The collision is between messages of their two signing roots.

The domains may differ.

It needs every variable-size count in both objects to fit its 256-bit word, and a lawful type. -/
theorem computeSigningRoot_ne_or_collision {α : Type} [SszType α] [LawfulSszType α]
    {first second : α}
    {firstDomain secondDomain : Domain} {firstRoot secondRoot : Root}
    (firstSized : CommitmentSized (desc α) (toValue first))
    (secondSized : CommitmentSized (desc α) (toValue second))
    (differ : first ≠ second)
    (firstSigned : computeSigningRoot first firstDomain = .ok firstRoot)
    (secondSigned : computeSigningRoot second secondDomain = .ok secondRoot) :
    firstRoot ≠ secondRoot ∨ ∃ x ∈ signingMessages first firstDomain,
      ∃ y ∈ signingMessages second secondDomain, MessageCollision x y := by
  by_cases same : firstRoot = secondRoot
  · subst same
    -- Equal roots of two different pairs are one root of two different signing values.
    obtain ⟨valuesDiffer, firstRooted, secondRooted⟩ :=
      signingValues_of_computeSigningRoot_eq (fun pairs => differ (Prod.mk.inj pairs).1)
        firstSigned secondSigned
    -- Two values of one type with one root are equal, or two messages of their trees collide.
    rcases hashTreeRoot_binding ((wellFormed_signingShape_iff _).mpr LawfulSszType.wellFormed)
        (fits_signingValue_iff.mpr (LawfulSszType.fits first))
        (fits_signingValue_iff.mpr (LawfulSszType.fits second))
        (commitmentSized_signingValue_iff.mpr firstSized)
        (commitmentSized_signingValue_iff.mpr secondSized) firstRooted secondRooted with
      equal | ⟨firstTree, secondTree, firstOk, secondOk, a, b, -, aMember, bMember, collision⟩
    · exact absurd equal valuesDiffer
    · refine .inr ⟨a, ?_, b, ?_, collision⟩
      · rw [signingMessages, valueMessages_of_valueTree firstOk]
        exact aMember
      · rw [signingMessages, valueMessages_of_valueTree secondOk]
        exact bMember
  · exact .inl same

/-- The inputs of the binary hashes in the root of the signing data of an object root and a domain.

They are those of the tree of the signing data, which holds the object root and the domain. -/
def signingDataMessages (objectRoot : Root) (domain : Domain) : List Bytes :=
  valueMessages (desc SigningData) (toValue (SigningData.mk objectRoot domain))

/-- Every variable-size count of signing data fits its 256-bit word, since it has no list. -/
private theorem signingData_commitmentSized (data : SigningData) :
    CommitmentSized (desc SigningData) (toValue data) := by
  refine .container fun pair member => ?_
  simp [desc, toValue, SszFields.descs, SszFields.toValues] at member
  repeat' rcases member with rfl | member
  all_goals exact .byteVector _ _

/-- Two objects signed in two different domains have different signing roots, or SHA-256 collides.

The objects may be of two types, and the collision is between messages of their signing data. -/
theorem computeSigningRoot_ne_or_collision_of_domain_ne {α β : Type} [SszType α]
    [SszType β] {first : α} {second : β} {firstDomain secondDomain : Domain}
    {firstObjectRoot secondObjectRoot firstRoot secondRoot : Root}
    (differ : firstDomain ≠ secondDomain)
    (firstObject : hashTreeRoot first = .ok firstObjectRoot)
    (secondObject : hashTreeRoot second = .ok secondObjectRoot)
    (firstSigned : computeSigningRoot first firstDomain = .ok firstRoot)
    (secondSigned : computeSigningRoot second secondDomain = .ok secondRoot) :
    firstRoot ≠ secondRoot ∨ ∃ x ∈ signingDataMessages firstObjectRoot firstDomain,
      ∃ y ∈ signingDataMessages secondObjectRoot secondDomain, MessageCollision x y := by
  by_cases same : firstRoot = secondRoot
  · subst same
    -- Each signing root is the root of the signing data of its object root.
    simp only [computeSigningRoot, firstObject, secondObject, bind, Except.bind]
      at firstSigned secondSigned
    -- Two signing data values with one root are equal, or two messages of their trees collide.
    rcases hashTreeRoot_binding (signingData_commitmentSized _) (signingData_commitmentSized _)
        firstSigned secondSigned with
      equal | ⟨firstTree, secondTree, firstOk, secondOk, a, b, -, aMember, bMember, collision⟩
    · exact absurd (SigningData.mk.inj equal).2 differ
    · refine .inr ⟨a, ?_, b, ?_, collision⟩
      · rw [signingDataMessages, valueMessages_of_valueTree firstOk]
        exact aMember
      · rw [signingDataMessages, valueMessages_of_valueTree secondOk]
        exact bMember
  · exact .inl same

/-- Two objects signed under two domain types have two different signing roots, or SHA-256 collides.

Each domain is that of its domain type, of any fork version and of any genesis validators root.

So, unless the node hash collides, no signing root in one domain type is one in another.

For instance, no attestation has the signing root of a deposit. -/
theorem computeSigningRoot_ne_or_collision_of_domainType_ne {config : Config} {α β : Type}
    [SszType α] [SszType β] {first : α} {second : β} {firstType secondType : DomainType}
    {firstVersion secondVersion : Version} {firstGenesis secondGenesis : Root}
    {firstDomain secondDomain : Domain}
    {firstObjectRoot secondObjectRoot firstRoot secondRoot : Root}
    (differ : firstType ≠ secondType)
    (firstDomained :
      computeDomain config firstType firstVersion firstGenesis = .ok firstDomain)
    (secondDomained :
      computeDomain config secondType secondVersion secondGenesis = .ok secondDomain)
    (firstObject : hashTreeRoot first = .ok firstObjectRoot)
    (secondObject : hashTreeRoot second = .ok secondObjectRoot)
    (firstSigned : computeSigningRoot first firstDomain = .ok firstRoot)
    (secondSigned : computeSigningRoot second secondDomain = .ok secondRoot) :
    firstRoot ≠ secondRoot ∨ ∃ x ∈ signingDataMessages firstObjectRoot firstDomain,
      ∃ y ∈ signingDataMessages secondObjectRoot secondDomain, MessageCollision x y :=
  computeSigningRoot_ne_or_collision_of_domain_ne
    (computeDomain_ne differ firstDomained secondDomained) firstObject secondObject firstSigned
    secondSigned

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

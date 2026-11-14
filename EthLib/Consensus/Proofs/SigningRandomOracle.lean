module

public import EthLib.Consensus.Containers.Misc
public import EthLib.Consensus.Signing
public import EthLib.Serialization.Proofs.Ssz.RandomOracle
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
import EthLib.Consensus.Proofs.Containers.Signing
import EthLib.Serialization.Proofs.Ssz.Type.Legality

/-!
# Proofs: a collision of the signing root in the random oracle model

A signing root is the root of the signing data, which holds the root of the object and the domain.

A container reads only the root of each field.

So the signing root is also the root of the signing data with the object in place of its root.

A collision of the signing root is then two different such values with one root.

The two objects have one type, and their two domains may differ.

In the random oracle model of the SSZ root, finding one has probability at most `Q^2 / 2^256`.

`Q` counts every oracle call of the experiment, the adversary's and the extraction's.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz SszType Serialization.Ssz.RandomOracle
open OracleComp OracleSpec ENNReal

/-- The type of the signing data with an object of the given type in place of its root. -/
def signingShape (shape : Desc) : Desc :=
  .container ["object_root", "domain"] [shape, .byteVector bytesPerChunk]

/-- The signing data with the object in place of its root. -/
def signingValue (value : Value) (domain : Domain) : Value :=
  .seq [value, .bytes domain.toArray]

/-- The signing data of two objects, each with its domain. -/
def signingValues (pair : (Value × Domain) × (Value × Domain)) : Value × Value :=
  (signingValue pair.1.1 pair.1.2, signingValue pair.2.1 pair.2.2)

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
  -- The root of the object is its leaf, so the root in its place keeps the root of the container.
  have summary := hashTreeRoot_summary (names := ["object_root", "domain"])
    (fields := [desc α, .byteVector bytesPerChunk])
    (values := [toValue object, .bytes domain.toArray]) (position := 0) rfl rfl rfl rooted
  have objectRooted : SszType.hashTreeRoot object = .ok ⟨root, width⟩ :=
    hashTreeRoot_ok_iff.mpr rooted
  rw [computeSigningRoot, objectRooted]
  show SszType.hashTreeRoot (SigningData.mk ⟨root, width⟩ domain) = _
  rw [SszType.hashTreeRoot_eq]
  exact congrArg (· >>= toChunk) summary

/-- The signing type is well formed exactly when the type of the object is. -/
private theorem wellFormed_signingShape_iff (shape : Desc) :
    (signingShape shape).wellFormed = .ok () ↔ shape.wellFormed = .ok () := by
  have distinct : firstDuplicate ["object_root", "domain"] = none := by decide
  rw [signingShape, wellFormed_container_iff]
  cases sound : shape.wellFormed <;>
    simp [sound, distinct, Desc.allWellFormed, Desc.wellFormed, bind, Except.bind]

/-- The signing data fits the signing type exactly when the object fits its type. -/
private theorem fits_signingValue_iff {shape : Desc} {value : Value} {domain : Domain} :
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
private theorem commitmentSized_signingValue_iff {shape : Desc} {value : Value}
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
private theorem signingValue_inj {first second : Value} {firstDomain secondDomain : Domain} :
    signingValue first firstDomain = signingValue second secondDomain ↔
      first = second ∧ firstDomain = secondDomain := by
  simp [signingValue, Vector.toArray_inj]

/-- A win on the signing data of two objects is a collision of the signing root.

The two objects with their domains differ, and both objects fit one well-formed type.

Every count in them fits its 256-bit word, and the two roots agree. -/
theorem wins_signingValue_iff {shape : Desc} {first second : Value}
    {firstDomain secondDomain : Domain} {firstRoot secondRoot : Except Err Bytes} :
    Wins (signingShape shape)
        ⟨signingValue first firstDomain, signingValue second secondDomain, firstRoot, secondRoot⟩ ↔
      shape.wellFormed = .ok () ∧ Fits shape first ∧ Fits shape second ∧
        CommitmentSized shape first ∧ CommitmentSized shape second ∧
        (first, firstDomain) ≠ (second, secondDomain) ∧
        ∃ root, firstRoot = .ok root ∧ secondRoot = .ok root := by
  simp only [Wins, wellFormed_signingShape_iff, fits_signingValue_iff,
    commitmentSized_signingValue_iff, ne_eq, signingValue_inj, Prod.mk.injEq]

/-- A collision of the signing root, at probability at most `Q^2 / 2^256`.

The adversary outputs two objects of one type, each with a domain, and the domains may differ.

The adversary wins when the two pairs differ, fit the well-formed type, and have one signing root.

Every count in them must fit its 256-bit word.

The bound needs at most `Q` oracle calls in the whole experiment, repeats included.

The experiment runs on the signing data with the object in place of its root. -/
theorem prEvent_signingRoot_le_two_pow (shape : Desc)
    (adversary : OracleComp (unifSpec + HashOracle) ((Value × Domain) × (Value × Domain)))
    {Q : Nat}
    (budget : IsQueryBoundP (experiment (signingShape shape) (signingValues <$> adversary))
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
        (experiment (signingShape shape) (signingValues <$> adversary))).run ∅}[
      Wins (signingShape shape) z.1] ≤ Q * ((Q : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_wins_le_two_pow _ _ budget

/-- Two messages with one signing root win on the values that the bound hashes.

The outcome holds the signing values of the two pairs of a message and a domain, and their roots.

It needs the type of the messages to be lawful, and the two pairs to differ.

It also needs every count in both messages to fit its 256-bit word. -/
theorem wins_of_computeSigningRoot_eq {α : Type} [SszType α] [LawfulSszType α]
    {first second : α} {firstDomain secondDomain : Domain} {root : Root}
    (firstSized : CommitmentSized (desc α) (toValue first))
    (secondSized : CommitmentSized (desc α) (toValue second))
    (differ : (first, firstDomain) ≠ (second, secondDomain))
    (firstSigned : computeSigningRoot first firstDomain = .ok root)
    (secondSigned : computeSigningRoot second secondDomain = .ok root) :
    let values := signingValues ((toValue first, firstDomain), (toValue second, secondDomain))
    Wins (signingShape (desc α)) ⟨values.1, values.2,
      Serialization.Ssz.hashTreeRoot (signingShape (desc α)) values.1,
      Serialization.Ssz.hashTreeRoot (signingShape (desc α)) values.2⟩ := by
  -- The bound reads each pair of the adversary as its signing value.
  show Wins (signingShape (desc α))
    ⟨signingValue (toValue first) firstDomain, signingValue (toValue second) secondDomain,
      Serialization.Ssz.hashTreeRoot (signingShape (desc α))
        (signingValue (toValue first) firstDomain),
      Serialization.Ssz.hashTreeRoot (signingShape (desc α))
        (signingValue (toValue second) secondDomain)⟩
  rw [computeSigningRoot_eq_hashTreeRoot] at firstSigned secondSigned
  -- A signing root is the root of its signing value, cut to one node.
  have rooted : ∀ {value : Value} {domain : Domain},
      (do toChunk (← Serialization.Ssz.hashTreeRoot (signingShape (desc α))
        (signingValue value domain))) = Except.ok root →
      Serialization.Ssz.hashTreeRoot (signingShape (desc α)) (signingValue value domain) =
        .ok root.toArray := by
    intro value domain signed
    cases found : Serialization.Ssz.hashTreeRoot (signingShape (desc α))
        (signingValue value domain) with
    | error fault => simp [found, bind, Except.bind] at signed
    | ok bytes =>
      simp only [found, bind, Except.bind] at signed
      rw [toChunk_ok_iff.mp signed]
  refine wins_signingValue_iff.mpr ⟨LawfulSszType.wellFormed, LawfulSszType.fits first,
    LawfulSszType.fits second, firstSized, secondSized, ?_, root.toArray,
    rooted firstSigned, rooted secondSigned⟩
  -- Equal untyped values read back as equal typed values.
  intro same
  apply differ
  obtain ⟨valued, domained⟩ := Prod.mk.inj same
  have back := congrArg (ofValue (α := α)) valued
  rw [LawfulSszType.ofValue_toValue, LawfulSszType.ofValue_toValue] at back
  rw [Except.ok.inj back, domained]

/-- Every count of a block header fits its word, since the header has no list. -/
theorem commitmentSized_beaconBlockHeader (header : BeaconBlockHeader) :
    CommitmentSized (desc BeaconBlockHeader) (toValue header) := by
  refine .container fun pair member => ?_
  simp [SszType.desc, SszType.toValue, SszFields.descs, SszFields.toValues] at member
  repeat' rcases member with rfl | member
  all_goals first | exact .byteVector _ _ | exact .uint _ _

/-- Every count of a checkpoint fits its word, since the checkpoint has no list. -/
theorem commitmentSized_checkpoint (checkpoint : Checkpoint) :
    CommitmentSized (desc Checkpoint) (toValue checkpoint) := by
  refine .container fun pair member => ?_
  simp [SszType.desc, SszType.toValue, SszFields.descs, SszFields.toValues] at member
  repeat' rcases member with rfl | member
  all_goals first | exact .byteVector _ _ | exact .uint _ _

/-- Every count of a vote fits its word, since the vote has no list. -/
theorem commitmentSized_attestationData (data : AttestationData) :
    CommitmentSized (desc AttestationData) (toValue data) := by
  refine .container fun pair member => ?_
  simp [SszType.desc, SszType.toValue, SszFields.descs, SszFields.toValues] at member
  repeat' rcases member with rfl | member
  all_goals first
    | exact .byteVector _ _
    | exact .uint _ _
    | exact commitmentSized_checkpoint _

end EthLib.Consensus

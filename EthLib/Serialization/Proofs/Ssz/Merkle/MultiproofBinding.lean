module

public import EthLib.Serialization.Proofs.Ssz.Merkle.MultiproofAcceptance
public import EthLib.Cryptography.Proofs.Merkle.Multiproof.Trace

/-! Conflicting multiproof claims expose a SHA-256 collision, found by the Merkle search. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Cryptography.Merkle

/-- The collision two multiproofs run into, if any: the two messages hashed at one node.

The two rebuilds are compared in the tree as deep as the deeper of the two requests. -/
def findMultiproofMessageCollision (leftLeaves leftProof : List Bytes) (leftIndices : List Nat)
    (rightLeaves rightProof : List Bytes) (rightIndices : List Nat) : Option (Bytes × Bytes) :=
  match getHelperIndices leftIndices, getHelperIndices rightIndices with
  | .ok leftHelpers, .ok rightHelpers =>
    let height := max (gindexHeight leftIndices) (gindexHeight rightIndices)
    (Cryptography.Merkle.findMultiproofCollision sszNodeHash
        (multiproofNodes height leftIndices leftHelpers leftLeaves leftProof)
        (multiproofNodes height rightIndices rightHelpers rightLeaves rightProof) height 0).map
      fun c => (c.x.1 ++ c.x.2, c.y.1 ++ c.y.2)
  | _, _ => none

/-- The messages a multiproof verifier hashes: each pair of nodes, joined, as the rebuild runs. -/
def verifiedMultiproofMessages (leaves proof : List Bytes) (indices : List Nat) : List Bytes :=
  match claimPositions indices with
  | .ok (height, opened) =>
    (((rebuild (recordingHash sszNodeHash fun _ a b => a ++ b)
      (opened.zip leaves ++ (helpers height opened).zip proof) height).run []).run).2
  | .error _ => []

/-- A multiproof compared with itself gives no collision, so the search can fail. -/
theorem findMultiproofMessageCollision_self (leaves proof : List Bytes) (indices : List Nat) :
    findMultiproofMessageCollision leaves proof indices leaves proof indices = none := by
  unfold findMultiproofMessageCollision
  split
  · -- Both requests have the same helpers, so the two rebuilds are one.
    rename_i leftHelpers rightHelpers leftBuilt rightBuilt
    rw [leftBuilt] at rightBuilt
    cases rightBuilt
    dsimp only
    rw [Cryptography.Merkle.findMultiproofCollision_self]
    rfl
  · rfl

/-- Moving a multiproof to a tree `k` levels taller lifts every node it gives by `k` levels. -/
theorem multiproofNodes_lift {height : Nat} {indices helpers : List Nat}
    {leaves proof : List Bytes} (deep : ∀ g ∈ indices ++ helpers, Nat.log2 g ≤ height) (k : Nat) :
    multiproofNodes (height + k) indices helpers leaves proof =
      (multiproofNodes height indices helpers leaves proof).map
        fun e => ((⟨e.1.level + k, e.1.index⟩ : Position), e.2) := by
  simp only [multiproofNodes, List.zip_map_left, List.map_map]
  refine List.map_congr_left fun e member => ?_
  obtain ⟨g, v⟩ := e
  simp only [Function.comp_apply, Prod.map, id]
  rw [gindexPosition_lift (deep _ (List.of_mem_zip member).1)]

/-- The facts an accepted multiproof gives, in a tree at least as deep as its own. -/
private structure Accepted (leaves proof : List Bytes) (indices helpers : List Nat)
    (root : Bytes) (height : Nat) : Prop where
  helperIndices : getHelperIndices indices = .ok helpers
  leafCount : leaves.length = indices.length
  proofCount : proof.length = helpers.length
  tall : gindexHeight indices ≤ height
  widths : ∀ e ∈ multiproofNodes height indices helpers leaves proof, e.2.size = bytesPerChunk
  rebuilt : (rebuild.go sszNodeHash (multiproofNodes height indices helpers leaves proof)
    height 0).run = some root
  messages : (((rebuild.go (recordingHash sszNodeHash fun _ a b => a ++ b)
    (multiproofNodes height indices helpers leaves proof) height 0).run []).run).2 =
      verifiedMultiproofMessages leaves proof indices

private theorem accepted_of_verify {leaves proof : List Bytes} {indices : List Nat} {root : Bytes}
    (verified : verifyMerkleMultiproof leaves proof indices root = .ok true) {height : Nat}
    (tall : gindexHeight indices ≤ height) :
    ∃ helpers, Accepted leaves proof indices helpers root height := by
  obtain ⟨leafWidths, proofWidths, built⟩ := (verifyMerkleMultiproof_eq_true_iff ..).mp verified
  obtain ⟨helpers, helperIndices, leafCount, proofCount, rebuilt⟩ :=
    calculateMultiMerkleRootUnchecked_shape built
  have valid := getHelperIndices_valid helperIndices
  -- Lifting the nodes lifts the rebuild, since the SSZ hash ignores positions.
  have lift := multiproofNodes_lift (leaves := leaves) (proof := proof)
    (fun g member => (valid g member).2) (height - gindexHeight indices)
  rw [Nat.add_sub_cancel' tall] at lift
  refine ⟨helpers, helperIndices, leafCount, proofCount, tall, fun e member => ?_, ?_, ?_⟩
  · have := (List.of_mem_zip member).2
    rcases List.mem_append.mp this with leaf | node
    · exact leafWidths _ leaf
    · exact proofWidths _ node
  · rw [lift]
    have := rebuild_go_lift sszNodeHash (height - gindexHeight indices) (fun _ => rfl)
      (multiproofNodes (gindexHeight indices) indices helpers leaves proof) (gindexHeight indices) 0
    rw [Nat.add_sub_cancel' tall] at this
    exact this.trans rebuilt
  · -- The record of the lifted rebuild is the record of the verifier's own rebuild.
    rw [lift]
    have := rebuild_go_lift_monad (recordingHash sszNodeHash fun _ a b => a ++ b)
      (height - gindexHeight indices) (fun _ => rfl) (gindexHeight indices) 0
      (multiproofNodes (gindexHeight indices) indices helpers leaves proof)
    rw [Nat.add_sub_cancel' tall] at this
    rw [this, verifiedMultiproofMessages, claimPositions_ok (getHelperIndices_ok helperIndices).1]
    dsimp only
    rw [← multiproofNodes_eq helperIndices leafCount]
    rfl

/-- An accepted claim is read back from its nodes, with no node given above it, in the tree. -/
private theorem Accepted.claim {leaves proof : List Bytes} {indices helpers : List Nat}
    {root : Bytes} {height : Nat} (valid : Accepted leaves proof indices helpers root height)
    {index : Nat} {value : Bytes} (member : (index, value) ∈ indices.zip leaves) :
    (multiproofNodes height indices helpers leaves proof).lookup
        (gindexPosition height index) = some value ∧
      (∀ e ∈ multiproofNodes height indices helpers leaves proof,
        e.1.IsAncestor (gindexPosition height index) → e.1 = gindexPosition height index) ∧
      InTree height (gindexPosition height index) := by
  have bounds := getHelperIndices_valid valid.helperIndices
  -- All indices of the request lie within the tree.
  have deep : ∀ g ∈ indices ++ helpers, 1 ≤ g ∧ Nat.log2 g ≤ height :=
    fun g hg => ⟨(bounds g hg).1, Nat.le_trans (bounds g hg).2 valid.tall⟩
  have claimedIndex := List.mem_append_left helpers (List.of_mem_zip member).1
  have claimed := deep index claimedIndex
  -- Two valid indices with one position are one index.
  have injective : ∀ a b, 1 ≤ a → Nat.log2 a ≤ height → 1 ≤ b → Nat.log2 b ≤ height →
      gindexPosition height a = gindexPosition height b → a = b := by
    intro a b na da nb db same
    have := congrArg (positionGindex height) same
    rwa [positionGindex_gindexPosition na da, positionGindex_gindexPosition nb db] at this
  refine ⟨?_, ?_, gindexPosition_inTree claimed.1 claimed.2⟩
  · -- The positions repeat no index, so the lookup finds the claimed value.
    apply lookup_of_mem_nodup
    · rw [multiproofNodes, List.map_fst_zip (by simp [valid.leafCount, valid.proofCount])]
      exact List.pairwise_map.mpr ((getHelperIndices_all_nodup valid.helperIndices).imp_of_mem
        fun ha hb distinct same => distinct
          (injective _ _ (deep _ ha).1 (deep _ ha).2 (deep _ hb).1 (deep _ hb).2 same))
    · rw [multiproofNodes, List.zip_map_left]
      refine List.mem_map.mpr ⟨(index, value), ?_, rfl⟩
      rw [List.zip_append (by simp [valid.leafCount])]
      exact List.mem_append_left _ member
  · -- A node given above the claim is the claim shifted, which the antichain makes the claim.
    intro e he above
    rw [multiproofNodes, List.zip_map_left] at he
    obtain ⟨⟨g, v⟩, pair, rfl⟩ := List.mem_map.mp he
    have gMember := (List.of_mem_zip pair).1
    obtain ⟨steps, hsteps⟩ := above
    simp only [Prod.map_fst] at hsteps ⊢
    have levels := congrArg Position.level hsteps
    simp only [gindexPosition, Position.ancestor_level] at levels
    have short : steps ≤ Nat.log2 index := by
      have := (deep g gMember).2
      omega
    rw [gindexPosition_ancestor claimed.1 claimed.2 short] at hsteps
    -- The shifted claim is a valid index too.
    have positive : 1 ≤ index >>> steps := by
      have := shiftRight_le (index >>> steps) (Nat.log2 index - steps)
      rwa [← Nat.shiftRight_add, Nat.add_sub_cancel' short, shiftRight_depth claimed.1] at this
    have shallow : Nat.log2 (index >>> steps) ≤ height :=
      Nat.le_trans (levelOf_mono positive (shiftRight_le index steps)) claimed.2
    have same := injective _ _ (deep g gMember).1 (deep g gMember).2 positive shallow hsteps
    rw [getHelperIndices_antichain valid.helperIndices index claimedIndex g gMember steps same.symm]

/-- The search's two pairs are messages the verifiers hash, and they collide under SHA-256. -/
private theorem collision_of_found {leftLeaves leftProof rightLeaves rightProof : List Bytes}
    {leftIndices rightIndices leftHelpers rightHelpers : List Nat} {leftRoot rightRoot : Bytes}
    {height : Nat}
    (left : Accepted leftLeaves leftProof leftIndices leftHelpers leftRoot height)
    (right : Accepted rightLeaves rightProof rightIndices rightHelpers rightRoot height)
    {c : Collision Bytes}
    (found : Cryptography.Merkle.findMultiproofCollision sszNodeHash
      (multiproofNodes height leftIndices leftHelpers leftLeaves leftProof)
      (multiproofNodes height rightIndices rightHelpers rightLeaves rightProof) height 0 =
        some c) :
    c.x.1 ++ c.x.2 ∈ verifiedMultiproofMessages leftLeaves leftProof leftIndices ∧
      c.y.1 ++ c.y.2 ∈ verifiedMultiproofMessages rightLeaves rightProof rightIndices ∧
      MessageCollision (c.x.1 ++ c.x.2) (c.y.1 ++ c.y.2) := by
  -- Each pair is one its own rebuild records.
  have leftRecorded := findMultiproofCollision_recorded sszNodeHash (fun _ a b => a ++ b) height 0
    _ [] found
  have rightRecorded := findMultiproofCollision_recorded sszNodeHash (fun _ a b => a ++ b) height 0
    _ [] (c := ⟨c.position, c.y, c.x⟩)
    (by rw [findMultiproofCollision_swap, found]; rfl)
  rw [left.messages] at leftRecorded
  rw [right.messages] at rightRecorded
  refine ⟨leftRecorded, rightRecorded, ?_⟩
  obtain ⟨⟨different, joined⟩, -⟩ := findMultiproofCollision_valid sszNodeHash found
  -- Every node the two rebuilds hash has 32 bytes, since a parent is a SHA-256 digest.
  obtain ⟨x1, x2, y1, y2⟩ := findMultiproofCollision_children sszNodeHash
    (fun node => node.size = bytesPerChunk) (fun _ x y => combine_size x y)
    left.widths right.widths found
  refine ⟨by simp [x1, x2, Nat.two_mul], by simp [y1, y2, Nat.two_mul],
    fun equal => different ?_, ?_⟩
  · -- Fixed child widths keep the boundary between the two children in place.
    obtain ⟨h1, h2⟩ := Array.append_inj equal (x1.trans y1.symm)
    exact Prod.ext h1 h2
  · -- The two pairs hash to one parent, which is the digest of their messages.
    exact ByteArray.ext joined

/-- Between accepted multiproofs, the search returns hashed messages that collide under SHA-256. -/
theorem findMultiproofMessageCollision_valid
    {leftLeaves leftProof rightLeaves rightProof : List Bytes} {leftIndices rightIndices : List Nat}
    {leftRoot rightRoot first second : Bytes}
    (leftAccepted : verifyMerkleMultiproof leftLeaves leftProof leftIndices leftRoot = .ok true)
    (rightAccepted :
      verifyMerkleMultiproof rightLeaves rightProof rightIndices rightRoot = .ok true)
    (found : findMultiproofMessageCollision leftLeaves leftProof leftIndices rightLeaves rightProof
      rightIndices = some (first, second)) :
    first ∈ verifiedMultiproofMessages leftLeaves leftProof leftIndices ∧
      second ∈ verifiedMultiproofMessages rightLeaves rightProof rightIndices ∧
      MessageCollision first second := by
  obtain ⟨leftHelpers, left⟩ := accepted_of_verify leftAccepted
    (Nat.le_max_left (gindexHeight leftIndices) (gindexHeight rightIndices))
  obtain ⟨rightHelpers, right⟩ := accepted_of_verify rightAccepted
    (Nat.le_max_right (gindexHeight leftIndices) (gindexHeight rightIndices))
  simp only [findMultiproofMessageCollision, left.helperIndices, right.helperIndices] at found
  obtain ⟨c, hc, pair⟩ := Option.map_eq_some_iff.mp found
  cases pair
  exact collision_of_found left right hc

/-- Two accepted requests for one root agree where they both claim a position.

Otherwise the search over the two rebuilds finds a SHA-256 collision. -/
theorem verifyMerkleMultiproof_overlap_binding
    {leftLeaves leftProof rightLeaves rightProof : List Bytes}
    {leftIndices rightIndices : List Nat} {root firstValue secondValue : Bytes} {index : Nat}
    (leftAccepted : verifyMerkleMultiproof leftLeaves leftProof leftIndices root = .ok true)
    (rightAccepted : verifyMerkleMultiproof rightLeaves rightProof rightIndices root = .ok true)
    (leftClaim : (index, firstValue) ∈ leftIndices.zip leftLeaves)
    (rightClaim : (index, secondValue) ∈ rightIndices.zip rightLeaves) :
    firstValue = secondValue ∨
      ∃ first second, findMultiproofMessageCollision leftLeaves leftProof leftIndices
          rightLeaves rightProof rightIndices = some (first, second) ∧
        first ∈ verifiedMultiproofMessages leftLeaves leftProof leftIndices ∧
        second ∈ verifiedMultiproofMessages rightLeaves rightProof rightIndices ∧
        MessageCollision first second := by
  -- Compare both rebuilds in the tree as deep as the deeper request.
  obtain ⟨leftHelpers, left⟩ := accepted_of_verify leftAccepted
    (Nat.le_max_left (gindexHeight leftIndices) (gindexHeight rightIndices))
  obtain ⟨rightHelpers, right⟩ := accepted_of_verify rightAccepted
    (Nat.le_max_right (gindexHeight leftIndices) (gindexHeight rightIndices))
  obtain ⟨leftAt, leftBelow, inside⟩ := left.claim leftClaim
  obtain ⟨rightAt, rightBelow, -⟩ := right.claim rightClaim
  rcases rebuild_go_binding sszNodeHash leftAt rightAt leftBelow rightBelow _ 0 root inside
      left.rebuilt right.rebuilt with same | found
  · exact .inl same
  · -- The Merkle search succeeds, and the SSZ search returns its two messages.
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp found
    refine .inr ⟨_, _, ?_, collision_of_found left right hc⟩
    simp only [findMultiproofMessageCollision, left.helperIndices, right.helperIndices, hc,
      Option.map_some]

/-- Two accepted multiproofs for the same positions bind every claimed value.

Otherwise the search over the two rebuilds finds a SHA-256 collision. -/
theorem verifyMerkleMultiproof_binding {leftLeaves leftProof rightLeaves rightProof : List Bytes}
    {indices : List Nat} {root : Bytes}
    (leftAccepted : verifyMerkleMultiproof leftLeaves leftProof indices root = .ok true)
    (rightAccepted : verifyMerkleMultiproof rightLeaves rightProof indices root = .ok true) :
    leftLeaves = rightLeaves ∨
      ∃ first second, findMultiproofMessageCollision leftLeaves leftProof indices
          rightLeaves rightProof indices = some (first, second) ∧
        first ∈ verifiedMultiproofMessages leftLeaves leftProof indices ∧
        second ∈ verifiedMultiproofMessages rightLeaves rightProof indices ∧
        MessageCollision first second := by
  -- Equal request positions give equal list lengths, so unequal claims differ at some position.
  obtain ⟨_, left⟩ := accepted_of_verify leftAccepted (Nat.le_refl _)
  obtain ⟨_, right⟩ := accepted_of_verify rightAccepted (Nat.le_refl _)
  have leftCount := left.leafCount
  have rightCount := right.leafCount
  cases found : findMultiproofMessageCollision leftLeaves leftProof indices rightLeaves rightProof
      indices with
  | some pair =>
    exact .inr ⟨pair.1, pair.2, rfl,
      findMultiproofMessageCollision_valid leftAccepted rightAccepted found⟩
  | none =>
    refine .inl (List.ext_getElem (by omega) fun position leftBound rightBound => ?_)
    have indexBound : position < indices.length := by omega
    -- Every shared position is bound by the theorem for overlapping requests.
    have first : (indices[position], leftLeaves[position]) ∈ indices.zip leftLeaves :=
      List.mem_iff_getElem.mpr ⟨position, by simp; omega, by simp⟩
    have second : (indices[position], rightLeaves[position]) ∈ indices.zip rightLeaves :=
      List.mem_iff_getElem.mpr ⟨position, by simp; omega, by simp⟩
    -- The search found nothing, so the overlap theorem leaves only equal values.
    rcases verifyMerkleMultiproof_overlap_binding leftAccepted rightAccepted first second with
      equal | ⟨_, _, collided, -, -, -⟩
    · exact equal
    · simp [found] at collided

end EthLib.Serialization.Ssz

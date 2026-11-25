module

public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Proofs.Signing
public import EthLib.Consensus.Proofs.SlashingProtection

/-!
# Proofs: a signer that follows EIP-3076 signs no slashable pair unless SHA-256 collides

Two messages that the signer signs and that its record forbids together share a signing root.

A slashable pair is two different messages with one signing root.

So two SHA-256 inputs of their trees collide.

The search over the messages of the two signing roots returns that collision.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Cryptography.Bls

/-- A signer of votes signs no slashable pair, unless SHA-256 collides on their signing data. -/
theorem notSlashable_or_collision_of_importAndSignAttestations
    {signingRootOf : AttestationData → Root} {pubkey : BLSPubkey} {start finish : Interchange}
    {steps : List AttestationSignerStep}
    -- The signer may import files between its votes.
    (signed : importAndSignAttestations signingRootOf pubkey start steps = .ok finish)
    {data1 data2 : AttestationData} {domain1 domain2 : Domain}
    (member1 : .signAttestation data1 ∈ steps) (member2 : .signAttestation data2 ∈ steps)
    -- The root that the signer takes for each vote is its signing root in a domain.
    --
    -- The two domains may differ.
    (rooted1 : computeSigningRoot data1 domain1 = .ok (signingRootOf data1))
    (rooted2 : computeSigningRoot data2 domain2 = .ok (signingRootOf data2)) :
    isSlashableAttestationData data1 data2 = false ∨ ∃ x y,
      findMessageCollision (signingMessages data1 domain1) (signingMessages data2 domain2) =
        some (x, y) ∧ MessageCollision x y := by
  cases slashable : isSlashableAttestationData data1 data2
  · exact .inl rfl
  -- The record gives the two votes one signing root.
  have same := signingRoot_eq_of_importAndSignAttestations signed member1 member2 slashable
  -- A vote is never slashable with itself, so the two votes differ.
  have differ : data1 ≠ data2 := by
    rintro rfl
    rw [isSlashableAttestationData_self] at slashable
    cases slashable
  rcases computeSigningRoot_ne_or_findMessageCollision (AttestationData.commitmentSized data1)
      (AttestationData.commitmentSized data2) differ rooted1 rooted2 with differ | found
  · exact absurd same differ
  · exact .inr found

/-- A signer of blocks signs no two different headers of one slot, unless SHA-256 collides. -/
theorem eq_or_collision_of_importAndSignBlocks {signingRootOf : BeaconBlockHeader → Root}
    {pubkey : BLSPubkey} {start finish : Interchange} {steps : List BlockSignerStep}
    -- The signer may import files between its headers.
    (signed : importAndSignBlocks signingRootOf pubkey start steps = .ok finish)
    {header1 header2 : BeaconBlockHeader} {domain1 domain2 : Domain}
    (member1 : .signBlock header1 ∈ steps) (member2 : .signBlock header2 ∈ steps)
    (sameSlot : header1.slot = header2.slot)
    -- The root that the signer takes for each header is its signing root in a domain.
    --
    -- The two domains may differ.
    (rooted1 : computeSigningRoot header1 domain1 = .ok (signingRootOf header1))
    (rooted2 : computeSigningRoot header2 domain2 = .ok (signingRootOf header2)) :
    header1 = header2 ∨ ∃ x y,
      findMessageCollision (signingMessages header1 domain1) (signingMessages header2 domain2) =
        some (x, y) ∧ MessageCollision x y := by
  by_cases equal : header1 = header2
  · exact .inl equal
  -- The record gives the two headers of one slot one signing root.
  have same := signingRoot_eq_of_importAndSignBlocks signed member1 member2 sameSlot
  rcases computeSigningRoot_ne_or_findMessageCollision (BeaconBlockHeader.commitmentSized header1)
      (BeaconBlockHeader.commitmentSized header2) equal rooted1 rooted2 with differ | found
  · exact absurd same differ
  · exact .inr found

end EthLib.Consensus

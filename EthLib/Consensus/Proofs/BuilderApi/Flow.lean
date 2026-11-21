module

public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.Proofs.BuilderApi.Bid

/-!
# Proofs: the body built from an accepted bid names the proposer's fee recipient

A proposer accepts a bid only when the header of the bid names its fee recipient.

It then signs a blinded block whose body holds that header.

The payload that the builder reveals unblinds that body only when its header is the same header.

So the payload of the full body names the fee recipient that the proposer checked.

This holds at every fork from Bellatrix to Fulu.

It says that the payload names the fee recipient, not that the fee recipient receives the value.
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base

variable {preset : Preset} {fork : Fork}

/-- From Bellatrix to Fulu, a body that unblinds holds the payload, whose header is the blinded one.
-/
theorem BlindedBeaconBlockBody.executionPayload_unblind
    {body : BlindedBeaconBlockBody preset fork} {range : HasBuilderApi fork}
    {payload : ExecutionPayload preset fork} {full : BeaconBlockBody preset fork}
    (made : body.unblind range payload = .ok full) :
    full.executionPayload range = payload ∧
      payload.header = .ok (body.executionPayloadHeader range) := by
  unfold BlindedBeaconBlockBody.unblind at made
  split at made
  · simp at made
  · rename_i header computed
    split at made
    · rename_i same
      simp only [Except.ok.injEq] at made
      subst made
      exact ⟨rfl, by rw [computed, same]⟩
    · simp at made

/-- From Bellatrix to Fulu, a body built from an accepted bid names the checked fee recipient.

The proposer accepts the bid, and builds the blinded body from the header of the bid.

It unblinds that body with the payload that the builder reveals.

The payload of the full body then names the fee recipient of the check.

The check takes the fee recipient that the proposer registered last, so the payload names that one.
-/
theorem feeRecipient_unblind_of_processBid {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {range : HasBuilderApi fork}
    {signed : SignedBuilderBid preset fork} {feeRecipient : ExecutionAddress}
    {body : BlindedBeaconBlockBody preset fork} {payload : ExecutionPayload preset fork}
    {full : BeaconBlockBody preset fork}
    (accepted : processBid config checks state range signed feeRecipient = .ok ())
    (fromBid : body.executionPayloadHeader range = signed.message.header)
    (made : body.unblind range payload = .ok full) :
    (full.executionPayload range).feeRecipient = feeRecipient := by
  obtain ⟨-, pays, -⟩ := processBid_ok_iff.mp accepted
  obtain ⟨held, header⟩ := BlindedBeaconBlockBody.executionPayload_unblind made
  -- The header of the payload is the header of the bid, which names the fee recipient.
  rw [held, ← (ExecutionPayload.header_parentHash_feeRecipient header).2, fromBid, pays]

end EthLib.Consensus.BuilderApi

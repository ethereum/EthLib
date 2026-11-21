module

public import EthLib.Consensus.BuilderApi.Proposal
public import EthLib.Consensus.Proofs.SlashingProtection

/-!
# Proofs: a proposer's choice between a builder's payload and its local payload

With the circuit breaker fired, a proposer that has signed no blinded block builds locally.

So does one whose bid is late or missing.

A bid in time gives the builder's payload, and a signed blinded block always keeps it.

A recorded block passes the check again, so the record accepts the unblinded block as a repeat.

A block and its blinded form have one signing root, so the unblinded block is that repeat.
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base Cryptography.Bls

/-- With the circuit breaker fired and no blinded block signed, the payload is local. -/
theorem chooseSource_circuitBreaker (bidArrival : Option Nat) :
    chooseSource true bidArrival false = .local := rfl

/-- With no blinded block signed, a bid later than the tolerance, or none, gives a local payload.
-/
theorem chooseSource_late {circuitBreaker : Bool} {bidArrival : Option Nat}
    (late : ∀ arrival, bidArrival = some arrival →
      BUILDER_PROPOSAL_DELAY_TOLERANCE * 1000 < arrival) :
    chooseSource circuitBreaker bidArrival false = .local := by
  unfold chooseSource
  cases circuitBreaker
  · cases bidArrival with
    | none => rfl
    | some arrival => simp [Nat.not_le.mpr (late arrival rfl)]
  · rfl

/-- The payload comes from the builder exactly for a signed blinded block or a bid in time.

A bid in time needs the circuit breaker not to have fired. -/
theorem chooseSource_eq_builder_iff {circuitBreaker : Bool} {bidArrival : Option Nat}
    {signedBlinded : Bool} :
    chooseSource circuitBreaker bidArrival signedBlinded = .builder ↔
      signedBlinded = true ∨ (circuitBreaker = false ∧
        ∃ arrival, bidArrival = some arrival ∧
          arrival ≤ BUILDER_PROPOSAL_DELAY_TOLERANCE * 1000) := by
  unfold chooseSource
  cases signedBlinded <;> cases circuitBreaker <;> cases bidArrival <;> simp

/-- Once a blinded block is signed, the payload comes from the builder, whatever else holds. -/
theorem chooseSource_signedBlinded (circuitBreaker : Bool) (bidArrival : Option Nat) :
    chooseSource circuitBreaker bidArrival true = .builder := rfl

/-- After a block that passed the check is recorded, the same block passes again.

So the unblinded block, with the signing root of the signed blinded block, can still be signed. -/
theorem checkBlock_recordBlock_self {held : Interchange} {pubkey : BLSPubkey} {slot : Slot}
    {root : Root} (passed : held.checkBlock pubkey slot root = .ok ()) :
    (held.recordBlock pubkey slot root).checkBlock pubkey slot root = .ok () := by
  unfold Interchange.checkBlock at passed ⊢
  rw [blocksOf_recordBlock, checkBlockSigning_eq_ok_iff]
  obtain ⟨clear, -⟩ := checkBlockSigning_eq_ok_iff.mp passed
  refine ⟨fun block member => ?_, fun _ _ => Or.inr ?_⟩
  · rcases List.mem_append.mp member with old | new
    · exact clear block old
    · simp_all [SignedBlockRecord.conflictsWith]
  · simp [isRepeatBlock]

end EthLib.Consensus.BuilderApi

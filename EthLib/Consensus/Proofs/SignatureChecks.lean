module

public import EthLib.Consensus.Transition.Basic

/-!
# Proofs: assumptions on the signature checks

The transition takes its BLS signature checks as an argument.

A check that accepts says nothing about who signed, unless an assumption links the two.

The assumption takes a relation that says which messages the holder of each key signed.

It asks that an aggregate check accepts a message only if every key of the aggregate signed it.

No signature scheme meets it with certainty, so the theorems take it as a hypothesis.

The checks that accept every signature do not meet it, when no key signed any message.
-/

@[expose] public section

namespace EthLib.Consensus

/-- The assumption on an aggregate signature check: it accepts only messages that all keys signed.

The relation says which messages the holder of each key signed.

BLS with proofs of possession is meant to give this, except with small probability.

A separate module bounds how often one honest member's bit is forged, with random oracles.

It needs a proof of possession for every signer, and it is not a proof of this assumption.

Ethereum's keys carry deposit signatures instead.

The theorems that reason about one accepted check take the assumption instead of the bound. -/
def SignatureChecks.AggregateSound (checks : SignatureChecks)
    (signed : Cryptography.Bls.BLSPubkey → ByteArray → Prop) : Prop :=
  ∀ keys message signature, checks.fastAggregateVerify keys message signature = true →
    ∀ key ∈ keys, signed key message

/-- The assumption has content: the checks that accept every signature do not meet it.

Here no key signed any message, and the checks still accept a signature by one key. -/
theorem SignatureChecks.not_aggregateSound_acceptAll :
    ¬SignatureChecks.acceptAll.AggregateSound fun _ _ => False :=
  fun sound =>
    sound #[Vector.replicate _ 0] .empty (Vector.replicate _ 0) rfl (Vector.replicate _ 0) (by simp)

end EthLib.Consensus

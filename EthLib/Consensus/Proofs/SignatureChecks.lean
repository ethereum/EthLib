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

Over every input, the BLS checks accept the honest signature of any valid key on any message.

With those checks, the relation must then hold for every valid key and every message.

So two more assumptions cover only a given set of calls, such as the calls that a run made.

One is for aggregate checks, and the other for the check of one signature by one key.

For the relation of real signatures, each says that no accepted call of the set is a forgery.
-/

@[expose] public section

namespace EthLib.Consensus

/-- The assumption on an aggregate signature check: it accepts only messages that all keys signed.

The relation says which messages the holder of each key signed.

With the BLS checks, it holds only for a relation that relates every valid key to every message.

So for those checks, only a form restricted to a set of calls can say who signed.

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

/-- The assumption on aggregate checks, for a given set of calls only.

Each call holds the keys, the message and the signature.

If a call of the set accepts, every key of the call signed its message. -/
def SignatureChecks.AggregateSoundOn (checks : SignatureChecks)
    (calls : Array Cryptography.Bls.BLSPubkey × ByteArray × Cryptography.Bls.BLSSignature → Prop)
    (signed : Cryptography.Bls.BLSPubkey → ByteArray → Prop) : Prop :=
  ∀ keys message signature, calls (keys, message, signature) →
    checks.fastAggregateVerify keys message signature = true → ∀ key ∈ keys, signed key message

/-- The assumption on a set of calls has content: the checks that accept everything fail it.

The set holds one call by one key, and no key signed any message. -/
theorem SignatureChecks.not_aggregateSoundOn_acceptAll (key : Cryptography.Bls.BLSPubkey)
    (message : ByteArray) (signature : Cryptography.Bls.BLSSignature) :
    ¬SignatureChecks.acceptAll.AggregateSoundOn (· = (#[key], message, signature))
      fun _ _ => False :=
  fun sound => sound #[key] message signature rfl rfl key (by simp)

/-- The assumption on the check of one signature by one key, for a given set of calls only.

Each call holds the key, the message and the signature.

If a call of the set accepts, its key signed its message. -/
def SignatureChecks.VerifySoundOn (checks : SignatureChecks)
    (calls : Cryptography.Bls.BLSPubkey × ByteArray × Cryptography.Bls.BLSSignature → Prop)
    (signed : Cryptography.Bls.BLSPubkey → ByteArray → Prop) : Prop :=
  ∀ key message signature, calls (key, message, signature) →
    checks.verify key message signature = true → signed key message

/-- The assumption on a set of calls has content: the checks that accept everything fail it.

The set holds one call, and no key signed any message. -/
theorem SignatureChecks.not_verifySoundOn_acceptAll (key : Cryptography.Bls.BLSPubkey)
    (message : ByteArray) (signature : Cryptography.Bls.BLSSignature) :
    ¬SignatureChecks.acceptAll.VerifySoundOn (· = (key, message, signature)) fun _ _ => False :=
  fun sound => sound key message signature rfl rfl

end EthLib.Consensus

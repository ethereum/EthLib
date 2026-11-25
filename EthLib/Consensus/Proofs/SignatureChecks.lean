module

public import EthLib.Consensus.Transition.Basic

/-!
# Proofs: assumptions on the signature checks

The transition takes its BLS signature checks as an argument.

A check that accepts says nothing about who signed, unless an assumption links the two.

No signature scheme meets it with certainty, so the theorems take a form of it as a hypothesis.
-/

@[expose] public section

namespace EthLib.Consensus

/-- The assumption on an aggregate signature check: it accepts only messages that all keys signed.

A separate module bounds how often one honest member's bit is forged, with random oracles.

It needs a proof of possession for every signer, and it is not a proof of this assumption.

Ethereum's keys carry deposit signatures instead.

Over every input, the BLS checks accept the honest signature of any valid key on any message.

With the BLS checks, it holds only for a relation that relates every valid key to every message.

So for those checks, only a form restricted to a set of calls can say who signed.

The theorems take the form on a set of calls instead of the bound; this form implies it. -/
def SignatureChecks.AggregateSound (checks : SignatureChecks)
    -- The relation says which messages the holder of each key signed.
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

If a call of the set accepts, every key of the call signed its message.

For the relation of real signatures, it says that no accepted call of the set is a forgery. -/
def SignatureChecks.AggregateSoundOn (checks : SignatureChecks)
    -- Each call holds the keys, the message and the signature.
    --
    -- The set can be the calls that a run made.
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

/-- The assumption over every input gives the assumption on any set of calls. -/
theorem SignatureChecks.AggregateSound.on {checks : SignatureChecks}
    {signed : Cryptography.Bls.BLSPubkey → ByteArray → Prop} (sound : checks.AggregateSound signed)
    (calls : Array Cryptography.Bls.BLSPubkey × ByteArray × Cryptography.Bls.BLSSignature → Prop) :
    checks.AggregateSoundOn calls signed :=
  fun keys message signature _ => sound keys message signature

/-- The assumption on the check of one signature by one key, for a given set of calls only.

If a call of the set accepts, its key signed its message.

For the relation of real signatures, it says that no accepted call of the set is a forgery. -/
def SignatureChecks.VerifySoundOn (checks : SignatureChecks)
    -- Each call holds the key, the message and the signature.
    --
    -- The set can be the calls that a run made.
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

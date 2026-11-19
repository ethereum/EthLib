module

/-!
# Signature aggregation

The model is Definition 8 of [Hofheinz, Reichle and Wagner](https://eprint.iacr.org/2026/723).

The paper aggregates signatures on one common message; here each signer signs its own message.
-/

@[expose] public section

namespace EthLib.Cryptography.Aggregation

/-- A signature aggregation scheme.

Hash-based signatures have no algebraic structure to combine, unlike BLS signatures.

An aggregation scheme combines them with a proof, which a user never sees. -/
structure Scheme where
  /-- The public parameters, which every algorithm reads. -/
  Params : Type
  /-- The public keys. -/
  PublicKey : Type
  /-- The secret keys. -/
  SecretKey : Type
  /-- The messages. -/
  Message : Type
  /-- What a signer reads beyond its key and the message:
  - for a stateful scheme, the leaf index or epoch;
  - for a stateless scheme, the unit type. -/
  SignContext : Type
  /-- What key generation reads, such as a seed. -/
  KeyGenInput : Type
  /-- The signatures. -/
  Signature : Type
  /-- The aggregates. -/
  Aggregate : Type
  /-- The public parameters, fixed once for the scheme.

  The paper draws them at random; a transparent proof system needs no such draw. -/
  setup : Params
  /-- Generates a key pair from its input.

  The input carries all the randomness of the scheme.

  It returns nothing on an input it rejects, such as a seed of the wrong length. -/
  gen : Params → KeyGenInput → Option (PublicKey × SecretKey)
  /-- Signs a message under a secret key in a context.

  Signing is deterministic, where the paper allows it to draw randomness.

  It returns nothing when the key cannot sign in that context. -/
  sign : Params → SecretKey → SignContext → Message → Option Signature
  /-- Aggregates raw signatures and earlier aggregates into one aggregate.

  Each raw signature comes with its claim, and each earlier aggregate with the claims it covers.

  Since an input may be an earlier aggregate, aggregates nest to any depth.

  Two inputs may cover the same claim.

  Aggregation is deterministic.

  It returns nothing when an input does not verify or the result exceeds the scheme's capacity. -/
  aggregate : Params → List ((PublicKey × Message) × Signature) →
    List (List (PublicKey × Message) × Aggregate) → Option Aggregate
  /-- Checks an aggregate against the claims it covers.

  It reads only the claims and the aggregate, never how the aggregate was built. -/
  verify : Params → List (PublicKey × Message) → Aggregate → Bool

/-- A claim of a scheme: a public key and a message it signed.

Signers of one aggregate may sign different messages. -/
abbrev Scheme.Claim (S : Scheme) : Type :=
  S.PublicKey × S.Message

end EthLib.Cryptography.Aggregation

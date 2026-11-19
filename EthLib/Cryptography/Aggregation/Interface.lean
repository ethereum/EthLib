module

/-!
# Signature aggregation

Hash-based signatures have no algebraic structure to combine, unlike BLS signatures.

An aggregation scheme combines them with a proof instead.

A user sees keys, signatures, aggregates and one verifier; the proof system stays hidden.

The interface follows the syntax of hint-free multi-signatures, with seven choices.

- A claim is a public key and a message it signed, so signers may sign different messages.
- Aggregation takes raw signatures and earlier aggregates, so aggregates nest to any depth.
- Two inputs of one aggregation may cover the same claim.
- Verification reads the claims and the aggregate, never how the aggregate was built.
- Signing reads a context: a leaf index for a stateful scheme, nothing for a stateless one.
- Key generation reads an input of the scheme's own type, such as a seed.
- Randomness enters through that input only: signing and aggregation are deterministic.

The syntax is that of [Hofheinz, Reichle and Wagner](https://eprint.iacr.org/2026/723).
-/

@[expose] public section

namespace EthLib.Cryptography.Aggregation

/-- A signature aggregation scheme.

It generates keys, signs messages, and aggregates signatures and earlier aggregates.

It verifies an aggregate against the claims it covers.

A claim is a public key with a message it signed. -/
structure Scheme where
  /-- The public parameters, which every algorithm reads. -/
  Params : Type
  /-- The public keys. -/
  PublicKey : Type
  /-- The secret keys. -/
  SecretKey : Type
  /-- The messages. -/
  Message : Type
  /-- What a signer reads beyond its key and the message.

  For a stateful scheme it is the leaf index or epoch.

  For a stateless scheme it is the unit type. -/
  SignContext : Type
  /-- What key generation reads, such as a seed. -/
  KeyGenInput : Type
  /-- The signatures. -/
  Signature : Type
  /-- The aggregates. -/
  Aggregate : Type
  /-- The public parameters, fixed once for the scheme. -/
  setup : Params
  /-- Generates a key pair from its input.

  It returns nothing on an input it rejects, such as a seed of the wrong length. -/
  gen : Params → KeyGenInput → Option (PublicKey × SecretKey)
  /-- Signs a message under a secret key in a context.

  It returns nothing when the key cannot sign in that context. -/
  sign : Params → SecretKey → SignContext → Message → Option Signature
  /-- Aggregates raw signatures and earlier aggregates into one aggregate.

  Each raw signature comes with its claim, and each earlier aggregate with the claims it covers.

  It returns nothing when an input does not verify or the result exceeds the scheme's capacity. -/
  aggregate : Params → List ((PublicKey × Message) × Signature) →
    List (List (PublicKey × Message) × Aggregate) → Option Aggregate
  /-- Checks an aggregate against the claims it covers. -/
  verify : Params → List (PublicKey × Message) → Aggregate → Bool

/-- A claim of a scheme: a public key and a message it signed. -/
abbrev Scheme.Claim (S : Scheme) : Type :=
  S.PublicKey × S.Message

end EthLib.Cryptography.Aggregation

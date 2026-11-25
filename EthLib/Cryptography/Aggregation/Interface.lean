module

/-!
# Signature aggregation

The model is inspired by Definition 8 of [Hofheinz et al.](https://eprint.iacr.org/2026/723).

The paper aggregates signatures on one common message; here each signer signs its own message.
-/

@[expose] public section

namespace EthLib.Cryptography.Aggregation

/-- A signature aggregation scheme: a signature scheme with a way to combine its signatures. -/
structure Scheme where
  /-- The public parameters, which every algorithm reads. -/
  Params : Type
  /-- The public keys. -/
  PublicKey : Type
  /-- The secret keys. -/
  SecretKey : Type
  /-- The messages. -/
  Message : Type
  /-- The contexts in which a key can sign:
  - for an epoch-based scheme, the epochs of the key's lifetime;
  - for a stateless scheme, the unit type.

  A signature binds its context, so a verifier reads the context as part of the claim. -/
  SignContext : Type
  /-- The inputs of key generation, such as seeds of the right length.

  Every input is valid, so key generation cannot fail. -/
  KeyGenInput : Type
  /-- The signatures. -/
  Signature : Type
  /-- The aggregates. -/
  Aggregate : Type
  /-- The public parameters, fixed once for the scheme.

  The paper draws them at random; a transparent proof system needs no such draw. -/
  setup : Params
  /-- Whether a key may sign at most once in each context.

  An epoch-based scheme sets it: a one-time key that signs twice can leak its secret.

  The unforgeability game refuses a second signing query in one context when it is set. -/
  stateful : Bool
  /-- The largest number of distinct claims one aggregate must cover. -/
  capacity : Nat
  /-- Generates a key pair from its input.

  The input carries all the randomness of key generation. -/
  gen : Params → KeyGenInput → PublicKey × SecretKey
  /-- Signs a message under a secret key in a context.

  Signing is deterministic, where the paper allows it to draw randomness. -/
  sign : Params → SecretKey → SignContext → Message → Signature
  /-- Checks a single signature against the claim it signs: a key, a context and a message. -/
  verifySignature : Params → PublicKey × SignContext × Message → Signature → Bool
  /-- Aggregates signatures and earlier aggregates into one aggregate.

  Each signature comes with its claim, and each earlier aggregate with the claims it covers:
  - an input may be an earlier aggregate, so aggregates nest to any depth;
  - two inputs may cover the same claim;
  - aggregation is deterministic. -/
  aggregate : Params → List ((PublicKey × SignContext × Message) × Signature) →
    List (List (PublicKey × SignContext × Message) × Aggregate) → Aggregate
  /-- Checks an aggregate against the claims it covers.

  It reads only the claims and the aggregate, never how the aggregate was built. -/
  verify : Params → List (PublicKey × SignContext × Message) → Aggregate → Bool

/-- A claim: a public key, a context and a message that the key signed in that context.

The proofs of correctness and unforgeability state their conditions over claims. -/
abbrev Scheme.Claim (S : Scheme) : Type :=
  S.PublicKey × S.SignContext × S.Message

end EthLib.Cryptography.Aggregation

module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.AdversaryCalls
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Main

/-!
# Proofs: leanSPHINCS as EthLib computes it is unforgeable

The theorem holds in the random oracle model, for one key and at most `2^30` signing requests.

Take an adversary whose experiment makes at most `q >= 1` hash calls.

It forges a signature with probability at most `q / 2^127`.

`q` counts every hash call of the experiment, the signer's and key generation's included.

The game runs EthLib's key generation, signing and verification.

Their hash `H` is a query to the oracle.

The security proof in `Security/` reasons over a model of the scheme with the same calls.

The bridge in `Unforgeability/Bridge/` compares EthLib with it:

- EthLib's bytes, addresses, keys and signatures are the model's.
- Each hashing routine of EthLib is the model's, call for call or under every answer function.
- An EthLib forgery is a model forgery of a translated adversary.
- A signing request costs the model at most what it costs EthLib, so the budget `q` carries over.

A second theorem charges only the adversary's own hash calls, and takes a bound on its requests.

The scheme's calls then add a constant: 264193 for key generation and 491 for verification.

Each signing request adds at most `470595 + 3 * 2^32`, when every counter search runs to its end.

At the model's cap of 1,182,000,000 requests, the constant is about `2^63.7`.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

/-- leanSPHINCS as EthLib computes it is strongly unforgeable in the random oracle model.

Take an adversary whose experiment makes at most `q >= 1` hash calls in every run.

It forges with probability at most `q / 2^127`.

`q` counts the calls of key generation and of every signing request too. -/
theorem unforgeable : HasClassicalSecurityBits 127 := fun q hq adversary hbound =>
  (forgeAdvantage_le adversary).trans
    (SphincsSecurity.h26_layered q hq (translate adversary)
      (hasHashQueryBound_translate_self adversary q hbound))

/-- leanSPHINCS as EthLib computes it is strongly unforgeable, with the adversary's calls as budget.

Take an adversary with at most `q` hash calls of its own and `r` signing requests in every run.

It forges with probability at most `(q + C) / 2^127`, where `C` bounds the scheme's calls.

At 1,182,000,000 requests, `C` is about `2^63.7`, so the bound is never below about `2^-63.3`. -/
theorem unforgeable_adversary : HasAdversarySecurityBits 127 := fun q r adversary hbound =>
  unforgeable (q + schemeCalls r) (by unfold schemeCalls keyGenCalls; omega) adversary
    (hasHashQueryBound_of_adversary adversary q r hbound)

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge

/-! The build fails if the theorem ever depends on more than Lean's three standard axioms. -/

/--
info: 'EthLib.Cryptography.Sphincs.Unforgeability.Bridge.unforgeable' depends on axioms:

[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EthLib.Cryptography.Sphincs.Unforgeability.Bridge.unforgeable

/--
info: 'EthLib.Cryptography.Sphincs.Unforgeability.Bridge.unforgeable_adversary' depends on axioms:

[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EthLib.Cryptography.Sphincs.Unforgeability.Bridge.unforgeable_adversary

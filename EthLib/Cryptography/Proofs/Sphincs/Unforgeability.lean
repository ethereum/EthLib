module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Cost
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

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge

/-! The build fails if the theorem ever depends on more than Lean's three standard axioms. -/

/--
info: 'EthLib.Cryptography.Sphincs.Unforgeability.Bridge.unforgeable' depends on axioms:

[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EthLib.Cryptography.Sphincs.Unforgeability.Bridge.unforgeable

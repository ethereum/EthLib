module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Statement
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Domains
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.LandedDigest
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.VerificationCost

/-!
# Proofs: the model of the leanSPHINCS security proof

A model of leanSPHINCS in the random oracle model, with its lemmas.

The model is generic over the height, the layers, the FORS forest and the cap on signatures.

The security proof that reasons about it lands in later parts.

The README of the security proof says where the proof comes from and what changed here.
-/

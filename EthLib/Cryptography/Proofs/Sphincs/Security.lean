module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Statement
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Domains
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.LandedDigest
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.VerificationCost
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Base.SplitCert
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Base.VirtualMono
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Seed.Coupling
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Configurations
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.CoverPotential.Price
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.NoRepeat
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.ScanSigner.SignatureLaw
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Classification.Signature
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.Outside
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.ShortInputs
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.GraphView.Correctness
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.CoverBound.MomentTable

/-!
# Proofs: the model of the leanSPHINCS security proof

A model of leanSPHINCS in the random oracle model, with its lemmas.

Generic probability bounds, and the coupling that moves the hidden key seed out of the game.

The model is generic over the height, the layers, the FORS forest and the cap on signatures.

The security proof that reasons about it lands in later parts.

The README of the security proof says where the proof comes from and what changed here.
-/

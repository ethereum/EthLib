module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Configurations
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Base.SplitCert
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.CoverBound.MomentTable
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.CoverPotential.Price
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.ScanSigner.SignatureLaw
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.Outside
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.GraphSampling
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Classification.Hidden
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.Memo
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.CostProgram
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.SeedFreeGame

/-!
# Proofs: the model of the leanSPHINCS security proof

A model of leanSPHINCS in the random oracle model, with its lemmas.

Generic probability bounds, and the coupling that moves the hidden key seed out of the game.

The model is generic over the height, the layers, the FORS forest and the cap on signatures.

The first game hops of the security proof are here too.

They internalize long hash inputs, sample short ones as one table, and count the hash calls of runs.

The rest of the proof lands in later parts.

The README of the security proof says where the proof comes from and what changed here.
-/

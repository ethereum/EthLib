module

public import
  EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Classification.RecoveredFors
public import
  EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Classification.RefinedEvents
public import
  EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Classification.SignedReveals
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Classification.Targeting
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Configurations
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.CoverBound.ClassLaw
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.CoverBound.HTermOption
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.CoverBound.IntTables
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.CoverPotential.StartValue
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LargeBudget.HeavyTerm
public import
  EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LargeBudget.WeightedPotential
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.ExposedUniform
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.RouteStart
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.SeedElimination
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.ScanSigner.ScanReveals
public import
  EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.SmallBudget.Contact.NearWitness

/-!
# Proofs: the model of the leanSPHINCS security proof

A model of leanSPHINCS in the random oracle model, with its lemmas.

Generic probability bounds, and the coupling that moves the hidden key seed out of the game.

The model is generic over the height, the layers, the FORS forest and the cap on signatures.

The first game hops of the security proof are here too.

They internalize long hash inputs, sample short ones as one table, and count the hash calls of runs.

They also remove the key's seed and the scheme seed from the game.

A lazy run samples the hidden values only when a hash call reads them.

The rest of the proof lands in later parts.

The README of the security proof says where the proof comes from and what changed here.
-/

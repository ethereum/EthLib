module

public import EthLib.Consensus.Proofs.Containers.Execution
public import EthLib.Consensus.Proofs.Models.Ffg.AccountableSafety
public import EthLib.Consensus.Proofs.Models.Ffg.PlausibleLiveness
public import EthLib.Consensus.Proofs.Models.ForkChoice.LmdGhost

/-!
# `EthLib.Consensus.Proofs`

Machine-checked properties and models of the consensus layer.

The models are abstract protocols, and their theorems say why the protocol is secure.
-/

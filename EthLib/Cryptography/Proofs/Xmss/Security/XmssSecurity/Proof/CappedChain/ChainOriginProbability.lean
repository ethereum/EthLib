module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CappedChain.ChainEventDecomposition
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.WinningEventReduction

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def WinningOutcomeChainValueHasKeygenOrigin
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  WinningOutcomeBadEventOccurs finalCache outcome (.chain chain) ∧
    OutcomeChainValueHasKeygenOrigin keygenCache finalCache secretKey outcome chain

end XmssSecurity.CappedChain

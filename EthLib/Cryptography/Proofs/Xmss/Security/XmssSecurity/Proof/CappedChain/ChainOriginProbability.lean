import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CappedChain.ChainEventDecomposition
import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.WinningEventReduction

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def WinningOutcomeChainValueHasKeygenOrigin
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  WinningOutcomeBadEventOccurs finalCache outcome (.chain chain) ∧
    OutcomeChainValueHasKeygenOrigin keygenCache finalCache secretKey outcome chain

end XmssSecurity.CappedChain

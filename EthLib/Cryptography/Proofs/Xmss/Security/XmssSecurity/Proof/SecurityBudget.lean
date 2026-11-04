module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.EncodingLemmas
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.RandomOracle

@[expose] public section

namespace XmssSecurity

/-- The elementary bad events used by the current classical reduction. -/
inductive BadEvent where
  | encoding
  | chain (chain : ChainIndex)
  | suffixCollision (step : Fin verificationChainHashes)
  | leaf
  /-- Two paths collide below a parent on level `level + 1`, from 1 to 16. -/
  | merkle (level : Fin treeHeight)
deriving DecidableEq, Fintype

end XmssSecurity

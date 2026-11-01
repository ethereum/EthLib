module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.RandomOracle

@[expose] public section

namespace XmssSecurity

def hashOutputHigh (output : HashOutput) : Digest :=
  (Rom.hashOutputEquivDigestPair output).1

end XmssSecurity

module

public import VCVio.OracleComp.Constructions.SampleableType
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.HashInputLemmas

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

theorem card_randomness : Fintype.card Randomness = 2 ^ randomnessBits := by
  simp

end XmssSecurity

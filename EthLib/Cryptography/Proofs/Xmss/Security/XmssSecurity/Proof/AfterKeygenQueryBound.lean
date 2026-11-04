module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CacheReplayEval
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.DetailedExecution
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CappedChain.EncodingQueryBound
public import VCVio.OracleComp.QueryTracking.QueryBound
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.IdealStatement
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.StatementLemmas
public import VCVio.OracleComp.QueryTracking.SubSpec
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Translate

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

/-- A query to the hash oracle, not to the uniform sampler. -/
def IsHashQuery : OracleWorld.Domain → Prop := fun input => input matches .inr _

instance : DecidablePred IsHashQuery := by
  intro input
  cases input <;> unfold IsHashQuery <;> exact inferInstance

/-- The after-key-generation budget bounds every run after key generation. -/
theorem afterKeygen_hashQueryBound (adversary : Adversary) (q : Nat)
    (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    HashQueryBound (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
      keyResult.2 q := by
  have hrest : HashQueryBound
      (Seeded.gameRest Concrete.scheme adversary keyResult.1.1 keyResult.1.2) keyResult.2 q := by
    simp only [HashQueryBound, simulateQ_countHashQueries]
    exact hbound keyResult hkeyResult
  have hmap : GameOutcome.won <$>
      detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2 =
        Seeded.gameRest Concrete.scheme adversary keyResult.1.1 keyResult.1.2 := by
    classical
    simp [Seeded.gameRest, detailedGameAfterKeygen, GameOutcome.won]
  exact (hashQueryBound_iff_of_map_eq hmap _ _).mpr hrest

namespace CappedChain

theorem sourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen
    (q : Nat) (adversary : Adversary)
    (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    HashQueryBound (sourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2)
      keyResult.2 q :=
  (hashQueryBound_iff_of_map_eq
    (detailedGameAfterKeygen_unlogged_projection adversary keyResult.1.1 keyResult.1.2) _ _).mp
      (afterKeygen_hashQueryBound adversary q hbound keyResult hkeyResult)

end CappedChain

end XmssSecurity

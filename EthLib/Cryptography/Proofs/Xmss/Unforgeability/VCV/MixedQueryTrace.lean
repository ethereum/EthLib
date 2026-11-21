module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedGameProgram
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ClientRelease
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ResidualRandomizer
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerReleaseTrace

/-!
# Requests that cannot disclose a chain position

The optional-reply client can draw private coins and make arbitrary public hash requests.

Both use ports distinct from a direct read of a chain value.

The two private accesses before signing draw only from their respective local tables.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleSpec OracleComp
open CanonicalGraph.PairedQueries

/-- The tick uses only the private sampling port, including from an empty local tick table. -/
theorem tick_no_chain (pp : PublicParam) (s : ResidualCache pp) :
    AllQueriesSatisfy (simulateQ (expand PairedHashWord.halves) ((mixedTick pp).run s))
      (Within ∅) := by
  simp only [mixedTick, StateT.run_mk, simulateQ_map, expand_coin]
  exact map_within _ (lifted_random _)

/-- A private parameter lookup samples only missing rows. -/
theorem parameter_no_chain (pp : PublicParam) (s : ResidualCache pp) :
    AllQueriesSatisfy (simulateQ (expand PairedHashWord.halves) ((mixedParameter pp).run s))
      (Within ∅) := by
  simp only [mixedParameter, StateT.run_map, simulateQ_map, mixedLocalWord, StateT.run_mk,
    simulateQ_bind, simulateQ_pure, expand_coin]
  apply map_within
  apply allQueriesSatisfy_bind (lifted_random _)
  intro low
  apply allQueriesSatisfy_bind (lifted_random _)
  intro high
  exact allQueriesSatisfy_pure _ _

/-- A raw adversarial hash, even at an honest chain address, uses only the public halves. -/
theorem adversary_no_chain (pp : PublicParam) (t : World.Domain) (s : ResidualCache pp) :
    AllQueriesSatisfy (simulateQ (expand PairedHashWord.halves) ((mixedWorldPass pp t).run s))
      (Within ∅) := by
  simp only [mixedWorldPass, StateT.run_monadLift, monadLift_self, simulateQ_bind, simulateQ_pure,
    simulateQ_spec_query]
  apply allQueriesSatisfy_bind
  · cases t with
    | inl n =>
      apply (allQueriesSatisfy_query_iff _ _).2
      intro c eq
      cases eq
    | inr b =>
      simp only [expand, RandomOraclePairedValue.readHalves, simulateQ_bind, simulateQ_pure,
        simulateQ_spec_query]
      apply allQueriesSatisfy_bind
      · apply (allQueriesSatisfy_query_iff _ _).2
        intro c eq
        cases eq
      · intro low
        apply allQueriesSatisfy_bind
        · apply (allQueriesSatisfy_query_iff _ _).2
          intro c eq
          cases eq
        · exact fun _ => allQueriesSatisfy_pure _ _
  · exact fun _ => allQueriesSatisfy_pure _ _

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

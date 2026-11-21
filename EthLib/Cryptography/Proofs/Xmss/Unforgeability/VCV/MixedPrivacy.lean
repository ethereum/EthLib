module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedVerifierCut
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ChainDisclosure
public import VCVio.OracleComp.QueryTracking.RandomOracle.DisclosureTrace
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ChainDisclosure
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ClientRelease
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedVerifier
import all VCVio.OracleComp.QueryTracking.RandomOracle.Undisclosed

/-!
# Chain positions hidden throughout the actual normalized game

The verifier can query any public hash input, including an input for a hidden chain.

It cannot directly read a private chain cell.

A prefix of a chain remains absent until a successful signer discloses a value inside it.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleSpec OracleComp
open ChainDisclosure
open ChainGraph (Public Word)

private theorem protected_row {l : Layer} {e : UInt32} {x : Vector (Fin CHAIN_LENGTH) V} {k : Row}
    (inside : Sum.inr k ∈ prefixCells l e x) : ∃ a i j, k = .inl (a, .chain e i j) := by
  obtain ⟨i, d, _, eq⟩ := inside
  cases d with
  | mk d bound =>
    cases d with
    | zero => cases eq
    | succ n => exact ⟨l,i,Fin.ofNat 3 n,Sum.inr.inj eq⟩

private theorem protects (l : Layer) (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V)
    (seen : Set Cell)
    (separate : ∀ c ∈ seen, c ∉ prefixCells l e x)
    (q : SharedSpec.Domain) (within : Within seen q) :
    CanonicalGraph.AvoidsDirectRead (pub := Public) (R := Word) (prefixCells l e x) q := by
  rcases q with (((n | b) | start) | (c | k))
  · trivial
  · trivial
  · exact separate _ (within _ rfl)
  · trivial
  · intro member
    obtain ⟨a,i,j,rfl⟩ := protected_row member
    exact separate _ (within _ rfl) member

private theorem verifier_no_chain (pk : PublicKey) (f : Forgery) :
    AllQueriesSatisfy (verifyWith Honest.hash pk f.message f.signature) (Within ∅) := by
  have raw {α : Type} (p : OracleComp Bytes α) :
      AllQueriesSatisfy (simulateQ Honest.hash p) (Within ∅) := by
    induction p using OracleComp.inductionOn with
    | pure a => exact allQueriesSatisfy_pure _ _
    | query_bind t k ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      apply allQueriesSatisfy_bind _ ih
      unfold Honest.hash
      apply allQueriesSatisfy_bind
      · exact (allQueriesSatisfy_query_iff _ _).2 (by intro c eq; cases eq)
      · intro lo
        apply allQueriesSatisfy_bind
        · exact (allQueriesSatisfy_query_iff _ _).2 (by intro c eq; cases eq)
        · exact fun _ => allQueriesSatisfy_pure _ _
  have h := raw (verifyWith byteQuery pk f.message f.signature)
  simpa only [verify_sim, byteQuery, simulateQ_spec_query] using h

attribute [local irreducible] simulateQ mixedGame graph expandLocal Xmss.verifyWith
attribute [local irreducible] prefixCells releasedCells

/-- A chain prefix with no authorized release stays absent through public verification. -/
theorem mixed_prefix_absent (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    (obs : Outcome) (out : ResidualCache pp) (t : DeferredState)
    (actual : (some (obs,out),t) ∈ support ((simulateQ (graph pp).deferredImpl
      (guardedGraph left ((mixedGame pp A).run r))).run ((∅,∅),[])))
    (l : Layer) (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V)
    (separate : ∀ c ∈ releasedCells pp t.1 obs.log, c ∉ prefixCells l e x) :
    ∀ c ∈ prefixCells l e x, t.1.2 c = none := by
  obtain ⟨_, start, cut, xs, key, client, reads,
    verified⟩ := mixed_verifier_cut pp A left r _ obs out t actual
  have ignore : ∀ c ∈ (∅ : Set Cell), c ∉ prefixCells l e x := fun _ h => h.elim
  have seed := (graph pp).stays_undisclosed (prefix_child pp l e x)
    ((root_within pp .top LAYER_HEIGHT 0 ∅).mono (protects l e x ∅ ignore)) (fun _ _ => rfl) key
  have later := (graph pp).le_of_mem_support_simulateQ_deferredImpl _ verified
  have avoid : ∀ c ∈ releasedCells pp cut.1 obs.log, c ∉ prefixCells l e x :=
    fun c h => separate c (released_mono later (fun _ mem => mem) h)
  have hidden := (graph pp).stays_undisclosed_on_log _ (prefix_child pp l e x) seed client
    (fun entry mem => protects l e x _ avoid _ (reads entry mem))
  exact (graph pp).stays_undisclosed (prefix_child pp l e x)
    ((verifier_no_chain obs.key obs.candidate).mono (protects l e x ∅ ignore)) hidden verified

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

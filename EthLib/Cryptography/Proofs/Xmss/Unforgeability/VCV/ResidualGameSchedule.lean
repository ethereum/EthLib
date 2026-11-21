module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ResidualClient
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifierTail
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# The original keyed candidate at the sampled parameter

The sampled parameter fixes the graph before the native key generator builds the top root.

The client and verifier then share that key, the complete signing log and both residual tables.

Replaying a completed physical cap preserves all four final tables.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography Constants HashSig OracleComp OracleSpec TwoLayerGraph
open SecretEncoding.Residual

/-- The hidden root of the sampled parameter, followed by the adaptive stateful signing oracle. -/
@[expose] noncomputable def localClient (pp : PublicParam) (A : Adversary) :
    Honest.WithLocal (ResidualCache pp) BeforeVerify := do
  let root ← liftM (simulateQ (Honest.selection pp .top).liftQuery
    (LayerGraph.Hidden.beforeNode pp .top LAYER_HEIGHT 0 >>=
      fun _ => LayerGraph.readOutput (LayerGraph.treeRole LAYER_HEIGHT 0)))
  let key : PublicKey := ⟨root, pp⟩
  let (candidate, log) ← (simulateQ (clientOracle pp) (A.main key)).run
  return ⟨key, candidate, log⟩

/--
The normalized caller returns the native observation and verifies it with ordinary public hashes.
-/
@[expose] noncomputable def localGame (pp : PublicParam) (A : Adversary) :
    Honest.WithLocal (ResidualCache pp) Outcome := do
  let pre ← localClient pp A
  liftM (verifyCandidate Honest.hash pre)

private theorem root_same (pp : PublicParam) :
    Honest.SameLocal pp
      (inGraph pp (Xmss.node (hashOf sourcePass) pp sourcePrf .top LAYER_HEIGHT 0))
      (liftM (simulateQ (Honest.selection pp .top).liftQuery
        (LayerGraph.Hidden.beforeNode pp .top LAYER_HEIGHT 0 >>=
          fun _ => LayerGraph.readOutput (LayerGraph.treeRole LAYER_HEIGHT 0)))) := by
  rw [node_map_monad (fun {_} p => inGraph pp p) (inGraph_pure pp) (inGraph_bind pp)]
  simp only [inGraph_hash]
  change Honest.SameLocal pp (Xmss.node _ pp (graphPrf pp) _ _ _) _
  rw [Honest.node_lift pp .top (graphPrf pp) _ (graphPrf_pairs pp .top)]
  apply Honest.sameLocal_lift
  exact Honest.node_pairs pp .top _ (Honest.prf_pair pp .top emptyPrf) LAYER_HEIGHT 0 le_rfl

private theorem verify_same (pp : PublicParam) (pk : PublicKey) (forgery : Forgery) :
    inGraph pp (verifyWith (hashOf sourcePass) pk forgery.message forgery.signature) =
      (liftM (verifyWith Honest.hash pk forgery.message forgery.signature) : Honest.WithLocal
        (ResidualCache pp) _) := by
  rw [verifyWith_map_monad (fun {_} p => inGraph pp p) (inGraph_pure pp) (inGraph_bind pp)]
  rw [verifyWith_map_monad (fun {_} p => (liftM p : Honest.WithLocal (ResidualCache pp) _))
    (fun _ => liftM_pure _) (fun _ _ => liftM_bind _ _)]
  simp only [inGraph_hash]

/-- This is an equality of complete eager runs of the actual conditioned source. -/
theorem continuation_local (pp : PublicParam) (A : Adversary) :
    Honest.SameLocal pp (inGraph pp (continuation A pp)) (localGame pp A) := by
  simp only [continuation, localGame, localClient, inGraph_bind, inGraph_pure,
    bind_assoc, pure_bind]
  apply Honest.SameLocal.bind (root_same pp)
  intro root
  apply Honest.SameLocal.bind (adaptive_requests pp (A.main ⟨root, pp⟩))
  rintro ⟨candidate, log⟩
  simp only [verifyCandidate, liftM_bind, liftM_pure, verify_same]
  exact fun _ => rfl

attribute [local irreducible] localGame continuation graphRun runGraph evaluate inGraph

/-- The hidden execution preserves the outcome and four final tables of a completed capped run.

The cap tests the full-word query before splitting it.
-/
theorem graphRun_local_some (A : Adversary) (left : Nat) (w : HashOutput)
    (a : Outcome) (extra : ResidualCache (parameterOfWord w)) (st : GraphState)
    (actual : ((some a, extra), st) ∈ support (graphRun A left w)) :
    let pp := parameterOfWord w
    ((a, extra), st) ∈ support ((simulateQ (graph pp).eagerImpl
      ((localGame pp A).run (localState _ _ (toKeyedState pp (afterWord w))))).run (∅, ∅)) := by
  have native := graphRun_some A left w a extra st actual
  let pp := parameterOfWord w
  let initial := localState _ _ (toKeyedState pp (afterWord w))
  rw [runGraph, evaluate_inGraph] at native
  have eq := continuation_local pp A initial
  have stateEq := congrArg (fun (body : StateT Honest.SharedState ProbComp
      (Outcome × ResidualCache pp)) =>
    body.run (∅, ∅)) eq
  rw [stateEq] at native
  exact native

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

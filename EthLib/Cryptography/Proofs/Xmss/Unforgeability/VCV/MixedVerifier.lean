module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedCalls
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# The actual verifier under the mixed physical cutoff

The verifier runs on the supplied public key, candidate message and signature.

Every adaptive public hash request, at either layer, spends one physical query.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig TwoLayerGraph Honest OracleComp OracleSpec

private abbrev Bytes := ByteArray →ₒ Vector UInt8 32
private def byteQuery (b : ByteArray) : OracleComp Bytes (Vector UInt8 32) := liftM (Bytes.query b)

private theorem byte_calls {α : Type} (pp : PublicParam) (p : OracleComp Bytes α) :
    SameMixed pp (simulateQ (fun b => simulateQ (selectedImpl pp) (markedFindHash b)) p)
      (liftM (simulateQ mixedHash p)) := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa using (SameMixed.pure (pp := pp) a)
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, liftM_bind]
    exact (mixed_hash pp q).bind ih

private theorem verify_sim {ι : Type} {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (H : ByteArray → OracleComp spec (Vector UInt8 32))
    (pk : PublicKey) (msg : Message) (sig : Signature) :
    simulateQ impl (verifyWith H pk msg sig) =
      verifyWith (fun b => simulateQ impl (H b)) pk msg sig :=
  verifyWith_map_monad (fun {_} p => simulateQ impl p) (fun _ => simulateQ_pure impl _)
    (fun _ _ => simulateQ_bind impl _ _) H pk msg sig

/-- The accepted and refused verifier use the same physical cap and previous graph state. -/
theorem mixed_verifier (pp : PublicParam) (pk : PublicKey) (candidate : Forgery) :
    SameMixed pp (simulateQ (selectedImpl pp) (simulateQ (mark (fun _ => True))
      (verifyWith (hashOf sourcePass) pk candidate.message candidate.signature)))
      (liftM (verifyWith mixedHash pk candidate.message candidate.signature)) := by
  let body := verifyWith byteQuery pk candidate.message candidate.signature
  have all := byte_calls pp body
  unfold body at all
  simp only [verify_sim, byteQuery, simulateQ_spec_query] at all
  simp only [verify_sim, hash_chosen (fun _ => True) _ trivial]
  exact all

/-- The honest grind spends one physical unit on every attempted digest, even if it rejects. -/
theorem mixed_finder (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : Nat) :
    SameMixed pp (simulateQ (selectedImpl pp)
      (Xmss.Internal.findCodeword markedFindHash pp l e msg base c fuel))
      (liftM (Xmss.Internal.findCodeword mixedHash pp l e msg base c fuel)) := by
  have all := byte_calls pp (Xmss.Internal.findCodeword byteQuery pp l e msg base c fuel)
  have liftFinder {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
      (h : QueryImpl spec m) (H : ByteArray → OracleComp spec (Vector UInt8 32)) :
      simulateQ h (Xmss.Internal.findCodeword H pp l e msg base c fuel) =
        Xmss.Internal.findCodeword (fun b => simulateQ h (H b)) pp l e msg base c fuel :=
    findCodeword_map_monad (fun {_} p => simulateQ h p) (fun _ => simulateQ_pure h _)
      (fun _ _ => simulateQ_bind h _ _) H pp l e msg base c fuel
  simp only [liftFinder, byteQuery, simulateQ_spec_query] at all
  rw [liftFinder]
  exact all

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

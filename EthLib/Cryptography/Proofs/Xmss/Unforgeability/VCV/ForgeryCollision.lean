module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerComparison
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ReleaseCoherence
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealClient
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CanonicalPath

/-!
# A fresh accepted signature gives a same-key message collision

The upper signing key signs the bottom tree root.

See the leanXMSS draft, sections "WOTS+C", "The scheme" and "Security".

Following the upper signature first recovers that root or a collision.

Following the lower signature next recovers the actual signed reply or a second collision.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography Constants HashSig TwoLayerGraph Honest VerifierProbe OracleSpec OracleComp
open ChainGraph (digestEquiv)

/-- A candidate message query collides with a different query from an actual signed reply. -/
def SignedCollision (pp : PublicParam) (st : SharedState) (obs : Outcome) : Prop :=
  let sig := obs.candidate.signature
  ∃ req issued, (req,.ok issued) ∈ obs.log ∧
    ((req.leafIndex = sig.leafIndex ∧ SameKeyCollision pp st .bottom sig.leafIndex.toNat
      (packBytes obs.candidate.message) (packBytes req.message) sig.bottom issued.bottom) ∨
    (bottomTree req.leafIndex = bottomTree sig.leafIndex ∧ ∃ candidateRoot signedRoot,
      layerRoot (hashAt pp st) pp .bottom sig.leafIndex.toNat (packBytes obs.candidate.message)
        sig.bottom = some (some candidateRoot) ∧
      st.2 (.inr (.inl (.bottom,LayerGraph.treeRole LAYER_HEIGHT (bottomTree sig.leafIndex)))) =
        some (digestEquiv signedRoot) ∧ SameKeyCollision pp st .top (bottomTree sig.leafIndex)
          (packBytes candidateRoot) (packBytes signedRoot) sig.top issued.top))

private theorem short_digit {d : Digest} {x : Vector (Fin CHAIN_LENGTH) V}
    (accepted : codeword? d = some x) : ∃ i : Fin V, x[i].val < CHAIN_LENGTH - 1 := by
  by_contra! terminal
  have lower := Finset.sum_le_sum (s := Finset.univ) (fun i _ => terminal i)
  rw [sum_of_codeword accepted] at lower
  norm_num [V, CHAIN_LENGTH, TARGET_SUM] at lower

private theorem top_index (i : LeafIndex) : bottomTree i / 2 ^ LAYER_HEIGHT = 0 := by
  have size := i.toNat_lt_size
  change i.toNat < 4294967296 at size
  change i.toNat / 65536 / 65536 = 0
  omega

private theorem contains_signed {raw : RawLog} {f : Forgery} {req : SignRequest} {sig : Signature}
    (member : (req,.ok sig) ∈ raw) (msg : f.message = req.message)
    (idx : f.signature.leafIndex = sig.leafIndex)
    (bottom : f.signature.bottom = sig.bottom) (top : f.signature.top = sig.top) :
    Contains (eraseLog raw) f := by
  refine ⟨⟨req,some sig⟩, List.mem_map.mpr ⟨(req,.ok sig), member, rfl⟩, msg.symm, ?_⟩
  have same : f.signature = sig := by
    cases f with
    | mk m a =>
      cases a
      cases sig
      dsimp only at idx bottom top ⊢
      cases idx
      cases bottom
      cases top
      rfl
  rw [same]

attribute [local irreducible] graph mixedGame guardedGraph layerRoot messageDigest simulateQ

/-- Trace a fresh accepted forgery in the capped game to a colliding signing query. -/
theorem forgery_collision (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    (obs : Outcome) (out : ResidualCache pp) (t : DeferredState) (last : SharedState)
    (actual : (some (obs,out),t) ∈ support ((simulateQ (graph pp).deferredImpl
      (guardedGraph left ((mixedGame pp A).run r))).run ((∅,∅),[])))
    (win : wins obs = true) (later : t.1 ≤ last) (clean : ¬(graph pp).Conflict last)
    (safe : ¬(TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project last)) :
    SignedCollision pp last obs := by
  have ok : (Valid (eraseLog obs.log) ∧ ¬Contains (eraseLog obs.log) obs.candidate) ∧
      obs.verified = true := by
    simpa only [wins, Bool.and_eq_true, decide_eq_true_eq] using win
  let sig := obs.candidate.signature
  obtain ⟨b, bot, top, lowOpens, highOpens⟩ := accepted_openings pp A left r obs out t last actual
    ok.2 later clean
  have facts := signed_history pp A left r _ obs out t actual last later
  have anchored := (mixed_public_root pp A left r _ obs out t actual last later).2
  have root : AtPosition last .top ⟨LAYER_HEIGHT, bottomTree sig.leafIndex / 2 ^ LAYER_HEIGHT⟩
      obs.key.root := by
    rw [top_index]
    exact anchored
  obtain ⟨d, x, readTop, parsed, values, path⟩ := verified_layer_rows pp last .top
    (bottomTree sig.leafIndex) (packBytes b) sig.top obs.key.root safe top root
  obtain ⟨a, sa, signedRoot, y, memA, keyA, saved, issued, earlier⟩ :=
    top_word sig.leafIndex facts later clean highOpens
      (Option.bind_eq_some_iff.mpr ⟨d,readTop,parsed⟩)
      (fun i _ => values i) (short_digit parsed)
  obtain ⟨d', readSigned, parsedSigned⟩ := Option.bind_eq_some_iff.mp (issued.decoded clean)
  rcases compare_layer pp last out .top _ _ _ _ _ x y d d' readTop readSigned parsed parsedSigned
      earlier values path issued with clash | ⟨sameMsg, topSig⟩
  · exact ⟨a,sa,memA,Or.inr ⟨keyA,b,signedRoot,bot,saved,clash⟩⟩
  · have sameRoot := EthLib.Base.packBytes_injective sameMsg
    subst signedRoot
    obtain ⟨d, x, readBot, parsed, values, path⟩ := verified_layer_rows pp last .bottom
      sig.leafIndex.toNat (packBytes obs.candidate.message) sig.bottom b safe bot saved
    obtain ⟨req, reply, y, mem, key, issued, earlier⟩ :=
      bottom_word facts ok.1.1 later clean lowOpens
      (Option.bind_eq_some_iff.mpr ⟨d,readBot,parsed⟩) (fun i _ => values i) (short_digit parsed)
    rw [key] at issued
    obtain ⟨d', readSigned, parsedSigned⟩ := Option.bind_eq_some_iff.mp (issued.decoded clean)
    rcases compare_layer pp last out .bottom _ _ _ _ _ x y d d' readBot readSigned
        parsed parsedSigned
        earlier values path issued with clash | ⟨sameMsg, lowSig⟩
    · exact ⟨req,reply,mem,Or.inl ⟨key,clash⟩⟩
    · have topKey : bottomTree a.leafIndex = bottomTree req.leafIndex := by rw [key]; exact keyA
      have sameTop := ((facts a sa memA).same_top (facts req reply mem) topKey clean).1
      exact (ok.1.2 (contains_signed mem (EthLib.Base.packBytes_injective sameMsg)
        (key.symm.trans (facts req reply mem).1.symm) lowSig (topSig.trans sameTop))).elim

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

module

public import EthLib.Cryptography.Merkle.Tree
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Proofs: how many calls a Merkle climb makes

A climb calls its node hash once per sibling, whatever oracle the hash queries.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

open OracleSpec OracleComp

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p] {α : Type}
  {hash : Position → α → α → OracleComp spec α}

/-- A climb costs one hash per sibling. -/
theorem isQueryBoundP_climb (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) :
    ∀ (siblings : List α) (q : Position) (current : α),
      IsQueryBoundP (climb hash q current siblings) p siblings.length
  | [], _, _ => isQueryBoundP_pure _ _ _
  | _ :: rest, q, current => by
    rw [climb]
    refine (isQueryBoundP_bind (hhash _ _ _) fun _ _ =>
      isQueryBoundP_climb hhash rest _ _).mono ?_
    simp only [List.length_cons]
    omega

end EthLib.Cryptography.Merkle

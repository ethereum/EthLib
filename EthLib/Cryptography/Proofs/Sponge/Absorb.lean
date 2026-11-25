module

public import EthLib.Cryptography.Proofs.Indifferentiability
public import EthLib.Cryptography.Proofs.Sponge.Basic

/-!
# Proofs: the sponge's calls of the permutation

Run in the permutation model, the sponge asks the permutation at most once per absorbed block.

Answered by an oracle, those calls are the sponge over the oracle's forward answers.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec LazyPermutation

variable {Dg E C : Type} [XorOp Dg] [XorOp E]

/-- Running the sponge's calls of the permutation is the sponge over the forward answers. -/
theorem simulateQ_absorbAll {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (unifSpec + PermSpec (SpongeState Dg E C)) m)
    (s : SpongeState Dg E C) (bs : List (Dg × E)) :
    simulateQ impl (absorbAll (fun x => (liftM ((unifSpec + PermSpec (SpongeState Dg E C)).query
      (.inr (.inl x))) : PermComp (SpongeState Dg E C) _)) s bs) =
      absorbAll (fun x => impl (.inr (.inl x))) s bs := by
  induction bs generalizing s with
  | nil => simp [absorbAll]
  | cons B bs ih => simp [absorbAll_cons, ih]

/-- The sponge asks the permutation at most once per block. -/
theorem isQueryBoundP_absorbAll (s : SpongeState Dg E C) (bs : List (Dg × E)) :
    IsQueryBoundP (absorbAll (fun x => (liftM ((unifSpec + PermSpec (SpongeState Dg E C)).query
      (.inr (.inl x))) : PermComp (SpongeState Dg E C) _)) s bs) (·.isRight = true)
      bs.length := by
  induction bs generalizing s with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons B bs ih =>
    rw [absorbAll_cons, List.length_cons, add_comm]
    exact isQueryBoundP_bind ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
      fun y _ => ih y

end EthLib.Cryptography.Sponge

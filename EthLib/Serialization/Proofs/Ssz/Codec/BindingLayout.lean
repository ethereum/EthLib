import EthLib.Serialization.Proofs.Ssz.Codec.BindingTrace

/-! Successful value computations expose their layouts without assuming layout injectivity. -/

namespace EthLib.Serialization.Ssz
open CommitmentTree

/-- A successful computation uses every leaf its actual layout materializes. -/
theorem valueTreeAt_view {budget : Nat} {shape : Desc} {value : Value} {tree : CommitmentTree}
    (success : valueTreeAt (budget + 1) shape value = .ok tree) :
    ∃ layout trees, merkleLayout shape value = .ok layout ∧
      layoutTreesAt budget layout = .ok trees ∧
      (∀ capacity, layout.limit = some capacity → trees.size ≤ capacity) ∧
      tree = (content trees layout.limit).withMixin layout.mixin := by
  -- Overall success excludes both an invalid layout and a failed nested computation.
  cases laid : merkleLayout shape value with
  | error fault => simp [valueTreeAt, laid, Bind.bind, Except.bind] at success
  | ok layout =>
    -- Each selected position must have produced its own finite computation.
    cases materialized : layoutTreesAt budget layout with
    | error fault => simp [valueTreeAt, laid, materialized, Bind.bind, Except.bind] at success
    | ok trees =>
      refine ⟨layout, trees, rfl, materialized, ?_⟩
      -- A bounded tree succeeds only when its capacity includes every materialized position.
      cases limit : layout.limit <;>
        simp [valueTreeAt, laid, materialized, limit, Bind.bind, Except.bind, pure, Except.pure,
          content, throw, throwThe, MonadExceptOf.throw] at success ⊢
      · exact success.symm
      · split at success <;> simp_all

end EthLib.Serialization.Ssz

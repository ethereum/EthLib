module

public import EthLib.Serialization.Proofs.Ssz.Merkle.Gindex
public import EthLib.Serialization.Ssz.Type.Paths

/-! Type paths compose relative generalized indices and stop at mixing words. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- An empty path selects the current root. -/
@[simp] theorem getGeneralizedIndex_nil (shape : Desc) : getGeneralizedIndex shape [] = .ok 1 := rfl

/-- A nonterminal step resolves the remaining path inside its child before splicing the indices. -/
theorem getGeneralizedIndex_cons {shape child : Desc} {step : PathStep} {index : Nat}
    (resolved : shape.resolveStep step = .ok (index, some child)) (rest : List PathStep) :
    getGeneralizedIndex shape (step :: rest) =
      (getGeneralizedIndex child rest >>= gindexConcat index) := by
  -- Resolving a child leaves the remaining relative path to be joined beneath that child.
  simp only [getGeneralizedIndex, resolved, Bind.bind, Except.bind]

/-- A mixing-word step terminates at its relative node. -/
theorem getGeneralizedIndex_terminal {shape : Desc} {step : PathStep} {index : Nat}
    (resolved : shape.resolveStep step = .ok (index, none)) :
    getGeneralizedIndex shape [step] = .ok index := by
  -- A terminal step succeeds only because there is no suffix left to traverse.
  simp [getGeneralizedIndex, resolved, Bind.bind, Except.bind, pure, Except.pure]

/-- A path cannot continue inside a mixing word. -/
theorem getGeneralizedIndex_after_terminal {shape : Desc} {step next : PathStep} {index : Nat}
    (resolved : shape.resolveStep step = .ok (index, none)) (rest : List PathStep) :
    getGeneralizedIndex shape (step :: next :: rest) = .error .noPartsMixin := by
  -- A length, selector, or active-fields word has no addressable child type.
  simp [getGeneralizedIndex, resolved, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A terminal path step always names the right-hand mixing word. -/
theorem resolveStep_terminal_index {shape : Desc} {step : PathStep} {index : Nat}
    (resolved : shape.resolveStep step = .ok (index, none)) : index = 3 := by
  -- Only recognized mixing words return no child type, and each occupies the root’s right child.
  cases shape <;> cases step <;>
    simp only [Desc.resolveStep, Bind.bind, Except.bind, Pure.pure, Except.pure] at resolved
  all_goals repeat first | split at resolved | cases resolved
  all_goals first | rfl | exact (congrArg Prod.fst (Except.ok.inj resolved)).symm

/-- Every successful type path names a real generalized index. -/
theorem getGeneralizedIndex_positive (shape : Desc) (path : List PathStep) (index : Nat)
    (resolved : getGeneralizedIndex shape path = .ok index) : 1 ≤ index := by
  -- An empty path names one.
  -- A nonempty path either terminates at three or joins valid child indices.
  cases path with
  | nil => cases resolved; decide
  | cons step rest =>
    -- A failed first step cannot produce a successful full path.
    cases first : shape.resolveStep step with
    | error fault => simp [getGeneralizedIndex, first, Bind.bind, Except.bind] at resolved
    | ok target =>
      obtain ⟨head, _ | child⟩ := target
      -- A terminal mixing word has the fixed generalized index three.
      · cases rest <;> simp [getGeneralizedIndex, first, Bind.bind, Except.bind,
          pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at resolved
        have := resolveStep_terminal_index first
        omega
      -- A successful nested path finishes with a valid generalized-index splice.
      · rw [getGeneralizedIndex_cons first] at resolved
        cases suffix : getGeneralizedIndex child rest <;> simp [suffix, Bind.bind, Except.bind] at resolved
        exact gindexConcat_positive resolved

/-- A resolved child followed by any resolved suffix selects their spliced generalized index. -/
theorem getGeneralizedIndex_step {shape child : Desc} {step : PathStep} {head tail whole : Nat}
    {rest : List PathStep} (resolved : shape.resolveStep step = .ok (head, some child))
    (suffix : getGeneralizedIndex child rest = .ok tail)
    (joined : gindexConcat head tail = .ok whole) :
    getGeneralizedIndex shape (step :: rest) = .ok whole := by
  -- The first step and suffix have already succeeded, leaving only their prescribed splice.
  rw [getGeneralizedIndex_cons resolved, suffix]
  exact joined

/-- A path prefix ending at a child type, together with its composed node index. -/
inductive PathThrough : Desc → List PathStep → Desc → Nat → Prop where
  /-- An empty prefix leaves the type and its root unchanged. -/
  | nil (shape : Desc) : PathThrough shape [] shape 1
  /-- A child step composes its relative index with the remaining prefix. -/
  | cons {shape child target : Desc} {step : PathStep} {rest : List PathStep}
      {head tail whole : Nat}
      (resolved : shape.resolveStep step = .ok (head, some child))
      (through : PathThrough child rest target tail)
      (joined : gindexConcat head tail = .ok whole) :
      PathThrough shape (step :: rest) target whole

end EthLib.Serialization.Ssz

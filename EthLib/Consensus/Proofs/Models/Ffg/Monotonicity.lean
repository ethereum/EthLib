module

public import EthLib.Consensus.Proofs.Models.Ffg.Model

import EthLib.Consensus.Proofs.Models.Ffg.PlausibleLiveness

/-!
# Proofs: adding votes and allowed weights preserves Casper FFG finality

A slack link needs one allowed weight function under which its voters meet the bound.

Adding allowed weights keeps that witness, and adding votes can only increase its voting stake.

The links then keep their justification and finalization derivations.

Two such derivations with the same validator sets and genesis fit their unions of votes and weights.

The definitions of justification and finalization follow Gasper §4.4 and Definition 4.9.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus.Models.Ffg

variable {ν β : Type*} {V U : Checkpoint β → Finset ν}
  {W W' : Checkpoint β → Set (ν → ℕ)} {votes votes' : Set (Vote ν β)}

variable [Preorder β] {genesis : β}

/-- Adding votes and allowed weights keeps a slack link with the same validator sets. -/
theorem SlackLink.mono {s t : Checkpoint β}
    (linked : SlackLink V U W votes s t)
    (weights : ∀ c, W c ⊆ W' c) (more : votes ⊆ votes') : SlackLink V U W' votes' s t := by
  obtain ⟨epochs, chain, w, allowed, bound⟩ := linked
  refine ⟨epochs, chain, w, weights t allowed, bound.trans ?_⟩
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 3 (stake_mono (signers_mono (U := V t) more s t))) _

/-- Adding votes and allowed weights keeps a slack-justified checkpoint. -/
theorem SlackJustified.mono {c : Checkpoint β}
    (justified : SlackJustified V U W genesis votes c)
    (weights : ∀ c, W c ⊆ W' c) (more : votes ⊆ votes') :
    SlackJustified V U W' genesis votes' c :=
  justified.imp fun linked => linked.mono weights more

/-- Adding votes and allowed weights keeps a slack-finalized checkpoint. -/
theorem SlackFinalized.mono {c : Checkpoint β}
    (finalized : SlackFinalized V U W genesis votes c)
    (weights : ∀ c, W c ⊆ W' c) (more : votes ⊆ votes') :
    SlackFinalized V U W' genesis votes' c :=
  finalized.imp fun linked => linked.mono weights more

/-- Two slack-finalized checkpoints remain so under the unions of their votes and allowed weights.

The validator sets, second sets and genesis are the same in both derivations. -/
theorem SlackFinalized.union {c₁ c₂ : Checkpoint β}
    (first : SlackFinalized V U W genesis votes c₁)
    (second : SlackFinalized V U W' genesis votes' c₂) :
    SlackFinalized V U (fun c => W c ∪ W' c) genesis (votes ∪ votes') c₁ ∧
      SlackFinalized V U (fun c => W c ∪ W' c) genesis (votes ∪ votes') c₂ :=
  ⟨first.mono (fun _ => Set.subset_union_left) Set.subset_union_left,
    second.mono (fun _ => Set.subset_union_right) Set.subset_union_right⟩

end EthLib.Consensus.Models.Ffg

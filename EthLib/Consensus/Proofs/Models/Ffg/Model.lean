module

public import EthLib.Consensus.Proofs.Models.Stake

/-!
# Casper FFG: the model

The model follows Casper FFG §2, [arXiv 1710.09437v4](https://arxiv.org/abs/1710.09437v4).

Checkpoints follow Gasper §4.1, [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).

There, a checkpoint is an epoch boundary pair: a block with an epoch.

A preorder on blocks gives the chains: `a ≤ b` means that `a` is in the chain of `b`.

Each checkpoint `c` has its own validator set `V c`, as Gasper §8.6 gives each block its own set.

So one epoch can have two sets on two conflicting branches.

A supermajority link counts only the stake of the validators of its target checkpoint.

It weighs them by the weights of its target.

Gasper §8.6 counts the stake of the attestation epoch of a pair, which Gasper §4.1 defines.

Each checkpoint `c` also has its own weights `w c`, the stake of each validator for its links.

Gasper §8.6 keeps one stake for each validator instead.

A balance can change between two checkpoints, so the weights may differ from one to the next.

Constant weights give the model of Gasper §8.6.

A constant set and constant weights give the model of Casper FFG §2 and Gasper §4.

A slack link weakens a supermajority link by a second set `U c` for each checkpoint `c`.

A chain can count the votes for `c` against the stake of a later set `U c`, not of `V c`.

A validator of `V c` that left before `U c` then counts as a voter, but not in the total.

The slack is the stake of such validators, the set `E(V c, U c)` of Gasper §8.6, Definition 8.1.

Gasper has no slack: there each quorum holds two thirds of its own set.

Accountable safety then loses twice the slack of each of the two links that it finds.

The slack of earlier links does not add up.

Nothing ties `U` to `V`: with an empty second set, every ordered link is a slack link.

So the safety bounds say something only when the slack is bounded, as the exit churn bounds it.

With `U = V` the slack is zero, and a slack link is a supermajority link.

Justification and finalization take the kind of link as a parameter.

Supermajority links and slack links are two kinds.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Ffg

/-- A checkpoint: a block and an epoch.

One block can stand for several epochs when the epochs after it have no block.

A checkpoint of Casper FFG is a block with its checkpoint height as the epoch. -/
@[ext]
structure Checkpoint (β : Type*) where
  /-- The block. -/
  block : β
  /-- The epoch. -/
  epoch : ℕ

/-- A vote: a validator signs a link from a source checkpoint to a target checkpoint. -/
@[ext]
structure Vote (ν β : Type*) where
  /-- The validator that signs the vote. -/
  validator : ν
  /-- The checkpoint that the link starts from. -/
  source : Checkpoint β
  /-- The checkpoint that the link ends at. -/
  target : Checkpoint β

variable {ν β : Type*}

open scoped Classical in
/-- The validators of `V` that vote for the link from `s` to `t`. -/
noncomputable def signers (V : Finset ν) (votes : Set (Vote ν β)) (s t : Checkpoint β) :
    Finset ν :=
  {v ∈ V | ⟨v, s, t⟩ ∈ votes}

/-- Two distinct votes with one target epoch break the first slashing condition. -/
def DoubleVote (x y : Vote ν β) : Prop :=
  x ≠ y ∧ x.target.epoch = y.target.epoch

/-- The first vote surrounds the second, which breaks the second slashing condition.

For votes from `s₁` to `t₁` and from `s₂` to `t₂`, the epochs satisfy `s₁ < s₂ < t₂ < t₁`. -/
def SurroundVote (x y : Vote ν β) : Prop :=
  x.source.epoch < y.source.epoch ∧ y.source.epoch < y.target.epoch ∧
    y.target.epoch < x.target.epoch

/-- A validator is slashable when it signs two votes that break a slashing condition. -/
def Slashable (votes : Set (Vote ν β)) (v : ν) : Prop :=
  ∃ x ∈ votes, ∃ y ∈ votes, x.validator = v ∧ y.validator = v ∧
    (DoubleVote x y ∨ SurroundVote x y)

open scoped Classical in
/-- Slashable validators hold at least one third of the stake of `V`.

Gasper calls such a view `(1/3)`-slashable. -/
def OneThirdSlashable (V : Finset ν) (w : ν → ℕ) (votes : Set (Vote ν β)) : Prop :=
  stake w V ≤ 3 * stake w {v ∈ V | Slashable votes v}

variable [Preorder β]

/-- Two blocks conflict when neither is in the chain of the other. -/
def Conflicting (a b : β) : Prop :=
  ¬a ≤ b ∧ ¬b ≤ a

/-- A supermajority link from `s` to `t`.

The source comes before the target, in epoch and in the chain of the target.

Casper FFG §2 ignores a vote that breaks this order.

Validators of the set of the target vote for the link.

Under the weights of the target, they hold at least two thirds of the stake of that set. -/
def SupermajorityLink (V : Checkpoint β → Finset ν) (w : Checkpoint β → ν → ℕ)
    (votes : Set (Vote ν β)) (s t : Checkpoint β) : Prop :=
  s.epoch < t.epoch ∧ s.block ≤ t.block ∧
    2 * stake (w t) (V t) ≤ 3 * stake (w t) (signers (V t) votes s t)

open scoped Classical in
/-- A slack link from `s` to `t`: a supermajority link up to a slack.

The source comes before the target, in epoch and in the chain of the target.

The slack is the stake of the set `V t` outside the set `U t`.

Under the weights of `t`, twice the stake of `V t` is at most three times the stake of its voters.

That bound adds twice the slack. -/
def SlackLink (V U : Checkpoint β → Finset ν) (w : Checkpoint β → ν → ℕ)
    (votes : Set (Vote ν β)) (s t : Checkpoint β) : Prop :=
  s.epoch < t.epoch ∧ s.block ≤ t.block ∧
    2 * stake (w t) (V t) ≤ 3 * stake (w t) (signers (V t) votes s t) + 2 * stake (w t) (V t \ U t)

/-- The checkpoints justified by a kind of link.

The genesis block at epoch 0 is justified.

A link from a justified checkpoint justifies its target. -/
inductive JustifiedBy (link : Checkpoint β → Checkpoint β → Prop) (genesis : β) :
    Checkpoint β → Prop
  /-- The genesis checkpoint is justified. -/
  | root : JustifiedBy link genesis ⟨genesis, 0⟩
  /-- A link from a justified checkpoint justifies its target. -/
  | link {s t : Checkpoint β} : JustifiedBy link genesis s → link s t → JustifiedBy link genesis t

/-- The checkpoint `c` is `k`-finalized by a kind of link, as in Gasper Definition 4.9.

Blocks `b 0, ..., b k` start at the block of `c`, and each one is in the chain of the next.

The checkpoints `(b i, e + i)` for `i < k` are justified, where `e` is the epoch of `c`.

A link goes from `c` to `(b k, e + k)`.

Gasper also asks that these checkpoints are epoch boundary pairs.

The model drops that condition.

It then finalizes more checkpoints, so its safety theorem is stronger. -/
def KFinalizedBy (link : Checkpoint β → Checkpoint β → Prop) (genesis : β) (k : ℕ)
    (c : Checkpoint β) : Prop :=
  ∃ b : ℕ → β, b 0 = c.block ∧ (∀ i < k, b i ≤ b (i + 1)) ∧
    (∀ i < k, JustifiedBy link genesis ⟨b i, c.epoch + i⟩) ∧ link c ⟨b k, c.epoch + k⟩

/-- The checkpoints finalized by a kind of link.

They are the genesis checkpoint, and every `k`-finalized one with `k ≥ 1`.

The case `k = 1` is the finalization of Casper FFG §2. -/
def FinalizedBy (link : Checkpoint β → Checkpoint β → Prop) (genesis : β)
    (c : Checkpoint β) : Prop :=
  c = ⟨genesis, 0⟩ ∨ ∃ k, 1 ≤ k ∧ KFinalizedBy link genesis k c

/-- The checkpoints justified by supermajority links. -/
abbrev Justified (V : Checkpoint β → Finset ν) (w : Checkpoint β → ν → ℕ) (genesis : β)
    (votes : Set (Vote ν β)) : Checkpoint β → Prop :=
  JustifiedBy (SupermajorityLink V w votes) genesis

/-- The checkpoints `k`-finalized by supermajority links. -/
abbrev KFinalized (V : Checkpoint β → Finset ν) (w : Checkpoint β → ν → ℕ) (genesis : β)
    (votes : Set (Vote ν β)) (k : ℕ) : Checkpoint β → Prop :=
  KFinalizedBy (SupermajorityLink V w votes) genesis k

/-- The checkpoints finalized by supermajority links. -/
abbrev Finalized (V : Checkpoint β → Finset ν) (w : Checkpoint β → ν → ℕ) (genesis : β)
    (votes : Set (Vote ν β)) : Checkpoint β → Prop :=
  FinalizedBy (SupermajorityLink V w votes) genesis

/-- The checkpoints justified by slack links. -/
abbrev SlackJustified (V U : Checkpoint β → Finset ν) (w : Checkpoint β → ν → ℕ) (genesis : β)
    (votes : Set (Vote ν β)) : Checkpoint β → Prop :=
  JustifiedBy (SlackLink V U w votes) genesis

/-- The checkpoints finalized by slack links. -/
abbrev SlackFinalized (V U : Checkpoint β → Finset ν) (w : Checkpoint β → ν → ℕ) (genesis : β)
    (votes : Set (Vote ν β)) : Checkpoint β → Prop :=
  FinalizedBy (SlackLink V U w votes) genesis

variable {V U : Checkpoint β → Finset ν} {w : Checkpoint β → ν → ℕ} {votes : Set (Vote ν β)}
  {link link' : Checkpoint β → Checkpoint β → Prop} {genesis : β}

/-- With the validator sets as second sets, a slack link is a supermajority link. -/
theorem slackLink_self : SlackLink V V w votes = SupermajorityLink V w votes := by
  funext s t
  simp only [SlackLink, SupermajorityLink, Finset.sdiff_self, stake_empty, Nat.mul_zero,
    Nat.add_zero]

/-- A supermajority link is a slack link for every choice of second sets. -/
theorem SupermajorityLink.slackLink (U : Checkpoint β → Finset ν) {s t : Checkpoint β}
    (h : SupermajorityLink V w votes s t) : SlackLink V U w votes s t :=
  ⟨h.1, h.2.1, h.2.2.trans (Nat.le_add_right _ _)⟩

omit [Preorder β] in
/-- A weaker kind of link justifies more checkpoints. -/
theorem JustifiedBy.imp (weaker : ∀ {s t}, link s t → link' s t) {c : Checkpoint β}
    (h : JustifiedBy link genesis c) : JustifiedBy link' genesis c := by
  induction h with
  | root => exact .root
  | link _ hl ih => exact .link ih (weaker hl)

/-- A weaker kind of link finalizes more checkpoints. -/
theorem FinalizedBy.imp (weaker : ∀ {s t}, link s t → link' s t) {c : Checkpoint β}
    (h : FinalizedBy link genesis c) : FinalizedBy link' genesis c := by
  rcases h with rfl | ⟨k, hk, b, hb, hchain, hj, hl⟩
  · exact .inl rfl
  · exact .inr ⟨k, hk, b, hb, hchain, fun i hi => (hj i hi).imp weaker, weaker hl⟩

/-- A slack link whose target set lies in its second set is a supermajority link.

The slack is then zero. -/
theorem SlackLink.supermajorityLink {s t : Checkpoint β} (inside : V t ⊆ U t)
    (h : SlackLink V U w votes s t) : SupermajorityLink V w votes s t := by
  classical
  refine ⟨h.1, h.2.1, ?_⟩
  have empty : V t \ U t = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr inside
  have := h.2.2
  rw [empty, stake_empty] at this
  simpa using this

/-- A supermajority link raises the epoch, and its source block is in the chain of its target. -/
theorem SupermajorityLink.ordered {s t : Checkpoint β} (h : SupermajorityLink V w votes s t) :
    s.epoch < t.epoch ∧ s.block ≤ t.block :=
  ⟨h.1, h.2.1⟩

/-- A slack link raises the epoch, and its source block is in the chain of its target. -/
theorem SlackLink.ordered {s t : Checkpoint β} (h : SlackLink V U w votes s t) :
    s.epoch < t.epoch ∧ s.block ≤ t.block :=
  ⟨h.1, h.2.1⟩

/-- With the validator sets as second sets, slack-justified means justified. -/
theorem slackJustified_self : SlackJustified V V w genesis votes = Justified V w genesis votes := by
  rw [SlackJustified, slackLink_self]

/-- With the validator sets as second sets, slack-finalized means finalized. -/
theorem slackFinalized_self : SlackFinalized V V w genesis votes = Finalized V w genesis votes := by
  rw [SlackFinalized, slackLink_self]

/-- A finalized checkpoint is slack-finalized for every choice of second sets. -/
theorem Finalized.slackFinalized (U : Checkpoint β → Finset ν) {c : Checkpoint β}
    (h : Finalized V w genesis votes c) : SlackFinalized V U w genesis votes c :=
  FinalizedBy.imp (SupermajorityLink.slackLink U) h

end EthLib.Consensus.Models.Ffg

module

public import EthLib.Consensus.Proofs.Models.Stake

/-!
# Casper FFG: the model

Checkpoints, votes, slashing conditions, links, justification and finalization.

The model follows Casper FFG §2, [arXiv 1710.09437v4](https://arxiv.org/abs/1710.09437v4).

Checkpoints follow Gasper §4.1, [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus.Models.Ffg

/-- A checkpoint: a block and an epoch, an epoch boundary pair of Gasper §4.1.

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

Take votes from `s_1` to `t_1` and from `s_2` to `t_2`.

Their epochs satisfy `s_1 < s_2 < t_2 < t_1`. -/
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

-- A preorder on blocks gives the chains: `a ≤ b` means that `a` is in the chain of `b`.
variable [Preorder β]

/-- Two blocks conflict when neither is in the chain of the other. -/
def Conflicting (a b : β) : Prop :=
  ¬a ≤ b ∧ ¬b ≤ a

/-- A supermajority link from `s` to `t`, with two thirds of the stake of the set of `t`. -/
def SupermajorityLink (V : Checkpoint β → Finset ν) (w : ν → ℕ) (votes : Set (Vote ν β))
    (s t : Checkpoint β) : Prop :=
  -- The source comes before the target, in epoch and in the chain of the target.
  --
  -- Casper FFG §2 ignores a vote that breaks this order.
  s.epoch < t.epoch ∧ s.block ≤ t.block ∧
    -- Validators of the set of the target vote for the link.
    --
    -- They hold at least two thirds of the stake of that set.
    --
    -- Each checkpoint `c` has its own set `V c`, as Gasper §8.6 gives each block its own set.
    --
    -- So one epoch can have two sets on two conflicting branches.
    --
    -- The link counts only the stake of the validators of its target checkpoint.
    --
    -- Gasper §8.6 counts the stake of the attestation epoch of a pair, which Gasper §4.1 defines.
    --
    -- One stake function `w` holds for every validator, as Gasper §8.6 assumes.
    --
    -- A constant set gives the model of Casper FFG §2 and Gasper §4, with one set for all votes.
    2 * stake w (V t) ≤ 3 * stake w (signers (V t) votes s t)

open scoped Classical in
/-- A slack link from `s` to `t`: a supermajority link up to a slack.

The slack is the stake of the set `V t` outside the set `U t`. -/
def SlackLink (V U : Checkpoint β → Finset ν) (W : Checkpoint β → Set (ν → ℕ))
    (votes : Set (Vote ν β)) (s t : Checkpoint β) : Prop :=
  -- The source comes before the target, in epoch and in the chain of the target.
  --
  -- Each checkpoint `c` has a set `W c` of weights, not one stake function.
  --
  -- The link holds when its bound holds under one choice `w` of weights in `W t`.
  --
  -- A balance can change from one checkpoint to the next, and between two branches.
  --
  -- Two branches can justify one checkpoint from two states, each with its own balances.
  --
  -- A set of weights holds them both, where a single weights function could not.
  --
  -- Nothing bounds `W`: with the zero weights in `W t`, every ordered link is a slack link.
  --
  -- So the bounds say something only when every choice in each set `W c` stays near a reference.
  s.epoch < t.epoch ∧ s.block ≤ t.block ∧ ∃ w ∈ W t,
    -- Under `w`, twice the stake of `V t` is at most three times that of its voters.
    --
    -- The slack, counted twice, weakens that bound.
    --
    -- A chain can count the votes for `t` against the stake of a later set `U t`, not of `V t`.
    --
    -- A validator of `V t` that left before `U t` then counts as a voter, but not in the total.
    --
    -- The slack is the stake of such validators.
    --
    -- They form the set `E(V t, U t)` of Gasper §8.6, Definition 8.1.
    --
    -- Gasper has no slack: there each quorum holds two thirds of its own set.
    --
    -- Accountable safety then loses twice the slack of each of the two links that it finds.
    --
    -- The slack of earlier links does not add up.
    --
    -- Nothing ties `U` to `V`: with an empty second set, every ordered link is a slack link.
    --
    -- So the safety bounds say something only when the slack is bounded.
    --
    -- The exit churn bounds it.
    2 * stake w (V t) ≤ 3 * stake w (signers (V t) votes s t) + 2 * stake w (V t \ U t)

/-- The checkpoints justified by a kind of link, such as supermajority links or slack links.

The genesis block at epoch 0 is justified.

A link from a justified checkpoint justifies its target. -/
inductive JustifiedBy (link : Checkpoint β → Checkpoint β → Prop) (genesis : β) :
    Checkpoint β → Prop
  /-- The genesis checkpoint is justified. -/
  | root : JustifiedBy link genesis ⟨genesis, 0⟩
  /-- A link from a justified checkpoint justifies its target. -/
  | link {s t : Checkpoint β} : JustifiedBy link genesis s → link s t → JustifiedBy link genesis t

/-- The checkpoint `c` is `k`-finalized by a kind of link, as in Gasper Definition 4.9.

Gasper also asks that its checkpoints are epoch boundary pairs; the model drops that condition.

It then finalizes more checkpoints, so its safety theorem is stronger. -/
def KFinalizedBy (link : Checkpoint β → Checkpoint β → Prop) (genesis : β) (k : ℕ)
    (c : Checkpoint β) : Prop :=
  -- Blocks `b 0, ..., b k` start at the block of `c`, and each one is in the chain of the next.
  ∃ b : ℕ → β, b 0 = c.block ∧ (∀ i < k, b i ≤ b (i + 1)) ∧
    -- The checkpoints `(b i, e + i)` for `i < k` are justified, where `e` is the epoch of `c`.
    --
    -- A link goes from `c` to `(b k, e + k)`.
    (∀ i < k, JustifiedBy link genesis ⟨b i, c.epoch + i⟩) ∧ link c ⟨b k, c.epoch + k⟩

/-- The checkpoints finalized by a kind of link.

They are the genesis checkpoint, and every `k`-finalized one with `k ≥ 1`.

The case `k = 1` is the finalization of Casper FFG §2. -/
def FinalizedBy (link : Checkpoint β → Checkpoint β → Prop) (genesis : β)
    (c : Checkpoint β) : Prop :=
  c = ⟨genesis, 0⟩ ∨ ∃ k, 1 ≤ k ∧ KFinalizedBy link genesis k c

/-- The checkpoints justified by supermajority links. -/
abbrev Justified (V : Checkpoint β → Finset ν) (w : ν → ℕ) (genesis : β)
    (votes : Set (Vote ν β)) : Checkpoint β → Prop :=
  JustifiedBy (SupermajorityLink V w votes) genesis

/-- The checkpoints `k`-finalized by supermajority links. -/
abbrev KFinalized (V : Checkpoint β → Finset ν) (w : ν → ℕ) (genesis : β)
    (votes : Set (Vote ν β)) (k : ℕ) : Checkpoint β → Prop :=
  KFinalizedBy (SupermajorityLink V w votes) genesis k

/-- The checkpoints finalized by supermajority links. -/
abbrev Finalized (V : Checkpoint β → Finset ν) (w : ν → ℕ) (genesis : β)
    (votes : Set (Vote ν β)) : Checkpoint β → Prop :=
  FinalizedBy (SupermajorityLink V w votes) genesis

/-- The checkpoints justified by slack links. -/
abbrev SlackJustified (V U : Checkpoint β → Finset ν) (W : Checkpoint β → Set (ν → ℕ))
    (genesis : β) (votes : Set (Vote ν β)) : Checkpoint β → Prop :=
  JustifiedBy (SlackLink V U W votes) genesis

/-- The checkpoints finalized by slack links. -/
abbrev SlackFinalized (V U : Checkpoint β → Finset ν) (W : Checkpoint β → Set (ν → ℕ))
    (genesis : β) (votes : Set (Vote ν β)) : Checkpoint β → Prop :=
  FinalizedBy (SlackLink V U W votes) genesis

variable {V U : Checkpoint β → Finset ν} {W : Checkpoint β → Set (ν → ℕ)} {w : ν → ℕ}
  {votes : Set (Vote ν β)}
  {link link' : Checkpoint β → Checkpoint β → Prop} {genesis : β}

/-- A slack link is a supermajority link when it has no slack and one stake function.

The second sets are then the validator sets, and each set of weights holds one function. -/
theorem slackLink_self : SlackLink V V (fun _ => {w}) votes = SupermajorityLink V w votes := by
  funext s t
  simp only [SlackLink, SupermajorityLink, Finset.sdiff_self, stake_empty, Nat.mul_zero,
    Nat.add_zero, Set.mem_singleton_iff, exists_eq_left]

/-- A supermajority link is a slack link for every choice of second sets.

Its stake function is then the weights of every checkpoint. -/
theorem SupermajorityLink.slackLink (U : Checkpoint β → Finset ν) {s t : Checkpoint β}
    (h : SupermajorityLink V w votes s t) : SlackLink V U (fun _ => {w}) votes s t :=
  ⟨h.1, h.2.1, w, rfl, h.2.2.trans (Nat.le_add_right _ _)⟩

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

/-- A justified checkpoint with a link to the next epoch is finalized, with `k = 1`.

The block of the target must be above that of the checkpoint. -/
theorem FinalizedBy.of_one {c t : Checkpoint β} (justified : JustifiedBy link genesis c)
    (order : c.block ≤ t.block) (epochs : t.epoch = c.epoch + 1) (linked : link c t) :
    FinalizedBy link genesis c := by
  refine .inr ⟨1, le_rfl, fun i => if i = 0 then c.block else t.block, rfl, ?_, ?_, ?_⟩
  · intro i small
    obtain rfl : i = 0 := by omega
    simpa using order
  · intro i small
    obtain rfl : i = 0 := by omega
    simpa using justified
  · have target : (⟨t.block, c.epoch + 1⟩ : Checkpoint β) = t := by
      rw [← epochs]
    simpa [target] using linked

/-- A justified checkpoint is finalized with `k = 2`.

The checkpoint of the next epoch must be justified, and a link must reach the epoch after.

The blocks of the three checkpoints must be in order. -/
theorem FinalizedBy.of_two {c m t : Checkpoint β} (justified : JustifiedBy link genesis c)
    (middle : JustifiedBy link genesis m) (first : c.block ≤ m.block) (second : m.block ≤ t.block)
    (middleEpoch : m.epoch = c.epoch + 1) (epochs : t.epoch = c.epoch + 2) (linked : link c t) :
    FinalizedBy link genesis c := by
  refine .inr ⟨2, by omega,
    fun i => if i = 0 then c.block else if i = 1 then m.block else t.block, rfl, ?_, ?_, ?_⟩
  · intro i small
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · simpa using first
    · simpa using second
  · intro i small
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · simpa using justified
    · have target : (⟨m.block, c.epoch + 1⟩ : Checkpoint β) = m := by
        rw [← middleEpoch]
      simpa [target] using middle
  · have target : (⟨t.block, c.epoch + 2⟩ : Checkpoint β) = t := by
      rw [← epochs]
    simpa [target] using linked

/-- A slack link with one stake function is a supermajority link when it has no slack.

That holds when its target set lies in its second set. -/
theorem SlackLink.supermajorityLink {s t : Checkpoint β} (inside : V t ⊆ U t)
    (h : SlackLink V U (fun _ => {w}) votes s t) : SupermajorityLink V w votes s t := by
  classical
  obtain ⟨epochs, chain, w', rfl, bound⟩ := h
  have empty : V t \ U t = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr inside
  rw [empty, stake_empty] at bound
  exact ⟨epochs, chain, by simpa using bound⟩

/-- A supermajority link raises the epoch, and its source block is in the chain of its target. -/
theorem SupermajorityLink.ordered {s t : Checkpoint β} (h : SupermajorityLink V w votes s t) :
    s.epoch < t.epoch ∧ s.block ≤ t.block :=
  ⟨h.1, h.2.1⟩

/-- A slack link raises the epoch, and its source block is in the chain of its target. -/
theorem SlackLink.ordered {s t : Checkpoint β} (h : SlackLink V U W votes s t) :
    s.epoch < t.epoch ∧ s.block ≤ t.block :=
  ⟨h.1, h.2.1⟩

/-- With no slack and one stake function, slack-justified means justified. -/
theorem slackJustified_self :
    SlackJustified V V (fun _ => {w}) genesis votes = Justified V w genesis votes := by
  rw [SlackJustified, slackLink_self]

/-- With no slack and one stake function, slack-finalized means finalized. -/
theorem slackFinalized_self :
    SlackFinalized V V (fun _ => {w}) genesis votes = Finalized V w genesis votes := by
  rw [SlackFinalized, slackLink_self]

/-- A finalized checkpoint is slack-finalized for every choice of second sets.

Its stake function is then the weights of every checkpoint. -/
theorem Finalized.slackFinalized (U : Checkpoint β → Finset ν) {c : Checkpoint β}
    (h : Finalized V w genesis votes c) : SlackFinalized V U (fun _ => {w}) genesis votes c :=
  FinalizedBy.imp (SupermajorityLink.slackLink U) h

end EthLib.Consensus.Models.Ffg

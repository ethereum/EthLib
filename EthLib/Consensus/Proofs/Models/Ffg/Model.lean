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

Gasper §8.6 counts the stake of the attestation epoch of a pair, which Gasper §4.1 defines.

One stake function `w` holds for every validator, as Gasper §8.6 assumes.

A constant set gives the model of Casper FFG §2 and Gasper §4, with one set for all votes.
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

They hold at least two thirds of the stake of that set. -/
def SupermajorityLink (V : Checkpoint β → Finset ν) (w : ν → ℕ) (votes : Set (Vote ν β))
    (s t : Checkpoint β) : Prop :=
  s.epoch < t.epoch ∧ s.block ≤ t.block ∧ 2 * stake w (V t) ≤ 3 * stake w (signers (V t) votes s t)

/-- The justified checkpoints.

The genesis block at epoch 0 is justified.

A supermajority link from a justified checkpoint justifies its target. -/
inductive Justified (V : Checkpoint β → Finset ν) (w : ν → ℕ) (genesis : β)
    (votes : Set (Vote ν β)) : Checkpoint β → Prop
  /-- The genesis checkpoint is justified. -/
  | root : Justified V w genesis votes ⟨genesis, 0⟩
  /-- A supermajority link from a justified checkpoint justifies its target. -/
  | link {s t : Checkpoint β} :
      Justified V w genesis votes s → SupermajorityLink V w votes s t →
        Justified V w genesis votes t

/-- The checkpoint `c` is `k`-finalized, as in Gasper Definition 4.9.

Blocks `b 0, ..., b k` start at the block of `c`, and each one is in the chain of the next.

The checkpoints `(b i, e + i)` for `i < k` are justified, where `e` is the epoch of `c`.

A supermajority link goes from `c` to `(b k, e + k)`.

Gasper also asks that these checkpoints are epoch boundary pairs.

The model drops that condition.

It then finalizes more checkpoints, so its safety theorem is stronger. -/
def KFinalized (V : Checkpoint β → Finset ν) (w : ν → ℕ) (genesis : β) (votes : Set (Vote ν β))
    (k : ℕ) (c : Checkpoint β) : Prop :=
  ∃ b : ℕ → β, b 0 = c.block ∧ (∀ i < k, b i ≤ b (i + 1)) ∧
    (∀ i < k, Justified V w genesis votes ⟨b i, c.epoch + i⟩) ∧
    SupermajorityLink V w votes c ⟨b k, c.epoch + k⟩

/-- The finalized checkpoints: the genesis checkpoint, and every `k`-finalized one with `k ≥ 1`.

The case `k = 1` is the finalization of Casper FFG §2. -/
def Finalized (V : Checkpoint β → Finset ν) (w : ν → ℕ) (genesis : β) (votes : Set (Vote ν β))
    (c : Checkpoint β) : Prop :=
  c = ⟨genesis, 0⟩ ∨ ∃ k, 1 ≤ k ∧ KFinalized V w genesis votes k c

end EthLib.Consensus.Models.Ffg

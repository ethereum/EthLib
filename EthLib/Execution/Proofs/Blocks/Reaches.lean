module

public import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: the chains that a chain reaches

A chain reaches another through blocks that each pass their transition.

An invariant of the state that every such block keeps holds in every chain that it reaches.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base (Fork)
open EthLib.Execution.State (State)
open EthLib.Execution.Transactions (Transaction)

/-- A chain reaches another through blocks that each pass their transition and meet `allowed`.

`allowed` sees the chain before the block, and the block with its fork.

Each block may pass it with or without the check of its seal. -/
inductive BlockChain.Reaches
    (allowed : BlockChain → (fork : Fork) → Block fork Transaction → Prop) :
    BlockChain → BlockChain → Prop
  /-- A chain reaches itself. -/
  | refl (chain : BlockChain) : BlockChain.Reaches allowed chain chain
  /-- A block that `allowed` admits and that passes its transition, then the chains after it. -/
  | step {chain chain' : BlockChain} {fork : Fork} {block : Block fork Transaction} {post : State}
      (hallowed : allowed chain fork block) (checkSeal : Bool)
      (transition : stateTransition chain block checkSeal = .ok post)
      (tail : BlockChain.Reaches allowed (chain.addBlock block post) chain') :
      BlockChain.Reaches allowed chain chain'

/-- A property of the state that each admitted block keeps holds after such blocks. -/
theorem BlockChain.Reaches.invariant
    {allowed : BlockChain → (fork : Fork) → Block fork Transaction → Prop} {P : State → Prop}
    (keeps : ∀ {chain : BlockChain} {fork : Fork} {block : Block fork Transaction}
      {checkSeal : Bool} {post : State}, allowed chain fork block →
      stateTransition chain block checkSeal = .ok post → P chain.state → P post)
    {chain chain' : BlockChain} (reaches : chain.Reaches allowed chain') (start : P chain.state) :
    P chain'.state := by
  induction reaches with
  | refl => exact start
  | step hallowed _ transition _ ih => exact ih (keeps hallowed transition start)

end EthLib.Execution.Blocks

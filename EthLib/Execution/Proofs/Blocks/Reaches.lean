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

/-- A chain reaches another through blocks that each pass their transition at a fork in `forks`.

Each block may pass it with or without the check of its seal. -/
inductive BlockChain.Reaches (forks : Fork → Prop) : BlockChain → BlockChain → Prop
  /-- A chain reaches itself. -/
  | refl (chain : BlockChain) : BlockChain.Reaches forks chain chain
  /-- A block at a fork in `forks` that passes its transition, then the chains after it. -/
  | step {chain chain' : BlockChain} {fork : Fork} {block : Block fork Transaction} {post : State}
      (hfork : forks fork) (checkSeal : Bool)
      (transition : stateTransition chain block checkSeal = .ok post)
      (tail : BlockChain.Reaches forks (chain.addBlock block post) chain') :
      BlockChain.Reaches forks chain chain'

/-- A property of the state that each block at a fork in `forks` keeps holds after such blocks. -/
theorem BlockChain.Reaches.invariant {forks : Fork → Prop} {P : State → Prop}
    (keeps : ∀ {chain : BlockChain} {fork : Fork} {block : Block fork Transaction}
      {checkSeal : Bool} {post : State}, forks fork →
      stateTransition chain block checkSeal = .ok post → P chain.state → P post)
    {chain chain' : BlockChain} (reaches : chain.Reaches forks chain') (start : P chain.state) :
    P chain'.state := by
  induction reaches with
  | refl => exact start
  | step hfork _ transition _ ih => exact ih (keeps hfork transition start)

end EthLib.Execution.Blocks

module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Committees
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedRoot
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Indicators
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Sets
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Supporters
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.TargetVotes

/-!
# Proofs: the fast confirmation rule

This entry gathers the proofs about the fast confirmation rule, without adding any.

They cover the arithmetic of the rule, how it chooses the confirmed block and the tests it passes.

Other proofs tie the stake tests of the rule to the supporters and the committees it reads.

TargetVotes instantiates an assumed honest count at an accepted checkpoint test.

No theorem here shows that the confirmed block is safe in an execution or in another store.
-/

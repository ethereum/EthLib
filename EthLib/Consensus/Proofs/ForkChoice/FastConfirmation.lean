module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Committees
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedRoot
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.DutySupport
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalTransport
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalAnchor
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Indicators
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Sets
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Supporters
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.TargetVotes

/-!
# Proofs: the fast confirmation rule

This entry gathers the proofs about the fast confirmation rule, without adding any.

They cover the arithmetic of the rule, how it chooses the confirmed block and the tests it passes.

Other proofs tie the stake tests of the rule to the supporters and the committees it reads.

One module turns an assumed honest vote count into concrete voters when the one-third test passes.

Another shows that honest votes over a whole epoch keep the block on the head chain.

It requires votes only in that epoch, with the committee check on each selected vote.

For the head result, the epoch and its vote condition are witnesses of the same stake margin.

Its alternative conclusion is a hash collision between blocks of two honest stores.

It assumes the stake margin, the ancestry at earlier slots and a compatible finalized checkpoint.

It also assumes that delayed blocks pass the handler and that stores process messages on time.

Historical anchor transport derives later head ancestry from a guarded margin, or returns evidence.

It retains committee agreement, historical coverage, drift and finality conditions as hypotheses.
-/

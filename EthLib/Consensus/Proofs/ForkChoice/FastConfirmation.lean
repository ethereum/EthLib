module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Checkpoints
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Committees
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedRoot
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Indicators
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Sets
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Supporters

/-!
# Proofs: the fast confirmation rule

`Basic` gives the arithmetic and rule-update facts; `ConfirmedRoot` characterizes root selection.

`Indicators` and `Sets` connect the computed tests with stake and validator sets.

`Supporters` and `Committees` place supporters in the committees the rule reads.

`Checkpoints` gives checkpoint-check soundness of one successful `Store.onFastConfirmation` call.

Its endpoint assumes only that the call succeeds, for any preset, fork, configuration and store.

The descendant-search lemma additionally assumes that the selected start is at most one epoch old.

The general walk-member slot bound assumes the initial accumulator is above the terminal block.

These readers use an empty accumulator, so that condition is vacuous.

The result records the selected start, checkpoint-field updates and tests passed by a later root.

It proves neither safety of the start, retention by another honest store, nor accountability.

Conditional and accountable safety under #1458 are planned consumers, not delivered theorems here.

This entry imports the leaves without adding declarations. Declaration namespaces are unchanged.

The old sibling leaf imports move under `FastConfirmation` with these short names.

Import this entry for all seven leaves, or import a leaf directly for its facts.
-/

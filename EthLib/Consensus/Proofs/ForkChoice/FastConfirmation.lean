module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Committees
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedRoot
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Indicators
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Sets
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Supporters

/-!
# Proofs: the fast confirmation rule

`Basic` gives the arithmetic and rule-update facts.

`ConfirmedRoot` characterizes root selection and checkpoint-check soundness of one successful call.

`Indicators` and `Sets` connect the computed tests with stake and validator sets.

`Supporters` and `Committees` place supporters in the committees the rule reads.

The call endpoint assumes only success, for any preset, fork, configuration and store.

The descendant checkpoint result needs the lower freshness bound `currentEpoch ≤ startEpoch + 1`.

This permits future start epochs.

The general walk-member slot bound assumes the initial accumulator is above the terminal block.

These readers use an empty accumulator, so that condition is vacuous.

The result records the selected start, checkpoint-field updates and tests passed by a later root.

It proves neither safety of the start, retention by another honest store, nor accountability.

Conditional and accountable safety under #1458 are planned consumers, not delivered theorems here.

This entry imports the six leaves without adding declarations.

Import it for all results, or import a leaf directly for its facts.
-/

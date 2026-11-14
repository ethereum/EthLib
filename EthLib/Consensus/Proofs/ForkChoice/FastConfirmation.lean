module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic
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

This entry imports the leaves without adding declarations. Declaration namespaces are unchanged.

The old sibling leaf imports move under `FastConfirmation` with these short names.

Import this entry for all six leaves, or import a leaf directly for its facts.
-/

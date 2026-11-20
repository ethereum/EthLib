# History of the fork-indexed rules

`rules.tsv` holds the value of each fork-indexed rule of the execution layer at each fork.

A fork-indexed rule is a definition whose value depends only on the fork.

EthLib writes each rule once, with the fork as an argument.

So an edit made for one fork can change the rule at earlier forks, and no build error says so.

This file shows such a change in the pull request that makes it.

The file also holds each constant of type `Nat` of the execution layer and of `Base`, once.

```text
    rule                                  fork          value
    Execution.Evm.sloadCost · true        istanbul      800
    Execution.Evm.sloadCost · true        berlin        2100
    Execution.Evm.GasCosts.WARM_ACCESS    -             100
```

`lake exe rule-history` writes it from the compiled code.

`lake exe rule-history --check` fails when the code computes another value, and prints the changed lines.

The file is a record of what the code computes, not a test vector.

The code under test wrote it, so it shows a change and never shows that a value is right.

A pull request that changes a line names, for that line, the source that requires the new value.

A new fork adds one line per rule, and its pull request names the source of each value at the new fork.

The tool finds the rules by their type, so a new rule needs no change to the tool.

Its module doc, in `scripts/RuleHistory.lean`, lists the types it reads.

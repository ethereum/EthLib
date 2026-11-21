# History of the fork-indexed rules

`rules.tsv` holds the value at each fork of each fork-indexed rule of the execution layer whose value is a number.
A fork-indexed rule is a definition whose value depends only on the fork.
EthLib writes each rule once, with the fork as an argument.
So an edit made for one fork can change the rule at earlier forks, and no build error says so.
This file makes such a change visible in the pull request that makes it.
It also holds each constant of type `Nat` of the execution layer and of `Base`, once.

The file covers only the rules whose values are numbers, or structures of numbers.
A rule that gives a list, such as the addresses of the precompiles at a fork, or an opcode table, is not in it.
Neither is a fork branch written inside a function that takes more than the fork.
A rule can also give a value at a fork where no caller reads it, such as an access price before Berlin.
Such a line is what the code computes, not a value in force at that fork.

In the file, `·` stands for the fork, and the fork of a constant is `-`.
Three of its lines, with the sources of their values:

| rule | fork | value | source |
| --- | --- | --- | --- |
| `Execution.Evm.sloadCost · true` | `istanbul` | 800 | EIP-1884 |
| `Execution.Evm.sloadCost · true` | `berlin` | 2100 | EIP-2929 |
| `Execution.Evm.GasCosts.WARM_ACCESS` | `-` | 100 | EIP-2929 |

`lake exe rule-history` writes the file from the compiled code, and `lake exe rule-history --check` fails when the code computes another value, and prints the changed lines.
The file records what the code computes and is not a test vector.
The code under test wrote it, so it shows that a value changed, and never that a value is right.

A pull request that changes a line names, for that line, the source that requires the new value.
A new fork adds one line to each fork-indexed rule and none to the constants.
Its pull request names the source of each value at the new fork.
The tool finds the rules by their type, so a new rule needs no change to the tool.
The module header of `scripts/RuleHistory.lean` lists the types it reads.

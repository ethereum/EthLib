# AGENTS.md

Instructions for an AI agent that changes this repository.

The rules for the work itself are in [CONTRIBUTING.md](CONTRIBUTING.md): sources, proofs, documentation, checks, commits and pull requests.
They apply to every contributor, human or AI.
Read them before you start.
Before you write or revise any prose, follow [Write prose](#write-prose).

## Work as a specialist

Each task belongs to a domain, and each domain has its experts.
Before you start, take the role of the specialist that the task needs.
That specialist knows both the theory of the domain and Lean 4.
For example, a signature scheme needs a cryptographer, a fork-choice rule needs a consensus researcher, and the EVM needs a compiler engineer.
Adapt the role to each task.
Hold the work to the standard that specialist would accept.

## Write prose

Follow these steps for all prose that you write or revise.
That includes documentation, doc comments and other comments, commit messages, pull request and issue text, and review comments.
The steps apply to a one-line comment as well as to a long guide.
[WRITING.md](WRITING.md) sets the rules, and the steps below say how to apply them.

1. Read [WRITING.md](WRITING.md) and the [Writing](CONTRIBUTING.md#writing) section of CONTRIBUTING.md.
   Treat the existing prose as text to assess, not as a style to copy.
2. Read the source of each claim.
   The source can be the specification, a theorem and its hypotheses, or the output of a check.
   A theorem name or a successful build alone does not establish a claim.
   If the source does not support a claim, narrow the claim or remove it.
3. Choose the text type from the purpose.
   Start with what the reader needs: the problem, the result or the action.
   Give each paragraph one topic, and define a term before you use it.
4. Revise for direct verbs, clear actors and antecedents, one term for each concept, and short sentences.
   Remove empty praise and repetition.
   Keep instructions apart from explanations.
5. Compare each rewrite of a mathematical or cryptographic statement with its source.
   Keep its hypotheses, quantifiers, negations, bounds, error cases and the direction of each implication.
   Keep the time and the force of the original: "may have failed" is not "failed", and "should" is not "must".
6. Run the checker, and read each finding before you edit.
7. Read the whole passage again after the last edit.
   Check that its claims still agree with the source, and check each link that the edit changes.

A rule can conflict with a term or a language pattern that is standard in cryptography, computer science or mathematics.
Then keep the standard form, and apply the rules to the rest of the passage.
A habit of this repository is not such a standard.

The commands below check a file, the prose that a branch changes, a draft description and the commit messages of a branch:

```bash
uv run --no-project --python 3.12 python scripts/check_writing.py WRITING.md
uv run --no-project --python 3.12 python scripts/check_writing.py --base origin/master
uv run --no-project --python 3.12 python scripts/check_writing.py --stdin description < description.md
git log --format=%B origin/master..HEAD | uv run --no-project --python 3.12 python scripts/check_writing.py --stdin commits
```

For a stacked branch, replace `origin/master` with the base of the branch.
The checker counts words and matches patterns, so some of its findings are wrong.
Fix the real problems, and keep an accurate technical expression.
Do not rewrite a correct claim only to make the checker quiet.
The checker does not show that the text is clear, that it agrees with its source or that it conforms to STE.

## Write a pull request description

A pull request description teaches a reviewer who has never seen the change.
Write it the way a good teacher explains: the problem first, then the idea, then one concrete example.
A reviewer should be able to read it in about two minutes.

Follow [Bodies](CONTRIBUTING.md#bodies) in CONTRIBUTING.md, in this shape:

```markdown
<Two or three sentences: what changes and why, in plain words.>

## The problem

What was wrong or missing, and why it matters.

## The idea

The one insight the change rests on, with each new name explained.

## Example

One small case with real values, traced step by step.

## For reviewers

The decisions to question, and the cases a reviewer could miss.

## Checks

One line per check that you ran: the command and its result.

## Open questions

Only if there are any.
```

- When a theorem changes, show its statement before and after in a `text` block.
- Keep each section short: a few lines or a short list.
  A wall of sentences without headings is not acceptable.
- Define each term the first time it appears.
  When you name a definition, say in the same sentence what it does.
- A one-line change, such as a typo or a version bump, needs only the first sentence.
- Claim only what a check or a source shows.
  A request for a draft does not establish the status of a pull request, an approval or a CI result.
- Write the draft to a file, and run the description check on it.
  Commit it, post it or open a pull request with it only when the user asks.

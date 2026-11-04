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

Use this workflow for documents, doc comments, other comments, commit messages, pull request and issue text, and review comments.
Work within the user's requested scope.
The [writing guide](WRITING.md) and its [vocabulary](WRITING.md#vocabulary) offer advice.

1. **Read the source before stating a claim.**
   Follow [CONTRIBUTING.md](CONTRIBUTING.md) for source, proof, citation and testing requirements.
   Read the relevant definitions, hypotheses, proofs and test evidence.
   For contribution text, distinguish what changed, which checks ran and what remains uncertain.
2. **Start with what the reader needs.**
   State the problem, result or action first.
   Develop one topic per paragraph.
   Use the guide when its advice helps the reader.
3. **Revise real problems.**
   Identify a clarity or accuracy problem before changing a passage.
   Keep established terms, hypotheses, quantifiers, bounds, conditions, uncertainty and requirement strength.
   Repository habit alone does not justify unclear writing.
4. **Compare complete passages.**
   Read the old and new paragraphs side by side in context.
   This applies to contribution instructions as well as mathematical and cryptographic claims.
   Check that the revision keeps their meaning, conditions and scope, and explain why it is clearer.
   Read the final passage and check any changed links or references.
5. **Leave correct text alone.**
   You can use the checker for optional suggestions.
   Read each suggestion in context; it does not establish clarity, technical accuracy or STE conformance.
   Do not change clear, correct text to silence it.

Technical accuracy takes priority over writing advice.
Keep a standard technical form when a rule conflicts with it, and apply the advice to the rest of the passage.

The optional commands below check a file, changed prose, a draft description and commit messages.
The final command checks the messages only if `git log` succeeds:

```bash
uv run --no-project --python 3.12 python scripts/check_writing.py WRITING.md
uv run --no-project --python 3.12 python scripts/check_writing.py --base origin/master
uv run --no-project --python 3.12 python scripts/check_writing.py --stdin description < description.md
git log --format=%B origin/master..HEAD > commits.txt && \
  uv run --no-project --python 3.12 python scripts/check_writing.py --stdin commits < commits.txt
```

For a stacked branch, replace `origin/master` with its actual parent branch.
Keep `commits.txt` and private drafts out of the contribution.
The checker reads Markdown and Lean comments; review other prose manually.

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

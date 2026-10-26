# AGENTS.md

Rules for any agent, human or AI, that changes this repository.

EthLib holds formally verified Ethereum specifications, written in Lean.

Each one is an Ethereum primitive, from whichever part of the protocol it comes.

Clients and other Lean projects build on it.

EthLib is meant to be their source of truth.

A bug here spreads to everything built on top of it.

So every line must be correct, justified and readable by a specialist of its domain.

## The bar

Work the way the author of a standard would.

- Read the specification, the surrounding code and the existing proofs before writing anything.
- Every definition, value and rule has a source.
  You have read that source.
- If a source is ambiguous or two sources disagree, stop and say so.
  Do not pick one silently.
- Never invent a citation, a section number, a test vector or a known answer.
- Never claim a check passed unless you ran it and saw it pass.
- Keep changes small and on topic.
  One idea per pull request.

When you are not sure, ask.

A question costs minutes.

A plausible guess merged into a specification costs far more.

## Sources of truth

Each module implements a published specification.

It can be an EIP, an RFC, an ePrint paper, an ethresear.ch post, a specification repository such as `ethereum/consensus-specs`, or any other primary source.

When several exist, use the most authoritative one.

That specification is normative.

When the code and the specification disagree, the code is wrong until shown otherwise.

Cite the exact document and section in the code that implements it.

For example: `RFC 9380 §5.3.1`, or the fork and function name in `consensus-specs`.

This repository is the reference.

Do not cite another implementation as the authority for a behaviour.

Matching a client byte for byte is a useful test, not a justification.

## Work as a specialist

Each task belongs to a domain, and each domain has its experts.

Before starting, take the role of the specialist the task needs.

That specialist knows both the theory of the domain and Lean 4.

A cryptographer for a signature scheme, a consensus researcher for a fork-choice rule, a compiler engineer for the EVM.

Adapt the role to each task.

Hold the work to the standard that specialist would accept.

## Layout

```text
EthLib/<Domain>/<Module>/            the specification, executable
EthLib/<Domain>/Proofs/<Module>/     theorems about it
bindings/python/                     C exports and the Python package
tests/<domain>/<module>/             generated test vectors
```

A new domain adds its proof root to the `Proofs` library in `lakefile.lean`.

The specification never imports the proofs.

Proofs live in their own library, so the specification builds and links without them.

## Lean

### Specification code

- Write the specification to be read first and run second.
  Clarity wins over speed unless speed is the point of the change.
- Name things after the specification.
  If the paper calls it the randomizer, the code does too.
  If `consensus-specs` calls it `process_slots`, so does the code, in Lean's casing.
- Reject malformed input at the boundary with a typed error.
  No truncation, no padding, no silent fallback.
- Put invariants in types, such as `Vector` lengths and `Fin` bounds.
- Avoid `partial def` in new code.
  A function the kernel cannot unfold is a function nobody can prove anything about.

### Proofs

- No `sorry`, `admit` or new `axiom`.
  CI builds with `--wfail`, so an unfinished proof fails the build.
- Prefer proofs the kernel checks on its own.
- `native_decide` and `bv_decide` add a generated axiom.
  Use them only for closed known-answer checks the kernel cannot evaluate.
  Say why in a comment next to the tactic.
- After a proof change, check its axioms with `#print axioms`.
  The goal is `propext`, `Classical.choice` and `Quot.sound`, nothing else.
- Prove what a reader cares about.
  Round trips, injectivity, rejection of bad input, invariants of a state transition.
  Above all, agreement with the specification.

### Known answers

A known answer pins one input to one output, byte for byte.

Take it from the specification's own test vectors when they exist.

Otherwise, describe what it pins.

For example: "one honest signature at epoch 7", or "one empty slot processed".

Never regenerate an expected value from the code under test and call it a check.

## Documentation

Developers all over the world read this documentation.

Many read it in their second language.

Write for a smart reader who has never seen this file.

- One sentence per line.
  A sentence that wraps onto a second line is too long, so split it.
- Leave a blank line between ideas.
  Space makes a dense subject readable.
- Short, plain words.
  Define a term the first time it appears.
- Explain why, not what.
  The code already says what.
- Use ASCII for math and layouts: `x_i`, `2^32`, `sum_i`.
- Draw byte layouts and data flow in a fenced `text` block.
- No marketing, no hedging, no filler.
  Words such as "robust", "seamless", "comprehensive" and "it is worth noting" go.
- No editorial headers such as `# Why this matters`.
- Describe the code as it is now.
  Never "previously", "the fix", "as discussed".
- Comment every non-obvious step of a definition or proof.
  Put the comment right above the line it explains.

Example, from the XMSS signature layout:

````lean
/-- The signature layout, 1208 bytes.

```text
    [ randomizer: 24 | 42 chain values: 672 | 32 siblings: 512 ]
```

- The randomizer comes first, as in the paper's signature tuple.
- Chain values are in chain order.
- Siblings run from the leaf up to the root.
-/
def signatureSsz : Ssz.Desc :=
  .container ["randomness", "chain_values", "merkle_path"]
    [.byteVector RANDOMNESS_LEN, .byteVector (V * DIGEST_LEN),
      .byteVector (LOG_LIFETIME * DIGEST_LEN)]
````

When a module does not follow these rules, apply them to what you change.

Do not reformat untouched code in an unrelated pull request.

## Bindings

The C exports and the Python package are the public surface for clients.

- Export the operations a client calls, under the specification's names, and the object sizes.
  Keep internal steps, such as one hash or one helper of a state transition, inside Lean.
- Read every size from Lean at load time.
  Never hard-code a length in C or Python.
- The generated C frees each argument itself.
  A wrapper must not free what it passes to an export.

## Checks

Run these before opening a pull request:

```bash
lake build
```

It builds the specification and every proof, with warnings treated as errors in CI.

When you touch bindings or test vectors, also run the Python suite:

```bash
pip install -e '.[test]'
pytest
```

Report what you ran and what it printed.

If you skipped a check, say so.

## Commits and pull requests

A reviewer should know in fifteen seconds what the change does and where to look.

### Titles

Titles follow [Conventional Commits 1.0.0](https://www.conventionalcommits.org/en/v1.0.0/).

That holds for commit subjects and pull request titles alike.

A squash merge turns the pull request title into the commit on `master`.

```text
<type>(<scope>): <summary>
```

The type says what kind of change it is:

- `feat`: new behaviour, such as a new function, module or export.
- `fix`: behaviour that disagreed with the specification now agrees.
- `proof`: new or changed theorems, with no change to the specification code.
- `perf`: the same results, computed faster.
- `refactor`: the same behaviour, with the code restructured.
- `test`: test vectors, known answers or the Python suite.
- `docs`: documentation only.
- `build`: Lake, the Lean toolchain, dependencies or packaging.
- `ci`: the GitHub workflows.
- `chore`: anything else that touches no specification, proof or test.

Conventional Commits only fixes `feat` and `fix`.

The other types are the common ones, plus `proof`, which this repository needs.

The scope names the domain or module, in lowercase: `xmss`, `kzg`, `bls`, `ssz`, `bindings`.

Leave the scope out when the change spans the repository.

The summary is in the imperative mood, starts lowercase and has no trailing period.

The whole title fits in 72 characters.

A change that breaks consumers adds `!` before the colon.

That covers a new wire format, a renamed or removed export, or a new test-vector layout.

Its commit body then ends with a `BREAKING CHANGE:` footer that says what to change.

```text
feat(xmss): add SSZ encoding for the public key and the signature
fix(xmss)!: put the randomizer first in the signature encoding
proof(xmss): prove that the tweak encoding is injective
build: pin ssz-specs to a23a239
docs: add AGENTS.md
```

### Bodies

The commit body says why, when the subject cannot.

The pull request body is written for a human who has never seen the change.

Its length follows the change.

- A typo or a dependency bump needs one line, or none.
- An ordinary fix needs a few sentences.
- A new module, a wire-format change or a subtle proof needs more.
  Then explain it the way a good teacher would.

A longer body follows this order:

1. The problem.
   What is wrong or missing, and why it matters, in plain words.
2. The idea.
   The one insight the change rests on.
3. One concrete example.
   Real values traced step by step: bytes, a slot, an epoch, a gas cost.
   A short `text` block often says it best.
4. What reviewers and implementers must know.
   The case a reviewer could miss, and what consumers must change, if anything.

For example, a body for a wire-format change:

````markdown
A signature is 1208 bytes, and the order of its three fields is part of the wire format.

The paper writes a signature as (randomizer, chain values, path).
The verifier also needs the randomizer first, to recompute the encoding.
So the encoding now follows that order:

```text
before:  [ 42 chain values: 672 | randomizer: 24 | 32 siblings: 512 ]
after:   [ randomizer: 24 | 42 chain values: 672 | 32 siblings: 512 ]
```

The sizes are unchanged, so a length check cannot catch the old layout.
Every implementation that encodes or decodes signatures must switch.
````

Rules for every body:

- Plain words and short sentences.
  Define a term the first time it appears.
- Use a heading only when the body has several distinct parts.
- Leave out what the diff already shows: file lists, renamed symbols, the code retold.
- No checklists, no "this PR", no tables of unchanged values.
- Link the issue it closes: `Closes #22.`
- Stacked pull requests say so: `Stacked on #43.`

Read the body aloud before posting.

If it sounds like a report, cut it.

If you are an AI agent, say so in the pull request.

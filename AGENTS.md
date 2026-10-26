# AGENTS.md

Rules for any agent, human or AI, that changes this repository.

EthLib holds formally verified Ethereum primitives, written in Lean.

Clients and other Lean projects build on it.

A wrong constant, a swapped field or a missing check here becomes a bug downstream.

So every line must be correct, justified and readable by a specialist.

## The bar

Work the way a cryptographer writing a paper would.

- Read the standard, the surrounding code and the existing proofs before writing anything.
- Every constant, byte order, domain separator and field order has a source.
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

Each primitive implements a published standard.

The standard is normative.

When the code and the standard disagree, the code is wrong until shown otherwise.

- BLS12-381 signatures: `draft-irtf-cfrg-bls-signature-04`.
  Hash to curve: RFC 9380.
  The Ethereum wrappers: `ethereum/consensus-specs`.
- KZG commitments: EIP-4844 and EIP-7594, as written in `ethereum/consensus-specs`.
- XMSS signatures: ePrint 2025/055, by Drake, Khovratovich, Kudinov and Wagner.
- BLAKE2s: RFC 7693.
- SHA-256: FIPS 180-4.
- SSZ: `ethereum/ssz-specs`, pinned in `lakefile.lean`.

Cite the exact document and section in the code that implements it.

For example: `RFC 9380 §5.3.1`.

This repository is the reference.

Do not cite another implementation as the authority for a behaviour.

Matching a client byte for byte is a useful test, not a justification.

## Layout

```text
EthLib/Cryptography/<Primitive>/          the specification, executable
EthLib/Cryptography/Proofs/<Primitive>/   theorems about it
bindings/python/                          C exports and the Python package
tests/cryptography/<primitive>/           generated test vectors
```

The specification never imports the proofs.

Proofs live in their own library, so the spec builds and links without them.

## Lean

### Specification code

- Write the specification to be read first and run second.
  Clarity wins over speed unless speed is the point of the change.
- Name things after the standard.
  If the paper calls it the randomizer, the code does too.
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
  Round trips, injectivity, rejection of bad input, agreement with the standard.

### Known answers

A known answer pins one input to one output, byte for byte.

Take it from the standard's own test vectors when they exist.

Otherwise, describe what it pins, such as "one honest signature at epoch 7".

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

Older modules do not all follow these rules yet.

Apply them to what you change.

Do not reformat untouched code in an unrelated pull request.

## Bindings

The C exports and the Python package are the public surface for clients.

- Export the operations a client calls, under the standard's names, and the object sizes.
  Keep internal steps, such as one hash or one encoding layer, inside Lean.
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

- The title is a plain imperative sentence, such as "Add verification".
  No prefix such as `feat:`, no trailing period.
- The body is a few sentences of prose.
  It says why, and the one thing a reviewer could miss.
- Say what implementers must change, if anything.
- Leave out what the diff already shows: file lists, renamed symbols, the code retold.
- No checklists, no "this PR", no tables of unchanged values.
- Link the issue it closes: `Closes #22.`
- Stacked pull requests say so: `Stacked on #43.`

Read the body aloud before posting.

If it sounds like a report, cut it.

If you are an AI agent, say so in the pull request.

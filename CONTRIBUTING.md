# Contributing

This file sets the rules and the terms under which you contribute to EthLib.
They apply to every contributor, human or AI.
How to build and test is in the [README](README.md#contributing).

EthLib is a library of formally verified Ethereum primitives, written in Lean.
Each primitive implements a published specification, from whichever part of the protocol it comes.
Clients and other Lean projects build on it.
A bug here spreads to everything built on top of it.
So every line must be correct and justified by its source.

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
  Give each pull request one idea.

When you are not sure, ask.
A question costs minutes.
A plausible guess merged into this library costs far more.

## Sources of truth

Each module implements a published specification.
It can be an EIP, an RFC, a NIST or SEC standard, an ePrint paper, an ethresear.ch post, or any other primary source.
When several exist, use the most authoritative one.
That specification is normative.
When the code and the specification disagree, the code is wrong until someone shows otherwise.

Cite the exact document and section in the code that implements it.
For example: `RFC 9380 §5.3.1`, or `EIP-4844` with the name of its section.

EthLib is a specification at the same level as `ethereum/execution-specs` and `ethereum/consensus-specs`.
So do not cite them in the code.
You can read them to understand a rule and to check your work.
If no primary source states a rule, state the rule itself in the doc comment.
Test vectors keep their pinned origin, as [`ARCHITECTURE.md`](ARCHITECTURE.md#sources) explains.

Do not cite another implementation as the authority for a behaviour.
A byte-for-byte match with a client is a useful test, not a justification.

## Layout

```text
EthLib/<Domain>/<Module>/            the library code
EthLib/<Domain>/Proofs/<Module>/     theorems about it
EthLib/<Domain>/Exports/             the C exports the bindings call
bindings/python/                     the C extension and the Python package
tests/<domain>/<module>/             generated test vectors
```

[`ARCHITECTURE.md`](ARCHITECTURE.md) says which domain a module belongs to, what it may import and which types it shares.
A new domain adds its proof root to the `Proofs` library in `lakefile.lean`.
The library code never imports the proofs.
Proofs live in their own Lake library, so the library code builds and links without them.

The C exports live in a third library, `Exports`, so a Lean project that imports the specification gets no `@[export]` symbol.
A new domain with exports adds its export root to the `Exports` library.

These three libraries form one package, `EthLib`.
A property or a model may import Mathlib, Batteries or VCVio, and it goes in `EthLib/<Domain>/Proofs/<Module>/` like any other property.
The specification and the exports import nothing beyond the Lean toolchain.
[`ARCHITECTURE.md`](ARCHITECTURE.md#packages) describes the package.

## Lean

### Library code

- Write the code to be read first and run second.
  Clarity wins over speed unless speed is the point of the change.
- Name things after the specification.
  If the paper calls it the randomizer, the code does too.
  If `consensus-specs` calls it `process_slots`, so does the code, in Lean's casing.
- Reject malformed input at the boundary with a typed error.
  Do not truncate or pad it, and do not replace it silently with a default.
- Put invariants in types, such as `Vector` lengths and `Fin` bounds.
- Avoid `partial def` in new code.
  A function the kernel cannot unfold is a function nobody can prove anything about.

### Proofs

- Do not use `sorry`, `admit` or a new `axiom`.
  CI builds with `--wfail`, so an unfinished proof fails the build.
- Prefer proofs the kernel checks on its own.
- Do not use a tactic that trusts compiled code, such as `native_decide`, `bv_decide` or `decide +native`.
  Their computed results are justified by compiler-trusting axioms rather than kernel evaluation.
  `lake exe check-decls` fails on any use.
- After a proof change, check its axioms with `lake exe check-decls`.
  The goal is `propext`, `Classical.choice` and `Quot.sound`, nothing else.
- Prove what a reader cares about: round trips, injectivity, the rejection of bad input and the invariants of a state transition.
  Above all, prove agreement with the specification.

### Known answers

A known answer pins one input to one output, byte for byte.
Known answers belong in the Python test suite, in `bindings/python/tests/`, and never in Lean.

In Lean, a known answer is a theorem or an `example` that evaluates a definition on concrete inputs.
It compares the result with an expected value, by `rfl`, `decide`, `decide +kernel` or `simp`.
The build must then run the definition on those inputs.
One such proof can need several gigabytes of memory and minutes of build time.
It also checks only one input.

So state each Lean theorem for all inputs.
Test concrete inputs from Python, through the bindings.
If a function has no C export yet, add the export and its binding.

Lean keeps one kind of concrete fact: a small decidable fact that a definition needs to be correct.
Examples are a constant checked against the algorithm that generates it, or a Pratt certificate.
The order of the fork timeline is another example.
Each such proof must take a few seconds at most.

Take the test vectors from the specification's own test vectors when they exist.
Otherwise, describe what each vector pins.
For example: "one honest signature at epoch 7", or "one empty slot processed".
Next to the vectors, record their pinned origin, such as the commit they come from.

Never regenerate an expected value from the code under test and call it a check.

## Writing

Developers all over the world read EthLib, many of them in their second language.
[WRITING.md](WRITING.md) sets the standard for its English, based on ASD-STE100 Simplified Technical English (STE).
The standard applies to every author, human or AI.
It covers all prose: documentation, doc comments and other comments, commit messages, pull request and issue text, and review comments.

WRITING.md gives the full rules and the vocabulary of EthLib.
These rules matter most:

- Write short sentences: 20 words or fewer in an instruction, and 25 words or fewer in a description.
- Give each paragraph one topic, in six sentences or fewer.
- Use the active voice, and name the actor, such as the decoder, the verifier or CI.
- Use one term for one concept, with the meaning that the vocabulary gives it.
- Do not use semicolons, contractions or Latin abbreviations such as "e.g." in prose.
- Claim only what the code, a theorem or a check that you ran shows.
  A style edit keeps every hypothesis, bound, condition and uncertainty of the claim.

Technical accuracy comes first.
If a rule conflicts with a term or a language pattern that is standard in cryptography, computer science or mathematics, keep the standard form.
A habit of this repository is not such a standard.

Existing prose is not a model to copy.
When you change a passage, bring it to the standard.
Leave unrelated prose for a separate pull request.

`scripts/check_writing.py` finds some departures from the standard, such as long sentences and semicolons.
Run it on the prose that your branch changes:

```bash
uv run --no-project --python 3.12 python scripts/check_writing.py --base origin/master
```

For a stacked pull request, give its base branch instead of `origin/master`.
Each finding is a suggestion, so read it before you edit.
Fix the real problems, and do not change a correct sentence only to make the checker quiet.
CI runs the same check on the changed prose and on the pull request description.
It reports the findings as warnings, and they do not fail CI.

When you change the checker, also run its tests:

```bash
uv run --no-project --python 3.12 python -m unittest scripts/test_check_writing.py
```

## Documentation

Write for a smart reader who has never seen the file.

Two kinds of documentation live here, and they are read differently.
A doc comment in Lean sits next to the code and is read a few lines at a time, so it is terse.
A Markdown file is read from top to bottom, like a chapter, so it is prose.

These rules hold for both:

- Use short, plain words.
  Define a term the first time it appears.
- Explain why, not what.
  The code already says what.
- Use ASCII for math and layouts: `x_i`, `2^32`, `sum_i`.
- Draw byte layouts in a fenced `text` block.
- Do not add marketing or filler.
  Words such as "robust", "seamless", "comprehensive" and "it is worth noting" go.
- Do not hedge a claim that the evidence supports, and keep an uncertainty that the evidence does not resolve.
- Do not write editorial headings such as `# Why this matters`.
- Describe the code as it is now, without words such as "previously", "the fix" or "as discussed".

### Doc comments in Lean

- Write one sentence per line.
  A sentence that wraps onto a second line is too long, so split it.
- Leave a blank line between ideas.
  Space makes a dense subject readable.
- Comment every non-obvious step of a definition or proof.
  Put the comment right above the line it explains.

Example, from the XMSS signature layout:

````lean
/-- Encode one layer's signature as 1200 bytes.

```text
    [ randomizer: 16 | 58 chain values: 928 | 16 siblings: 256 ]
```

- Chain values are in chain order.
- Siblings run from the leaf up to the root.
-/
def encodeLayerSignature (sig : LayerSignature) : ByteArray :=
  packBytes sig.randomizer ++ packDigests sig.chainValues ++ packDigests sig.path
````

### Markdown files

A README, `SOUNDNESS.md` or a guide such as this one reads like a short chapter of a good mathematics textbook.
It is precise, concise and written to teach.

- Write paragraphs.
  A paragraph develops one idea over several sentences that lead into each other.
  A blank line after every sentence breaks that thread, so leave one only between paragraphs.
- In the source, start each sentence on a new line.
  Markdown joins the lines of a paragraph, and a diff then shows one sentence per line.
- Lead with the problem, then the idea, then the details.
  The reader should know why an object exists before meeting its definition.
- Show one small, concrete example where it helps, with the steps written out.
  Take its values from the specification or work them out by hand, never from the code under test.
- Keep bullets for content that is a list: operations, cases, files, commands.
  A bullet holds a full thought, not a fragment of a sentence.
- Use a Markdown table for tabular content.
- Name a file or a theorem where the reader needs to find it, not in every sentence.

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

Run these checks before you open a pull request:

```bash
lake build
```

It builds the library and every proof, with warnings treated as errors in CI.

Then check the compiled declarations:

```bash
lake exe check-decls
```

It reports any axiom beyond the standard three, and any `partial`, `opaque`, `unsafe`, `@[extern]`, `@[implemented_by]` or `@[csimp]`.
It also reports a definition of the specification that cannot unfold in the kernel, for example because it uses `while` or `IO`.

`scripts/check_decls_baseline.txt` lists the findings that exist today, and the goal is to remove each one.
A pull request that removes a finding removes its line, or the check fails on the stale entry.
A new finding is fixed, never added to the list.

When you change the check, also run `scripts/test_check_decls.sh`.

Then check that `SOUNDNESS.md` still holds:

```bash
uv run --no-project --python 3.12 python scripts/soundness_facts.py --check
uv run --no-project --python 3.12 python -m unittest scripts/test_soundness_facts.py
```

It fails when a fact it generates, such as the theorems that still use `native_decide`, no longer matches the repository.
Run it without `--check` to regenerate them.

It also fails when `pyproject.toml` declares a package version other than the one `SOUNDNESS.md` describes.
Then review the whole document for the new version, and update its version line by hand.

A release has one version, in the form `MAJOR.MINOR.PATCH`.
It appears twice: in `pyproject.toml` for the Python package, and in `lakefile.lean` for Lake.
A version bump changes both, and this check fails when they differ:

```bash
uv run --no-project --python 3.12 python scripts/release_manifest.py --check
uv run --no-project --python 3.12 python -m unittest scripts/test_release_manifest.py
```

When a tag `v<version>` is pushed, `publish.yml` runs the same check against the tag.
It then attaches `release-manifest.json` to the GitHub release.
The manifest records the version, the Lean toolchain, the revision of each Lake package, the fixture pins of `tests/sources.toml` and the exported C symbols.

Then check the imports of every Lean module:

```bash
uv run --no-project --python 3.12 python scripts/check_layers.py
```

It fails on an import that breaks a rule of [`ARCHITECTURE.md`](ARCHITECTURE.md#rules), and on a module that no library root imports.
An import that must break a rule goes in `scripts/check_layers_baseline.txt`, with the reason in a comment and in the pull request.
An entry that no longer breaks a rule fails the check, so remove it with the import.

When you touch test vectors or fixtures, also check their sources:

```bash
uv run --no-project --python 3.12 python scripts/check_fixture_pins.py
```

`tests/sources.toml` records one pinned commit for each repository that tests read from.
The check fails when a test cites another commit, and when a directory with a `SHA256SUMS` file does not name its sources.

Then check the layout of the Lean lines that your branch changes:

```bash
uv run --no-project --python 3.12 python scripts/check_lean_layout.py --base origin/master
```

It fails on a changed line longer than 100 characters, unless the line holds only a URL.
It also fails when two sentence lines of a comment touch, and one of them is changed.
Lines that your branch does not change are not checked.

These commands use uv and Python 3.12, with only the standard library.
See [prerequisites](README.md#prerequisites) for setup.

When you touch bindings or test vectors, also run the Python suite:

```bash
uv sync --frozen --extra test
uv run --no-sync pytest
```

The suite rewrites the vectors, so then check that the pinned ones are unchanged:

```bash
uv run --no-project --python 3.12 python tests/cryptography/check_vectors.py
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
- `proof`: new or changed theorems, with no change to the library code.
- `perf`: the same results, computed faster.
- `refactor`: the same behaviour, with the code restructured.
- `test`: test vectors, known answers or the Python suite.
- `docs`: documentation only.
- `build`: Lake, the Lean toolchain, dependencies or packaging.
- `ci`: the GitHub workflows.
- `chore`: anything else that touches no library code, proof or test.

Conventional Commits defines only `feat` and `fix`.
The other types are the common ones, plus `proof`, which this repository needs.

The scope names the domain or module, in lowercase: `xmss`, `kzg`, `bls`, `ssz`, `bindings`.
Leave the scope out when the change spans the repository.

The summary is an imperative phrase, such as "add strict scalar decoding", or a noun phrase for the result, such as "strict scalar decoding for RLP".
It starts lowercase and has no trailing period.
A name in the summary keeps its own case, such as `KZG` or `U256`.
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

Write the pull request body for a human who has never seen the change.
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

- Use plain words and short sentences, as [Writing](#writing) describes.
  Define a term the first time it appears.
- Use a heading only when the body has several distinct parts.
- Leave out what the diff already shows: file lists, renamed symbols, the code retold.
- Do not add checklists, the phrase "this PR" or tables of unchanged values.
- Link the issue it closes: `Closes #22.`
- Stacked pull requests say so: `Stacked on #43.`

Read the body aloud before you post it.
If it sounds like a report, cut it.

## Licence

EthLib's own material is distributed under CC0 1.0 Universal.
The legal text is in [LICENSE](LICENSE).
`pyproject.toml` declares `CC0-1.0 AND MIT AND Apache-2.0` for the Python package.
It ships the MIT-licensed RLP, hex-prefix and trie test cases from `ethereum/tests`, and the Apache-licensed secp256k1 test sets from `C2SP/wycheproof`.
Material from other projects keeps its own terms, as [Material from other projects](#material-from-other-projects) explains.

By submitting a contribution, you agree to make it available under CC0 1.0 Universal.
You must have the authority to do so.
CC0 covers only rights its affirmer holds, so you cannot dedicate work that is not yours to dedicate.

## Copyright notices

EthLib's own material carries no copyright notice in each file.
That is a choice of this project.
The [CC0 FAQ](https://wiki.creativecommons.org/wiki/CC0_FAQ#May_I_apply_CC0_to_computer_software?_If_so,_is_there_a_recommended_implementation?) recommends a notice at the top of each source file, but CC0 does not require one.

A file of EthLib's own may still need a notice, for example when it is distributed on its own.
That notice names "The EthLib Contributors", not a person or an organisation.
Do not add an AI-attribution line to a file header or its copyright notice.
The name is a convention for notices.
It does not say who holds which rights; the git history records who contributed what.

## Material from other projects

Code, data or text taken from another project keeps its own licence and notices.
The CC0 terms and the naming convention above do not apply to it.

Identify such material separately: mark where it starts and ends, name its author and give its licence.
The [CC0 FAQ](https://wiki.creativecommons.org/wiki/CC0_FAQ) asks the same for third-party work inside a CC0 work.
Do not remove or reword its notice.

Say in the pull request where the material comes from and under which licence.
Maintainers then check that the licence allows it to ship with EthLib.

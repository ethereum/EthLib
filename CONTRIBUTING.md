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
So do not cite them in the code as the authority for a rule.
You can read them to understand a rule and to check your work.
If no primary source states a rule, state the rule itself in the doc comment.
Test vectors keep their pinned origin, as [`ARCHITECTURE.md`](ARCHITECTURE.md#sources) explains.

A comment in the code may still name execution-specs or consensus-specs in a provenance note.
The note names the text and the commit where a rule is stated.
If it is known, the note also names the commit that EthLib took the rule from.
Put the note in the doc comment of the definition.
A note that covers several definitions can go once, in a section comment (`/-! -/`) above them.
Write a note only when no primary source states the rule in its own text.
Some EIPs state a rule only through a link to consensus-specs at a pinned commit, as EIP-4844 does for its KZG functions.
Such a rule cites the EIP, and it may also carry a provenance note.
A provenance note says where a rule is stated, not which text makes the rule normative, so it is not a citation of authority.

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
Among the properties, only a refinement module imports a model directly, as [`ARCHITECTURE.md`](ARCHITECTURE.md#three-kinds-of-content) explains.
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
- Do not use `panic!` or the `!` accessors, such as `xs[i]!`, `get!` and `set!`.
  Each one hides a failure: it returns a default value, or it changes nothing.
  Index with `Fin` or a `Vector`, walk arrays of equal length together with `zip`, or return a typed error.
  Older modules still use these accessors, and pull requests remove them module by module.
- Remove such an accessor even when no input that the source accepts reaches its default.
  A caller of a public function can still reach it, with arguments that break a precondition the type does not state.
  Change the definition in place, and keep no copy of the old one beside it.
  Wherever the old index was in range, the result must not change.
  Existing theorems and tests keep their meaning, and change their statements only where the type of the result changes.
  If any input reached a default where the source gives another outcome, the change is a `fix`.
  It cites the rule of the source that it restores.
  Take its test vectors from the source's own suite when one holds them.
  Otherwise take the expected value of each one from that rule, never from EthLib.
  Describe what each vector pins, and record its origin next to it, as [Known answers](#known-answers) asks.
- Prefer structural recursion, `map` and folds to `Id.run do` with mutable variables.
  A proof then follows the shape of the definition.
  A theorem about a `do` loop restates its elaborated body, so any edit of the loop breaks the statement.
  For a loop that can stop early, prefer `foldlM` in `Option` or `Except`.
  This is advice, not a rule: a loop whose speed matters can keep `do`.
- Prefer an `Except` `do` block for a chain of steps that can fail, so that it reads like the source.
  In proofs, prefer `bind_ok_iff` and the other lemmas of `EthLib/Base/Except.lean` to unfolding the chain into nested `match` expressions.
- A small decidable fact that [Known answers](#known-answers) allows, such as a constant checked against its algorithm, evaluates a definition in the kernel.
  That definition needs a recursion that the kernel can reduce.
  `decide` and `rfl` need structural recursion or fuel, because Lean makes a well-founded definition irreducible.
  `decide +kernel` also reduces a well-founded recursion whose measure is a single `Nat`, which Lean builds on `WellFounded.Nat.fix`.
  Do not count on it for a lexicographic measure, such as a pair, which Lean builds on `WellFounded.fix`.
  Lean documents only `WellFounded.Nat.fix` as reducing on closed terms.

### Failure at an entry point

An entry point is a public operation that a client or another layer calls.
Examples are a state transition, a gossip validation and an Engine API method.
What an entry point does with a wrong input is part of the protocol, so its source often says what it returns.

- Where the source defines the outcomes of an operation, return them as a type.
  For example, the Engine API answers a payload with one of five statuses, and gossip validation returns a `ValidationResult`: accept, ignore or reject.
  Map the internal errors to that type with total functions, close to the entry point.
  For example, after the checks of a payload, `newPayloadOnChain` maps an execution that aborts to `.syncing`, and any other failed transition to `.invalid`.
- Return a `Bool` only where the source defines one.
  A caller that the source requires to tell outcomes apart, for example to import or to queue a block, receives the richer type.
- Where the source fixes the order of its checks, and the order changes the outcome, follow that order.
  Pin it with a theorem, or with a test whose input fails two checks.
  Elsewhere, the source fixes only that the operation rejects the input.
  The consensus specification, for example, says only which state transitions are invalid.
  This guide does not say whether EthLib also promises which error such an input gets.
  Many proofs and Python tests pin the exact error today, and `bindings/contract/contract.json` lists the error codes of its methods.
- Where the source requires the state to be unchanged on failure, state that in a theorem.
  When the operation returns its input state on failure, state it as equality of the returned state.
  Inside a step, such as an EVM call that fails, state it over the values a caller can read: balances, nonces, code, storage and transient storage.
  Do not state it over the fields of the representation, since a new representation would break the statement.
  `processMessage_sameWrites_of_error` states it over the fields of `SameWrites`; a new theorem states it over readable values.

### Proofs

- Do not use `sorry`, `admit` or a new `axiom`.
  CI builds with `--wfail`, so an unfinished proof fails the build.
- Prefer proofs the kernel checks on its own.
- Do not use a tactic that trusts compiled code, such as `native_decide`, `bv_decide` or `decide +native`.
  Their computed results are justified by compiler-trusting axioms rather than kernel evaluation.
  `lake exe check-decls` fails on any use.
- Do not use `vcgen` or `mvcgen` in library proofs while `vcgen` is marked experimental.
  The reason is stability across toolchains, not soundness: the kernel checks a proof that `vcgen` builds like any other proof.
  In Lean v4.35.0, `mvcgen` is deprecated in favour of `vcgen`, and `vcgen` warns that it is experimental unless the option `experimental.vcgen` is set.
  Check this rule again at each update of the toolchain.
- After a proof change, check its axioms with `lake exe check-decls`.
  The goal is `propext`, `Classical.choice` and `Quot.sound`, nothing else.
- Name each theorem by the [naming conventions of Mathlib](https://leanprover-community.github.io/contribute/naming.html).
  The name is in `snake_case` and describes the statement: the conclusion first, then `_of_` and the hypotheses.
- Prove what a reader cares about: round trips, injectivity, the rejection of bad input and the invariants of a state transition.
  Above all, prove agreement with the specification.

### Known answers

A known answer pins one input to one output, byte for byte.
Known answers never enter the default build: the libraries `EthLib`, `Proofs` and `Exports`, which `lake build` builds.
They may run in three places outside it:

- The Python test suite, in `bindings/python/tests/`, runs them through the bindings, which are the surface that clients call.
- A fixture runner, a Lean executable that no default target builds, may run pinned fixtures through the definitions of the specification.
  It reaches an internal step that has no C export, and it runs compiled code, as the Python suite does.
- A Lean library of kernel vectors, which no default target imports, may prove known answers.
  CI must build it in its own step on every pull request, so that a failure points at the pull request that caused it.

In Lean, a known answer is a theorem or an `example` that evaluates a definition on concrete inputs.
It compares the result with an expected value, by `rfl`, `decide`, `decide +kernel` or `simp`.
The build must then run the definition on those inputs.
One such proof can need several gigabytes of memory and minutes of build time.
It also checks only one input.

So the library of kernel vectors holds such a proof only under a budget.
Each proof takes its input from the specification's own vectors, or covers every value of a finite type.
Each file of the library elaborates in under 20 s of CPU, with a peak memory under 2 GiB.
The budget is for the whole file, run alone with `lake env lean` after its imports are built, as `scripts/check_memory.py` runs it.

State each theorem of the default build for all inputs.
Test concrete inputs from Python, through the bindings, or through a fixture runner.
If a function that clients call has no C export yet, add the export and its binding.

The default build keeps one kind of concrete fact: a small decidable fact that a definition needs to be correct.
Examples are a constant checked against the algorithm that generates it, or a Pratt certificate.
The order of the fork timeline is another example.
Each such proof must take a few seconds at most.

Take the test vectors from the specification's own test vectors when they exist.
Otherwise, describe what each vector pins.
For example: "one honest signature at epoch 7", or "one empty slot processed".
Next to the vectors, record their pinned origin, such as the commit they come from.

Never regenerate an expected value from the code under test and call it a check.
A snapshot of values that the code computes, compared in CI, is a change detector and not a check.
A pull request that changes such a snapshot names the source of each changed line.

### No examples

EthLib proves general statements about the specification, and it keeps no examples.
An example is a proof about one particular program, contract, state or value, written to show how a rule or a tool works.
Do not add files of such proofs, and do not add them to other modules.

Example logic belongs outside the repository, with the project that needs it.
EthLib keeps the general rules and lemmas that such a proof uses.
If an example needs a general lemma that EthLib lacks, add the lemma, stated for all inputs.

A new rule or tactic is justified by its general statement.
Show its example in the description of the pull request, not in the tree.

### No benchmarks

A benchmark is a measurement on one machine, at one commit, against one set of references.
It is not part of the specification, and it ages as soon as EthLib or a reference changes.
So the repository keeps no benchmark code, benchmark inputs or tables of results.

Benchmarking is welcome for a given problem or pull request.
Run it locally, outside the tree, and keep its scripts and data out of your commits.
Give the numbers in the description of the pull request, with the machine and the command that produced them.

## Writing

Developers all over the world read EthLib, many of them in their second language.
The [writing guide](WRITING.md) offers advice for clear, precise and correct prose: documents, comments, commit messages, contribution descriptions and reviews.
Its vocabulary helps distinguish technical meanings.
For advice about sentence structure and punctuation, use the guide in context.
The source, proof, citation and testing requirements elsewhere in this file still apply.

Claim only what the code, a theorem or a check that you ran shows.

Leave clear, correct text alone, even when it does not follow a writing rule.
Read the surrounding passage before an edit, and preserve its meaning, conditions and requirement strength.
Correct real clarity or accuracy problems; leave unrelated prose for a separate change.
Technical accuracy and established terminology take priority.
Repository habit alone does not justify unclear writing.

The optional `scripts/check_writing.py` reports vocabulary, phrasal-verb, Latin-abbreviation, contraction, reference-history and approximate sentence-length suggestions.
It reads Markdown and Lean comments; review other prose manually.
For a local editing aid, run:

```bash
uv run --no-project --python 3.12 python scripts/check_writing.py --base origin/master
```

For a stacked pull request, give its actual parent branch.
Read suggestions in context and leave clear, correct text alone.
CI reports suggestions on changed prose and pull request descriptions as warnings.
Suggestions and unsupported-input notices return success; Git, usage and configuration errors remain failures.
The checker does not establish clarity, technical accuracy or STE conformance.

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
  This holds for list items too.
- Keep a long link out of the sentence.
  Write `[text][ref]` in the sentence, and the definition `[ref]: <url>` at the end of the comment.
- Put formulas that span several lines in a fenced `text` block.
  The layout check reads a line of a comment outside such a block as prose.
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
- The extension runs without the GIL on a free-threaded build of CPython.
  So a wrapper never reads the items of a list in place, since another thread may change the list.
  It reads them through `sequence_snapshot`, which copies a list into a tuple, or it passes the list to the generic converter, which copies it too.
- A Python function passes its arguments to the export and returns its result.
  It never encodes or decodes bytes by hand: no slices, no integers or text to or from bytes, no JSON text.
  Lean then defines every value that crosses the boundary, and its proofs can cover that value.

`scripts/check_python_boundary.py` finds the usual forms of such conversions in `bindings/python/ethlib`.
With `--base`, it fails on any conversion on a line added since the merge base, committed or not.
Without it, it fails on any conversion in the package.
Both forms skip the conversions that `scripts/check_python_boundary_allowlist.txt` lists.
That list names the conversions that remain from before the rule.
A new entry is an exception that a maintainer approves, so the list only shrinks otherwise.

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

When you add or change a C export that reads a fork name, check that it rejects the forks whose rules EthLib lacks:

```bash
uv run --no-project --python 3.12 python scripts/check_fork_cap.py
```

An export caps its fork with `forkUpTo` in `EthLib/Base/Exports.lean`, which names the last fork whose rules the export holds.
Without the cap, a later fork would get the rules of the fork before it.
An export may read the fork without a cap only if its rule does not change at the next fork, or if it already rejects that fork.
Such an export goes in `scripts/check_fork_cap_allowlist.txt`, with the reason on the same line.
An entry that no longer reads a fork name fails the check, so remove it with the code.

When you touch test vectors or fixtures, also check their sources:

```bash
uv run --no-project --python 3.12 python scripts/check_fixture_pins.py
```

`tests/sources.toml` records one pinned commit for each repository that tests read from.
The check fails when a test cites another commit, and when a directory with a `SHA256SUMS` file does not name its sources.
The file also pins each release archive that is too large to vendor, by its URL, its size and its sha256.
The check fails when no test names an archive.

`tests/generators.toml` records which program computed the expected values of each pinned directory and archive.
Where no record names the program, it says so, with what was read.
It also lists the modules that the Python tests import, and the version of each one that computes expected values while the tests run.
The check fails when a directory or an archive has no entry, and when a pinned file belongs to no group of cases.
It also fails when a test imports a module that the file does not list.
A module that computes no expected value is a tool, and it needs a reason.
So a new vector directory, or a new library in the tests, comes with its generator.

The check downloads no archive.
With `ETHLIB_ARCHIVES` set, it also checks the groups of each archive against the member list in that cache.

Then check the layout of the Lean lines that your branch changes:

```bash
uv run --no-project --python 3.12 python scripts/check_lean_layout.py --base origin/master
```

It fails on a changed line longer than 100 characters, unless the line holds only a URL.
It also checks the pairs of lines in a comment where at least one line is changed.
It fails when a sentence runs from one line onto the next, and when two sentence lines touch.
Lines that your branch does not change are not checked.
A Lean file that git does not track yet counts as changed on every line.

With `--all` in place of `--base`, the check reads every line of every Lean file that git tracks.
`--rule wrap` runs only the check of wrapped sentences; the other rules are `length` and `touching`.
CI also runs `--all --rule wrap`, so no Lean file in the tree may hold a wrapped sentence.

These commands use uv and Python 3.12, with only the standard library.
See [prerequisites](README.md#prerequisites) for setup.

When you touch bindings or test vectors, also run the Python suite:

```bash
uv sync --frozen --extra test
uv run --no-sync pytest -n auto
```

The suite rewrites the vectors, so then check that the pinned ones are unchanged:

```bash
uv run --no-project --python 3.12 python tests/cryptography/check_vectors.py
```

A test marked `archive` reads a release archive, and the suite skips it by default.
To run such tests, set `ETHLIB_ARCHIVES` to a cache directory:

```bash
ETHLIB_ARCHIVES=~/.cache/ethlib/archives uv run --no-sync pytest -m archive
```

The first run downloads each archive that the tests name, and checks its size and digest.
Each test then unpacks only the paths that it reads.
The `vectors-slow` workflow runs these tests every Monday.

The parity tests in `bindings/python/tests/parity` are archive tests too.
They run every case of execution-spec-tests and consensus-spec-tests at the forks in scope.
A case passes, fails, waits for a runner, or disagrees for a reason listed in `tests/parity/disagreements.toml`.
Set `ETHLIB_PARITY_REPORT` to a file name to get the report of these outcomes for each fork and runner.

When you change Python code, format it, lint it and check its types and its spelling:

```bash
uv sync --frozen --extra test --group lint
uv run --no-sync ruff format
uv run --no-sync ruff check
uv run --no-sync ty check
git ls-files -z '*.py' | xargs -0 uv run --no-sync codespell
uv run --no-sync python scripts/check_raises.py
uv run --no-sync python scripts/check_docstrings.py
uv run --no-project --python 3.12 python scripts/check_python_boundary.py --base origin/master
uv run --no-project --python 3.12 python scripts/check_python_comments.py --base origin/master
```

A test expects an exception through `raises` of `bindings/python/tests/raising.py`, which matches the whole message.
Where the decoder computes a number from malformed bytes, `raises_shape` matches the whole message with any number at each `{n}` of its template.
`scripts/check_raises.py` fails on any other use of `pytest.raises`, except a bare call in a function that `scripts/check_raises_allowlist.txt` lists with its reason.
It also fails on a template with `|`, `.*`, a brace or a backslash outside `{n}`.

A Python module docstring is one line that says what the module is.
A fact that the code needs goes in a comment next to that code, or in the `--help` text of a script.
A class or function docstring is one line when possible.
Otherwise it has short sentences, one per line, with a blank line between groups.
`scripts/check_docstrings.py` fails on a module docstring of more than one line, and on a docstring sentence that wraps onto a second line.

A comment follows the same rule: each sentence fits on one line.
`scripts/check_python_comments.py` fails when a sentence of a comment runs onto the next line, and at least one of the two lines is changed.
A list item and a field of a provenance record, such as `Commit: <hash>`, continue no sentence.
After a line that ends with a colon, a line that starts in lowercase continues the sentence.
The check skips code blocks, table rows and lines that hold only a URL.
With `--all` in place of `--base`, the check reads every Python file that git tracks.
CI runs `--all`, so no Python file in the tree may hold a wrapped sentence.

`pyproject.toml` configures each tool, and `uv.lock` pins its version.

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

CI builds `tests/downstream`, a separate Lake package that requires EthLib, as a downstream project does.
Its file `Consumer.lean` states the declarations that such projects rely on, and unfolds the definitions whose bodies their proofs read.
When it fails, the change has altered that public surface.
Either keep the old declaration, statement or exposed body, or update `Consumer.lean` and mark the change breaking as above.

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
`pyproject.toml` declares `CC0-1.0 AND MIT AND Apache-2.0 AND Unicode-3.0` for the Python package.
It ships the MIT-licensed RLP, hex-prefix and trie test cases from `ethereum/tests`, and the Apache-licensed test sets from `C2SP/wycheproof`.
The normalization tables derive from Unicode 16.0.0 data under the Unicode License V3.
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

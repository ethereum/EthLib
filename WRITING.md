# Writing

This guide sets the standard for the English of EthLib.
Developers all over the world read EthLib, many of them in their second language, so its prose must be clear on the first reading.
The guide is based on ASD-STE100 Simplified Technical English (STE), Issue 9, January 2025.

STE is the reference for correcting prose, not for keeping it as it is.
A habit of this repository is not a reason to keep an unclear sentence.
Where EthLib departs from STE, the rule says so, and the [relation to STE](#relation-to-ste) gives the reason for each departure.

[CONTRIBUTING.md](CONTRIBUTING.md#writing) sets the requirements for a contribution, and this guide gives the details.
The [vocabulary](#vocabulary) records the technical terms of EthLib and the words to avoid.
[AGENTS.md](AGENTS.md#write-prose) gives an agent the steps to apply this guide.

## Scope

The guide applies to all prose in the repository and around it:

- Markdown files, such as this one, `README.md` and the README of a module.
- Lean doc comments and other comments.
- Comments in Python, C, shell scripts and workflows.
- Commit messages.
- Pull request and issue descriptions, and review comments.

Read the surrounding text before you change a passage.
Correct the defects in the passage that you change.
Rewrite unrelated prose in a separate pull request.

Some text keeps its exact form, and the rules do not apply to it.
Formulas, identifiers, commands, byte layouts, generated output and test-vector data stay exact.
Quotations from a source, official titles and legal text also stay as they are.
The legal text includes the sections of `CONTRIBUTING.md` on the license, copyright notices and material from other projects.
A heading or a table label can be a fragment, but it uses the same terms as the text.

A comment that copies the reference code of a specification is a quotation, so it keeps the wording of the specification.
The text around it, and any explanation that EthLib adds, follows this guide.

## How to use STE

STE has two parts: writing rules and a general dictionary.
The dictionary gives each general word its approved meanings and its part of speech.
A subject field adds its own technical nouns and technical verbs under STE rules 1.5 to 1.13.
Cryptographic and mathematical terms add to the dictionary, but they do not replace it.

Use the STE dictionary to find the approved meaning and part of speech of a general word.
Use the [vocabulary](#vocabulary) for the technical terms of EthLib.
A word that is missing from the vocabulary is not always a defect.
A familiar English word is not always approved in STE.
If a direct replacement changes the meaning, rewrite the sentence, or keep the technical term and explain it.

Technical accuracy comes first.
A rule can conflict with a term or a language pattern that is standard in cryptography research and engineering, in computer science or in mathematics.
In that case, keep the standard form, and apply the rules to the rest of the sentence.
A wording that is only a habit of this repository is not a standard form.

This guide adapts STE for EthLib.
It is not a complete copy of STE, and it does not claim that EthLib conforms to STE.
It does not distribute or check the official dictionary.

## Text types

The purpose of a text decides its type, not its Markdown form:

| Type | Purpose | Examples | Sentence limit |
| --- | --- | --- | --- |
| Procedural | Tell the reader how to do a task | Build and test steps, the rules for a contribution, agent steps | 20 words |
| Descriptive | Explain a definition, a result or a design | Doc comments, module READMEs, `SOUNDNESS.md`, commit and pull request bodies | 25 words |

A numbered list can describe results, and a paragraph can contain an instruction.
Apply the limit for the purpose of each sentence.
Keep commands apart from explanations and warnings.

## Rules

The identifiers below, such as W1, are EthLib labels.
The STE references give the source of each principle.
They do not claim that this page reproduces each source rule.
STE gives its general recommendations (GR) as advice.
This guide makes the recommendations that it names into requirements for EthLib.

### Words

- **W1.** Prefer an approved general word with the intended meaning and part of speech.
  Use the established technical term when the subject needs it.
  Rephrase the sentence before you make a replacement that changes the meaning.
  (STE 1.1 to 1.4, 9.1, 9.2)
- **W2.** Use a technical term with its recorded meaning and part of speech.
  Qualify the term when the passage could give it more than one meaning: "KZG proof" or "Lean proof", "finite field" or "structure field".
  (STE 1.5 to 1.13)
- **W3.** Use one term for one concept in a passage, and do not change between synonyms for variety.
  Use the term of the specification: if consensus-specs says "blob", do not also write "payload".
  (STE 1.11, 9.4)
- **W4.** Write a multi-word noun of three words or fewer.
  Split a longer noun group with a word such as "of", "for" or "on": "the batch verification of blob KZG proofs".
  Established terms and names, such as "BLS12-381 scalar field", follow W5.
  (STE 2.1, 2.2)
- **W5.** Write a long technical noun in full the first time, such as "Recursive Length Prefix (RLP)".
  Then use a clear short name, a defined abbreviation or a hyphenated form.
  Do not make an abbreviation only to shorten the text.
  (STE 2.2)
- **W6.** Use a direct verb instead of a phrasal verb when the meaning stays the same.
  For example, write "find" instead of "figure out", and "install" instead of "set up".
  (STE 9.3)
- **W7.** Write English words instead of Latin abbreviations in prose: "for example" instead of "e.g.", and "that is" instead of "i.e.".
  Official titles and quotations keep their form.
  (STE GR-6)
- **W8.** Use Oxford spelling in prose: British spelling with "-ize" endings, such as "behaviour", "serialize" and "analyse".
  American spelling is also correct.
  Keep one spelling within a file.
  Official names, identifiers, quotations and legal text keep their own spelling.
  Lean declaration names follow the American spelling of Mathlib.
  (STE 1.14, 9.4)
- **W9.** Use gender-neutral language when gender is not relevant.
  Use "they" for a person whose pronouns you do not know.
  (STE GR-7)

### Verbs

- **V1.** Prefer the simple tenses, the imperative and the infinitive.
  Do not use a complex verb form when a simple form gives the same information.
  Keep a time span or an uncertainty that the sentence needs: "the build may have failed" does not mean "the build failed".
  (STE 3.1 to 3.4, EthLib adaptation)
- **V2.** Use a verb form that ends in "-ing" only as a technical noun or as part of one.
  "Decoding succeeds only on canonical input" uses "decoding" as the name of an operation.
  Rewrite other uses, such as an "-ing" form with an object at the start of a sentence.
  "During" is a preposition, so this rule does not apply to it.
  (STE 3.5)
- **V3.** Use the active voice.
  Name the actor: a person, a tool, a protocol participant or a mathematical object, such as the decoder, the verifier, CI or the declaration check.
  Do not invent an actor.
  (STE 3.6)
- **V4.** In descriptive text, use the passive voice only when the actor is unknown.
  A past participle can describe a state without a passive construction: "the length is fixed".
  (STE 3.3, 3.6)
- **V5.** Use a verb, not an abstract noun, for an action.
  Write "the decoder rejects the input", not "the decoder performs a rejection of the input".
  (STE 3.7)
- **V6.** Write "that" after "prove", "show", "assume" or "make sure" when it separates a claim from the verb: "prove that decoding undoes encoding".
  Do not add it before an object: "prove the theorem".
  (STE GR-1)

### Sentences

- **S1.** Keep each sentence within the limit for its [text type](#text-types).
  Split a long sentence at a logical boundary, and keep all of its conditions and qualifications.
  The [word count](#word-count) says what counts as one word.
  (STE 5.1, 6.3)
- **S2.** Give a sentence one topic.
  Give a step one instruction, except for actions that must occur together.
  (STE 4.1, 5.2)
- **S3.** Put a condition before an instruction when the reader needs it first.
  For example: "If you change Lean or C sources, run `uv sync --frozen --extra test` again."
  (STE 5.4)
- **S4.** Use the imperative for a step.
  Keep an instruction, a requirement and a description apart.
  When you revise a requirement, keep the force of "must", "may" and "can".
  (STE 5.3, EthLib adaptation)
- **S5.** Keep the articles, subjects and verbs that a sentence needs.
  Do not use contractions.
  (STE 4.2, 4.5)
- **S6.** Connect related sentences with words, so that the reader can follow the argument.
  Do not expect punctuation alone to show the connection.
  (STE 4.4)
- **S7.** Give each pronoun a clear antecedent.
  After "this" or "these", name the object when the reference could be unclear.
  (STE GR-3, GR-4)
- **S8.** Put an instruction in the procedure, not in a note.
  Readers can skip a note, so use notes only for supporting information.
  (STE 5.5)

### Paragraphs and lists

- **P1.** Give each paragraph one topic, and introduce the topic before its details.
  (STE 6.4, 6.5)
- **P2.** Keep a paragraph to six sentences or fewer.
  Split it where the subject or the purpose changes.
  (STE 6.6)
- **P3.** Give information gradually.
  Define a term or a notation before an explanation uses it.
  (STE 6.1, 6.2)
- **L1.** Use a vertical list when it makes steps, cases or conditions easier to tell apart.
  A short series does not always need a list.
  (STE 4.3)
- **L2.** Introduce a list with a sentence that gives its purpose and ends with a colon.
  Each item connects to that introduction.
  An item can complete the introductory sentence or be a complete sentence.
  (STE 4.3)
- **L3.** Keep the grammar and the punctuation of the items in a list the same.
  Start each prose item with a capital letter, and keep the case of an identifier.
  Do not end an item with a comma or a semicolon.
  (STE 4.3)
- **L4.** Number the steps when their order matters.
  Do not number independent facts.
  (STE 5.2)

### Punctuation and emphasis

- **U1.** Do not use a semicolon in prose.
  Write two sentences, or join the clauses with a conjunction.
  Code keeps its own punctuation.
  (STE 8.1)
- **U2.** Do not use a dash to join two clauses.
  State the relation in words, or write two sentences.
  A dash can separate a term from its description.
  This rule does not apply to mathematical notation.
  (EthLib addition)
- **U3.** Use a hyphen to join words that are directly related, when the hyphen makes the term clearer: "byte-for-byte match".
  Keep the usual spelling of an established technical term.
  (STE 8.2)
- **U4.** Use parentheses for references, identifiers, abbreviations, short explanations and alternatives.
  Put the information that an instruction needs in the instruction itself.
  (STE 8.3)
- **U5.** Use emphasis for a term that you define, a label, a warning or a specific requirement.
  Do not emphasize a whole paragraph.
  (EthLib addition)

### Word count

STE 8.4 to 8.7 say how to count words.
A number, or a number with its unit such as "48 bytes", counts as one word.
So do an abbreviation, an alphanumeric identifier, quoted text, a title or label, a proper name and a group of hyphenated words.
Do not add hyphens or quotation marks to hide a long sentence.

Text in parentheses counts as one word in the sentence around it.
Check the text in the parentheses on its own for length.
For the count, a list introduction ends at its colon, and each list item counts separately.

EthLib also counts a formula, a command, a URL and a citation key as one word.
A citation of a document and its section, such as RFC 9380 §5.3.1, also counts as one word.
This adaptation keeps exact references whole, so that the limit does not push a writer to shorten them.
The text of an ordinary link keeps its words.
The checker only approximates these rules, so read the sentence when its count is in doubt.

### Claims and evidence

EthLib adds these requirements to the STE principles:

- **C1.** State only what the code, a theorem, a test or a check that you ran establishes.
  Name each check that you did not run.
- **C2.** Keep the strength of a claim.
  Keep its hypotheses, quantifiers, negations, bounds and exceptional cases, such as the condition `r + n >= p` of a theorem on public key recovery.
  Do not call a definition "verified" or "proved" when no theorem covers the property.
  Name the theorem and the property that it states instead.
- **C3.** Describe the library as it is in its reference documentation: the Markdown files, the module READMEs and the Lean comments.
  The history of a change belongs in the commit message and the pull request description.
- **C4.** Replace private session notes and planning codes with an explanation or a reference that a reader of the merged tree can follow.
- **C5.** Replace a quality claim with the fact or the evidence behind it.
  Words such as "robust" or "comprehensive" are not evidence.
- **C6.** Give the argument or a precise reference instead of "obvious" or "trivial".
  An established term such as "trivial group" can stay.
- **C7.** Remove repetition that gives the reader nothing new.
  Repeat a condition when the reader needs it at the point of use.
- **C8.** Make the source of each definition, value and claim traceable.
  Use the citation rules in [CONTRIBUTING.md](CONTRIBUTING.md#sources-of-truth).
- **C9.** Describe test evidence by what it pins.
  Say where the vectors come from, and which input and output a known answer fixes.
  A value that the code under test generated is not evidence that the code agrees with the specification.

### Mathematical and technical conventions

"Let", "fix" and "suppose" can introduce notation in an argument, and they do not give an instruction.
"We" can mean the author and the reader together in an argument.
A sentence that states a property, such as "the encoding is injective", is a description, not a passive construction.

The same word can be a technical noun and a technical verb.
This occurs when the word belongs to a technical noun category (STE 1.5) and to a technical verb category (STE 1.12).
"Hash" is an example: "the hash of the message" uses a noun, and "hash the message" uses a verb.
STE 1.7 and 1.13 then allow each use in its own role, so this is not an adaptation.
The vocabulary lists the noun and the verb uses separately.

Some words change their meaning between cryptography, Ethereum, mathematics and Lean, such as "proof", "field", "domain" and "root".
Qualify them when two meanings can occur in the same passage.
A cryptographic usage that is standard, such as "the signature verifies", stays as it is.

## Vocabulary

STE's general dictionary stays the reference for general words, their meanings and their parts of speech.
This section adds the technical terms of EthLib, and the words to avoid.
It is not a replacement for the dictionary, and it does not list every permitted word.

### Terms and context

These terms have more than one meaning in EthLib.
The table helps a reader find the intended meaning.
It does not forbid the ordinary meaning in a different context:

| Term | Technical use | Qualify when necessary |
| --- | --- | --- |
| specification | The published source that a module implements, such as an EIP, an RFC or consensus-specs. Also the Lean definitions that implement it, as in "a Lean project that imports the specification". | Name the source, for example "consensus-specs `v1.7.0-alpha.12`", or write "the Lean definitions" when both meanings occur. |
| source | The primary document that a definition cites | Write "source code" or "Lean source" for the files. |
| proof | A Lean proof, a mathematical proof, or a cryptographic object such as a KZG proof | Write "KZG proof" or "cell proof" for the object. Write "Lean proof" when both meanings occur. |
| verify | The verification operation of a signature or proof scheme, as in "verify a signature" | "Formally verified" refers to Lean theorems about the code, so name the theorem when a claim depends on it. Use "check" for a repository check, such as `lake exe check-decls`. |
| valid | A value that satisfies the predicate of its specification, such as `KeyValidate` | Name the predicate. Do not use "valid" for "well formed" or "canonical" unless they mean the same. |
| canonical | The only encoding that a decoder accepts for a value, as in RLP | Say which encoding, and what the decoder does with other input. |
| field | A finite field, a member of a Lean structure, or a field of an SSZ container | Write "scalar field", "base field", "structure field" or "container field". |
| domain | A layer directory under `EthLib/` (the `<Domain>` of the layout), an area of expertise, a signing domain, or the evaluation domain of a polynomial | Write "layer", "signing domain" or "evaluation domain" when the meanings can mix. |
| root | A Merkle root or hash tree root, a root of unity, or the root file of a Lean library | Write "hash tree root", "root of unity" or "library root". |
| module | A Lean file, an EthLib module such as `Rlp`, or a module over a ring | Write "Lean file" or "module system" when the distinction matters. |
| export | A C symbol that `@[export]` declares, or the Lean `export` command | Write "C export" when both can occur. |
| binding | The Python bindings, or the binding property of a commitment scheme | Write "the bindings" for the package, and "binding" only for the property. |
| fork | A protocol upgrade, such as Fulu, or a copy of a git repository | Name the fork, or write "git fork". |
| vector | A test vector, an SSZ `Vector`, or a Lean `Vector` | Write "test vector" in prose. Write the type in code font. |
| word | A 256-bit EVM word, or a word of a sentence | Write "EVM word" or `U256`. |
| commit | A git commit, or the act of committing to a polynomial | Write "commit to a blob" for the cryptographic act. |
| soundness | The trust gaps that `SOUNDNESS.md` lists, the soundness of a proof system, or the soundness of Lean's kernel | Name the property, or refer to the gap by its identifier, such as C2. |

### Technical nouns

The table gives examples from each subject field.
Keep the established term and its spelling, and introduce a long or unfamiliar term before its abbreviation:

| Field | Examples |
| --- | --- |
| Protocol | execution layer, consensus layer, fork, slot, epoch, block, transaction, gas, base fee, blob base fee, blob, cell, address, opcode, EVM word, precompile, gossip message ID |
| Serialization | Recursive Length Prefix (RLP), Simple Serialize (SSZ), byte string, list, container, canonical encoding, merkleization, hash tree root, varint, Snappy |
| Hashes | hash function, digest, Keccak-256, SHA-256, RIPEMD-160, BLAKE2b compression function, CRC-32C |
| Signatures | BLS signature, BLS12-381, G1 point, G2 point, pairing, aggregate signature, secp256k1, ECDSA, public key recovery, secret key, public key |
| Commitments | KZG commitment, KZG proof, cell proof, trusted setup, root of unity, evaluation domain |
| Hash-based signatures | XMSS, leanXMSS, one-time signature, chain, Merkle path, randomizer, epoch, VRF |
| Test evidence | test vector, known answer, pinned vector, digest manifest, fixture |
| Native bindings | C export, C extension, Python package, wrapper, object size |
| Soundness | trust gap, generated fact, axiom, standard axioms, kernel, compiler trust, declaration check, baseline |
| Lean | definition, theorem, lemma, declaration, doc comment, module system, public import, exposed definition, Lake library, tactic, `sorry`, `native_decide` |
| Repository | branch, commit, pull request, stacked pull request, build, check, CI, workflow |

Use the name of the source for a key: consensus-specs and BLS write "secret key", and SEC 1 writes "private key".
"Precompile" is a noun, short for a precompiled contract, and EthLib does not use it as a verb.

### Technical verbs

Use these verbs for the actions of their field, with one meaning in a passage.
They fit the technical verb categories of STE 1.12, mostly those for computer processes and for mathematical and scientific information.
Name the declaration or explain the operation when the meaning is not clear:

| Field | Examples of actions |
| --- | --- |
| Serialization | encode a value, decode bytes, serialize and deserialize an SSZ value, merkleize a value, reject malformed input |
| Signatures | hash a message, sign a message, verify a signature, aggregate signatures or public keys, recover a public key |
| Commitments | commit to a blob, compute a KZG proof, open a commitment, verify a proof |
| Protocol | process a slot, execute an opcode, charge gas, compute a base fee |
| Mathematics | prove a claim, define an object, assume a hypothesis, bound a quantity, evaluate a polynomial, interpolate values |
| Lean | unfold a definition, elaborate a term, compile a module, expose a definition, import a module, export a function |
| Repository | build a target, run a check, pin a test vector or a dependency, regenerate a generated fact, rebase a branch, review a pull request |

Follow the specification for the verb: SSZ "serializes" a value, and RLP "encodes" one.

### Words to avoid

The table gives prompts for an editing pass over ordinary prose.
It does not define which words STE approves.
Use a replacement only when it keeps the meaning and the part of speech.
Rewrite the sentence when a direct replacement does not work:

| Avoid | Use |
| --- | --- |
| "utilize", "leverage", "make use of" | use |
| "ensure" | make sure that, or name the condition and the action |
| "in order to" | to |
| "prior to", "subsequent to" | before, after |
| "in the event that" | if |
| "comprised of" | has, contains |
| "a number of", "various" | the number, or "some" when the number is not known |
| "e.g.", "i.e.", "etc." | for example, that is, the full list |
| "cf.", "resp.", "w.r.t.", "wlog" | compare, explicit pairs, with respect to, without loss of generality |
| "respectively" | explicit pairs when the reference would otherwise be unclear |
| "robust", "seamless", "comprehensive", "powerful", "elegant", "crucial" | the measurement or the reason |
| "clearly", "obviously", "trivially", "basically" | the reason, or nothing |
| "it is worth noting that", "it is important to" | nothing, when the phrase adds no information |
| "now", "no longer", "previously", "formerly", "currently", "new", "the fix", "as discussed" | in library reference text, the fact about the present library (rule C3) |

"The following are equivalent" is a permitted mathematical introduction.
Words such as "simply" and "essentially" occur in mathematical terms, such as "simply connected".
Read their meaning before you delete them.

### How to add a term

1. Find the term in the specification, in the Lean or Mathlib documentation, or in the mathematical source.
2. Prefer the established term over a local synonym.
3. Record its meaning and its part of speech when the word can be ambiguous.
4. Add a qualifier when two technical meanings occur in the same passage.
5. Add the term in the pull request that first needs it.

A noun and a verb with the same spelling need separate entries.
An entry for "hash" as a noun does not approve every use of "hash" as a verb.
An example from a field is not a reason to reject another established term of that field.

## Examples

These examples come from EthLib's own prose.
They show when to revise a sentence and when to keep it:

| Before | After | Reason |
| --- | --- | --- |
| "A type is described by a *declaration*, and the data it holds by a *value*; the two are separate pieces of data." | A *declaration* describes a type, and a *value* holds its data. They are two separate pieces of data. | Name the actor (V3), and write two sentences instead of a semicolon (U1). |
| "Matching a client byte for byte is a useful test, not a justification." | A byte-for-byte match with a client is a useful test, not a justification. | An "-ing" form with an object is a verb, not a technical noun (V2). |
| "- **P**, a Lean proof that imports the specification;" | - **P**: a Lean proof that imports the specification. | A list item does not end with a semicolon (L3, U1). |
| "No theorem states what the signature functions return; in particular, none says that an honest aggregate signature verifies." | No theorem states what the signature functions return. In particular, no theorem says that an honest aggregate signature verifies. | Write two sentences (U1), and repeat the noun instead of "none" (S7). |
| "i.e. because Z(x) vanishes on (part of) the FFT domain itself" | that is, because Z(x) vanishes on part of the FFT domain itself | EthLib added this clause to a copied comment, so the guide applies to it (W7). |
| "This will be referred to as the FFT domain." | Keep as written. | The comment copies the reference code of consensus-specs, so it is a quotation. |
| "Decoding succeeds exactly on strings of 1056 bytes" | Keep as written. | "Decoding" names an operation, so it is a technical noun (V2). |
| "Since that release, `specs/altair/bls.md` has changed only in style." | Keep as written. | The perfect tense gives the time span from the release, and a simple tense would lose it (V1). |
| "a signature from the signing operation of SEC 1 verifies" | Keep as written. | "The signature verifies" is a standard usage in cryptography. |

Compare each rewrite of a mathematical or cryptographic statement with its source.
A shorter sentence is not better if it changes the statement.

## Relation to STE

| Source | Use in EthLib |
| --- | --- |
| STE 1.1 to 1.4, general vocabulary | Kept as the reference for general meanings and parts of speech. This guide and its checker do not contain the dictionary. |
| STE 1.5 to 1.13, technical terms | Applied through the vocabulary and the established usage of each subject field. |
| STE 1.7, 1.12 and 1.13, noun and verb roles | Applied as written: a word such as "hash" can be a technical noun and a technical verb when each use belongs to its category. |
| STE 1.14, spelling | STE 1.14 permits another official spelling directive. EthLib uses Oxford spelling and also accepts American spelling. Lean declaration names follow Mathlib. Legal text keeps its own spelling. |
| All STE rules | Technical accuracy comes first. A term or a language pattern that is standard in cryptography, computer science or mathematics stays when a rule conflicts with it. |
| STE 2 to 6, 8 and 9 | The source principles inform the rules above. Notation and the stated adaptations keep the technical meaning. |
| STE 3.1 to 3.4, verb forms (V1) | Adapted: simple forms stay preferred, but a modal or complex form stays when a simple form would lose an uncertainty or a time span. |
| STE 5.3, instructions (S4) | Adapted: a requirement keeps its "must", "may" or "can", because contribution rules state obligations as well as steps. |
| STE 7, safety instructions | Applied to risky operations, such as a command that rewrites the test vectors: the condition or the instruction comes before the explanation of the result. |
| STE 8.6, word count | Adapted: formulas, commands, URLs, citation keys and citations of a document and its section count as one word, so that exact references stay whole. |
| STE general recommendations | The recommendations named above are requirements of this guide, not STE rules. |
| EthLib additions | The claims and evidence rules (C1 to C9), the rule against dashes between clauses (U2) and the rule on emphasis (U5) are EthLib policies. |

ASD owns the standard, and [ASD's official Issue 9](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf) gives the full rules and the dictionary.
This guide paraphrases the rules and takes its examples from EthLib.
It does not reproduce the dictionary or claim a certification.

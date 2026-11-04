# Writing Guide

This guide helps you write clear, precise, correct technical text.
Its rules are advice.
If a passage is clear and correct, leave it alone, even if it does not follow a rule or the checker reports it.
Accuracy comes first, then clarity.
An existing repository convention is not a reason to keep unclear writing.

[CONTRIBUTING.md](CONTRIBUTING.md) owns the contribution requirements.
The [vocabulary](#vocabulary) clarifies technical meanings, and [Write prose](AGENTS.md#write-prose) describes the editing workflow.
This guide adds no second set of requirements.

## Scope

Use this advice when you add or revise documents, doc comments, other comments, commit messages, pull request and issue text, and review comments.
Read the surrounding text for context.
Correct related defects that affect the passage, and keep unrelated rewrites in a separate change.

Keep formulas, identifiers, commands, byte layouts, source quotations, generated output and test-vector data exact.
Official titles and legal text also retain their wording.
The legal text includes CONTRIBUTING's Licence, Copyright notices and Material from other projects sections.
Headings and table labels can be fragments, with clear and consistent terms.

A quotation retains its source wording.
Preserving a quotation does not make its source normative; CONTRIBUTING's [source policy](CONTRIBUTING.md#sources-of-truth) still governs citations.
Apply writing advice to the surrounding explanation when it improves clarity.

## How to use STE

This guide draws on ASD-STE100 Simplified Technical English (STE), Issue 9, and adapts it freely for EthLib.
It claims no STE conformance and does not distribute or check the official dictionary.
Use the project vocabulary to clarify meanings, not to decide which English words are permitted.

Technical accuracy takes priority over the rules in this guide.
A rule can conflict with a term or language pattern that is standard in cryptography, computer science or mathematics.
In that case, keep the standard form and apply the rules to the rest of the sentence.
A wording that is only a habit of this repository is not a standard form.

## Text types

Choose a text type from its purpose, not its Markdown form:

| Type | Purpose | Examples | Suggested sentence length |
| --- | --- | --- | --- |
| Procedural | Tell the reader how to do a task | Build instructions, contributor tasks, agent steps | 20 words |
| Descriptive | Explain a definition, result or observation | Doc comments, module READMEs, contribution bodies | 25 words |

A numbered list can describe results, and a paragraph can contain an instruction.
Use these lengths as prompts to review a sentence, not targets that require a rewrite.
Keep commands distinct from explanations and warnings.

## Rules

The labels below, such as W1, belong to EthLib.
STE references identify source principles, not exact equivalence to those rules.
All the advice below serves clarity and correctness.
A checker suggestion alone does not require an edit.

### Words

- **W1.** Prefer a common, simple word with the intended meaning.
  Use an established technical term when the subject requires it.
  Rephrase if a replacement would change the meaning.
  (STE 1.1 to 1.4, 9.1, 9.2)
- **W2.** Use a technical term with its recorded meaning and part of speech.
  Qualify the term when the passage could give it more than one meaning: "KZG proof" or "Lean proof", "finite field" or "structure field".
  (STE 1.5 to 1.13)
- **W3.** Use one term for one concept within a passage.
  Do not rotate synonyms for variety.
  Follow the normative source: if it says "blob", do not also write "payload".
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
- **V3.** Use the active voice.
  Name the person, tool, participant or mathematical object that performs the action.
  Make clear who or what does each action, and do not invent an actor.
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

- **S1.** Review sentences longer than the suggested length for their text type.
  Split at a logical boundary if that makes the sentence clearer, and keep its conditions and qualifications.
  The [word count](#word-count) describes the checker's estimates.
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

STE 8.4 to 8.7 describe word counting.
Numbers with their units, abbreviations, alphanumeric identifiers, quoted text, titles, labels, proper names and hyphenated groups count as one word.
A formula counts as quoted text, so it also counts as one word.
Do not add quotation marks or hyphens to hide a long sentence.

Parenthetical text counts as one word in the sentence around it, and is also reviewed separately.
A list introduction ends at its colon for the count, and each item counts separately.

EthLib also groups a Lean expression, command, URL, citation key, or document reference with its section as one word.
For example, a reference such as RFC 9380 §5.3.1 stays whole.
Ordinary link text retains its words.
These conventions help review sentences; they are not a conformance test.
The checker only approximates them.

### Claims and evidence

This advice helps authors describe claims and evidence accurately.
The actual source, proof, citation and testing requirements remain in CONTRIBUTING:

- **C1.** State only what the code or recorded evidence establishes.
  Identify conditional results and checks that you did not run.
- **C2.** Preserve the strength of a claim: hypotheses, quantifiers, negations, bounds and exceptional cases.
  For example, keep the condition `r + n >= p` in the public-key recovery result.
  Name the theorem and property instead of calling an uncovered definition "verified" or "proved".
- **C3.** Describe the present library in reference documentation.
  Change history belongs in commit messages, contribution descriptions and documents whose purpose is to record history.
- **C4.** Replace private session notes and temporary planning codes with explanations or maintained references that readers can find.
- **C5.** Replace unsupported quality claims with facts or evidence.
  Words such as "robust" or "comprehensive" do not supply evidence.
- **C6.** Give an argument or a precise reference instead of "obvious" or "trivial".
  Established technical names such as "trivial group" remain permitted.
- **C7.** Remove repetition that adds no useful context.
  Repeat a condition when readers need it at the point of use.
- **C8.** Make the source of each definition, value and claim traceable.
  Follow [Sources of truth](CONTRIBUTING.md#sources-of-truth).
- **C9.** Describe test evidence by what it pins and where its vectors come from.
  Follow [Known answers](CONTRIBUTING.md#known-answers) for their placement and provenance.
  A value generated by the code under test does not establish agreement with the specification.

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

Use this vocabulary to clarify technical meanings and wording.
It is not a dictionary of permitted English words and does not list every established term.
Qualify a term when two meanings can occur in the same passage.

### Terms and context

These terms have more than one meaning in EthLib.
The table helps a reader find the intended meaning.
It does not forbid the ordinary meaning in a different context:

| Term | Technical use | Qualify when necessary |
| --- | --- | --- |
| specification | A published normative source, such as an EIP, RFC, NIST or SEC standard, or the executable Lean definitions of EthLib. | Name the document or write "the Lean definitions" when both meanings occur. Follow CONTRIBUTING for source authority. |
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

Use the key name from the applicable standard, and explain a qualifier when "secret key" and "private key" occur together.
"Precompile" is a noun, short for a precompiled contract, and EthLib does not use it as a verb.

### Technical verbs

Use verbs with a clear meaning in their field.
These examples are not a list of permitted uses.
Name the declaration or explain the operation when its meaning is unclear:

| Field | Examples of actions |
| --- | --- |
| Serialization | encode a value, decode bytes, serialize and deserialize an SSZ value, merkleize a value, reject malformed input |
| Signatures | hash a message, sign a message, verify a signature, aggregate signatures or public keys, recover a public key |
| Commitments | commit to a blob, compute a KZG proof, open a commitment, verify a proof |
| Protocol | process a slot, execute an opcode, charge gas, compute a base fee |
| Mathematics | prove a claim, define an object, assume a hypothesis, bound a quantity, evaluate a polynomial, interpolate values |
| Lean | unfold a definition, elaborate a term, compile a module, expose a definition, import a module, export a function |
| Repository | build a target, run a check, pin a test vector or a dependency, regenerate a generated fact, rebase a branch, review a pull request |

Follow the applicable specification for the verb: SSZ "serializes" a value, and RLP "encodes" one.

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

Find the term in its normative source, Lean or Mathlib documentation, or mathematical literature.
Prefer the established term over a local synonym.
Record its meaning and grammatical role when ambiguity matters, and add a qualifier when two technical meanings occur together.
Noun and verb examples can help distinguish uses, but an example is not a reason to reject another established term.

## Examples

These examples show when a revision helps and when clear wording can stay:

| Before | After | Reason |
| --- | --- | --- |
| "We utilize the lemma." | We use the lemma. | Prefer the common word when the meaning stays the same. |
| "Matching a client byte for byte is a useful test, not a justification." | Keep as written. | The sentence is clear and preserves the source-authority distinction. |
| "The build may have failed." | Keep as written. | Preserve uncertainty and past time. |
| "The following are equivalent." | Keep as written. | Keep a conventional mathematical introduction when its reference is clear. |
| "This will be referred to as the FFT domain." | Keep as written when quoting the source. | A quotation keeps its wording; source authority still follows CONTRIBUTING. |
| "a signature from the signing operation of SEC 1 verifies" | Keep as written. | "The signature verifies" is established cryptographic usage. |

Use [Write prose](AGENTS.md#write-prose) to compare complete passages with their sources.
A shorter sentence is not better if it changes the statement.

## STE source

ASD owns ASD-STE100 Simplified Technical English.
[ASD's official Issue 9](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf) contains the rules and dictionary.
This guide adapts its principles for EthLib and claims no STE conformance.
It does not reproduce or check the official dictionary.

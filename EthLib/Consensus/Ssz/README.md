# SSZ

Simple Serialize, the encoding and Merkleization of Ethereum's consensus objects, with machine-checked codec and Merkle-tree proofs.
Types are represented as data, so one encoder, decoder, and merkleizer cover the implemented universe.

## Reading this module

The executable specification and the proofs about it live in two separate trees, and only the first is meant to be read.

```text
EthLib/Consensus/Ssz/           the executable specification
EthLib/Consensus/Proofs/Ssz/    the machine-checked properties of it
```

The proofs mirror the layout of the specification: what is proved about `Ssz.Codec.Serialize` sits in `Proofs.Ssz.Codec.Serialize`.
An implementer reads `Ssz/` and stops there; [Proven properties](#proven-properties) below says in prose what the other tree establishes.

```text
Ssz/Type      declarations, values, well-formedness, defaults, and paths
Ssz/Codec     serialization, deserialization, the JSON mapping, layouts, roots, and proofs
Ssz/Merkle    bounded and progressive trees, indices, and verification
```

Hashing uses `EthLib.Cryptography.Hash.Sha256`.

The conformance harness lives in [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs), under `lean/`.
It runs this specification against the released test vectors, and against the Python implementation on generated cases.

## Scope

The type universe covers unsigned integers, booleans, byte sequences, bitfields,
vectors, lists, containers, progressive collections, and compatible unions.
Legacy positional unions, including their nullable first option, are not implemented.

The reference is the Python implementation in [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs), which serves as the official specification,
together with [EIP-7495](https://eips.ethereum.org/EIPS/eip-7495),
[EIP-7916](https://eips.ethereum.org/EIPS/eip-7916), and
[EIP-8016](https://eips.ethereum.org/EIPS/eip-8016).
The prose it replaced is the [last SSZ text in consensus-specs](https://github.com/ethereum/consensus-specs/blob/802485ec74a6986542bd53bf153189623aab440c/ssz/simple-serialize.md).

Declarations and values are separate data.
Call `Desc.wellFormed` before using an externally supplied declaration.
The low-level operations do not repeat declaration validation at every recursive step.
A successful encoding establishes that its value fits a well-formed declaration.
Proof requests deliberately reject the root itself, empty requests, duplicate indices,
and ancestor/descendant pairs.
This is stricter than the generalized-index arithmetic in the reference proof helpers.

A progressive collection may declare a limit, which rules on its count alone.
The spine is laid out from the data either way, so a declared bound never reaches the root.

For example, a progressive container with layout `[true, false, true]` has two fields.
Its serialization contains only those two fields.
Its Merkle tree contains three positions: the first field, a zero leaf, and the second field.
The layout is mixed into the root so an absent field differs from a present zero-valued field.

### The JSON mapping

An SSZ schema defines a JSON encoding as well as a byte encoding, and both are implemented here.

SSZ gives the byte alias and a one-byte unsigned integer the same type; the JSON mapping does not,
writing the alias as a hex string where it writes the integer as decimal digits in a string.
A declaration alone therefore does not say which document a value is written as, so the mapping
takes a *spelling* beside the declaration: one node per node, marking where the alias was used.
A declaration that never uses the alias needs no spelling of its own.

Only the spelling the mapping gives is accepted, which is stricter than the Python implementation twice:

| The document | Here | The Python implementation |
| --- | --- | --- |
| A bitfield or byte sequence written as an array of its elements | Refused as an element of the wrong kind | Accepted, on all three kinds |
| A hex byte string with no `0x` | Refused | Accepted on a byte array, refused on a bitfield |

Both are leniency in the reference rather than anything the mapping spells, and no vector asserts
either: the invalid vectors that write an array assert only the name the refusal carries.

## Proven properties

- [Codec equivalence](../Proofs/Ssz/Codec/Canonicality.lean): encoding and decoding describe the same relation for every well-formed implemented type.
  Values survive round trips, and every accepted byte string is canonical.
- [Admissibility](../Proofs/Ssz/Codec/DecodeFits.lean): successful decoding produces a value of the declared shape.
  Successful encoding also establishes admissibility for well-formed declarations.
- [Encoding sizes](../Proofs/Ssz/Codec/Size.lean): structural byte counts and the four-byte offset bounds characterize successful serialization of admissible values, with exactly the predicted size.
  An admissible value can fail serialization only through offset overflow.
- [Defaults](../Proofs/Ssz/Type/DefaultLaws.lean): every successfully constructed default fits its declaration.
  The executable admissibility check agrees with the logical predicate for well-formed declarations.
- [Compatibility](../Proofs/Ssz/Type/CompatibilitySymmetry.lean): checks are reflexive and symmetric, and matching progressive field positions preserve names and compatible types.
  Compatibility is deliberately not transitive, as a checked counterexample demonstrates.
  [Shared addresses](../Proofs/Ssz/Type/CompatibilityIndices.lean): compatible progressive containers place a field of one name at one generalized index, so appending fields leaves earlier fields where a proof can still read them.
  Every option a union declares is compatible with every other, and each hangs at the same node whichever option the value carries.
- [Byte aliases](../Proofs/Ssz/Codec/Aliases.lean): byte arrays and sequences of eight-bit integers encode, decode, and root alike, refusals included.
- [Tree construction](../Proofs/Ssz/Merkle/Tree.lean): executable bounded and progressive trees agree with their mathematical definitions.
  Padding, subtree extraction, and upward construction preserve roots at arbitrary depths.
  [Merkleization cost](../Proofs/Ssz/Merkle/MerkleizeCost.lean): merkleizing a nonempty `k` chunks under a width of `w` costs fewer than `2 * k + log2 w` hashes, so a capacity far above the data adds only its logarithm.
  The hashes counted are the ones the implementation performs, established through a counting twin of the recursion that produces the same root.
  Materializing every leaf instead would cost `w - 1`, which is what the precomputed zero subtrees save.
  [Progressive levels](../Proofs/Ssz/Merkle/ProgressiveLevels.lean): a chunk of a progressive collection keeps its index however long the collection grows, and sits three levels deeper per factor of four.
- [Value roots](../Proofs/Ssz/Codec/RootDomain.lean): every admissible value of a well-formed type has a 32-byte root, independently of serialization's offset limit.
- [Constructed branches](../Proofs/Ssz/Codec/ProofCorrectness.lean): a branch built for any readable node reconstructs the value's root and passes verification, including across nested type boundaries.
- [Multiproofs](../Proofs/Ssz/Merkle/Multiproof.lean): the computed helper frontier suffices for reconstruction, and proofs read from a finite tree rebuild its root.
  [Construction from values](../Proofs/Ssz/Codec/MultiproofConstruction.lean) derives helper readability and reconstruction directly from successful value roots and claimed-node reads.
  No parent equations are required below leaves.
  [Multiproof size](../Proofs/Ssz/Merkle/MultiproofSize.lean): the helper count and twice the claim count together come to the number of distinct claim ancestors plus two, which fixes the count exactly for any claim set at one depth.
  Claiming a whole level therefore needs no helpers, and claiming any `k` nodes of a level of depth `d` needs at most `k * (d - log2 k)`.
  A run of `k` consecutive claims still needs at least `d - log2 k`.
  [Single claims](../Proofs/Ssz/Merkle/Singleton.lean): the helpers of one claim are its branch in the same order, and a single-item proof gets the same verdict from the multi-item verifier.
- [Type paths](../Proofs/Ssz/Codec/PathSelection.lean): recursive selections through present fields and elements agree with the value walker across every supported type family.
  Packed elements select their containing chunk, reserved steps select mixing words, and union descent follows the active option.
  A type-only index can name an absent position without asserting that a value is present; every readable padding node remains covered by the general branch theorem.
- [Authentication](../Proofs/Ssz/Merkle/Authentication.lean): two accepted branches at the same index and root either open the same leaf or exhibit a SHA-256 collision between actual 64-byte branch inputs.
  [Multiproof binding](../Proofs/Ssz/Merkle/MultiproofBinding.lean) gives the same guarantee for shared claims across different requests, with collision witnesses from the verifier's hash inputs.
- [Whole-value binding](../Proofs/Ssz/Codec/Binding.lean): admissible values of the same well-formed type with equal roots are equal, or their Merkle computations contain distinct 64-byte inputs with equal SHA-256 hashes.
  [CommitmentSized](../Proofs/Ssz/Codec/BindingDomain.lean) requires every nested variable collection count to fit its 256-bit mixing word.
  The proof recovers lengths, selectors, packed data, and nested values; callers supply no tree-alignment assumption.
  [Layout separation](../Proofs/Ssz/Codec/LayoutSeparation.lean): two legal progressive containers with different layouts and one root expose a SHA-256 collision between 64-byte inputs.
  [Layout words](../Proofs/Ssz/Codec/LengthBinding.lean): legal layouts of any lengths with equal mixed-in words are equal, so an absent field never shares a root with a zero value.
- [Summaries](../Proofs/Ssz/Codec/Summary.lean): replacing a value nested in a struct, a progressive struct, or a union by any value with the same root leaves the outer root unchanged.
  A vector, list, or progressive list of composite elements has the same root as the same collection holding each element's root as a 32-byte array.
  Replacing a struct field by a 32-byte array holding its root is the special case, and deeper summaries follow by repeating the replacement.
  A party holding only the summary computes the root a party holding the value computes, so a proof about anything inside the replaced value verifies against both.
- [The JSON mapping](../Proofs/Ssz/Codec/JsonRoundTrip.lean): a document written for an admissible value of any well-formed type reads back as that value, at every shape of the universe.
  [Basic shapes](../Proofs/Ssz/Codec/JsonLaws.lean) cover booleans, all six integer widths, the byte alias, both byte arrays, and all three bitfields.
  A bitfield is the hex of its own encoding, so its case is the codec round trip.
  [Hex](../Proofs/Ssz/Codec/JsonHex.lean): a hex string the mapping wrote reads back as the bytes it came from.
  Objects: a name written into one is read back from it, and every name an object carries is one it was written from, so a written struct never trips the undeclared-field refusal.
  The mapping is deliberately not canonical, and a checked counterexample gives two documents for one value.
  [Missing fields](../Proofs/Ssz/Codec/JsonLaws.lean): a container or progressive container document that leaves out a declared field is refused.
- [SHA-256](../../Cryptography/Proofs/Hash/Sha256.lean): roots hash with `EthLib.Cryptography.Hash.Sha256`, which is proved equal to FIPS 180-4 on every message shorter than 2^61 bytes, with its constants derived from prime roots.

### Domains and limits

Composite serialization and deserialization both require fewer than 2^32 bytes at each composite level.
Byte arrays are sequences of bytes, so they meet the same limit, though they write no offset table.
Roots meet no such limit.
A union adds its selector byte to the chosen option's encoding.
These distinctions are part of the mathematical size relation, rather than implicit machine-size assumptions.

Commitment binding has a separate length domain: variable collection counts must be below 2^256 at every nesting level.
`Fits` expresses value shape and declared capacities; `CommitmentSized` expresses exact length-word representability.
The low-level `lengthWord` keeps the low 256 bits outside that domain, so unrestricted root totality does not imply unrestricted binding.
SSZ does not separate roots by type; the whole-value theorem compares values under one declaration.
Its finite hash computation expands cached zero subtrees, preserving their mathematical hashes.

## Trust boundary

The proofs establish the stated properties of the formal definitions.
Agreement between those definitions and the English SSZ specification remains a review obligation.
No theorem assumes SHA-256 is injective or collision-free.

Kernel checking trusts Lean's kernel and standard logical foundations.
`lake exe check-decls` checks the axioms of every declaration, and that no definition runs compiled code other than itself.
The package is a foundation for a later implementation-refinement proof; such a proof must still relate that implementation's byte operations, errors, and resource limits to this model.

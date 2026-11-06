# SSZ

Simple Serialize (SSZ) is how the consensus layer turns its objects into bytes, and into 32-byte Merkle roots.
The bytes travel over the network and sit on disk.
The root commits to the whole object, so that a short proof can show one field of it to someone who holds only the root.

This module specifies both, with machine-checked proofs about the codec and the Merkle trees.
Types are represented as data, so a single encoder, decoder and merkleizer cover every type the module implements.

## Reading this module

The executable specification and the proofs about it live in two separate trees, and only the first is meant to be read.
`EthLib/Serialization/Ssz/` holds the executable specification, and `EthLib/Serialization/Proofs/Ssz/` holds the machine-checked properties of it.
The proofs mirror the layout of the specification: what is proved about `Ssz.Codec.Serialize` sits in `Proofs.Ssz.Codec.Serialize`.
An implementer reads `Ssz/` and stops there, and [Proven properties](#proven-properties) says in prose what the other tree establishes.

The specification has four parts:

| Directory | Contents |
| --- | --- |
| `Ssz/Type` | declarations, values, well-formedness, defaults, and paths |
| `Ssz/Codec` | serialization, deserialization, the JSON mapping, layouts, roots, and proofs |
| `Ssz/Merkle` | bounded and progressive trees, indices, and verification |
| `Ssz/Typed` | Lean types as SSZ types, encoded and rooted through the codec |

Hashing uses `EthLib.Cryptography.Hash.Sha256`.

The perfect trees and branch climbs are the Merkle trees of [`EthLib.Cryptography.Merkle`](../../Cryptography/Merkle/), hashing every node alike.

The conformance harness lives in [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs), under `lean/`.
It runs this specification against the released test vectors, and against the Python implementation on generated cases.

## Scope

The type universe covers unsigned integers, booleans, byte sequences, bitfields, vectors, lists, containers, progressive collections, and compatible unions.
Legacy positional unions, including their nullable first option, are not implemented.

The reference is the Python implementation in [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs), which serves as the official specification, together with [EIP-7495](https://eips.ethereum.org/EIPS/eip-7495), [EIP-7916](https://eips.ethereum.org/EIPS/eip-7916), and [EIP-8016](https://eips.ethereum.org/EIPS/eip-8016).
The prose it replaced is the [last SSZ text in consensus-specs](https://github.com/ethereum/consensus-specs/blob/802485ec74a6986542bd53bf153189623aab440c/ssz/simple-serialize.md).

A type is described by a *declaration*, and the data it holds by a *value*; the two are separate pieces of data.
A declaration that comes from outside must be checked with `Desc.wellFormed` before it is used, because the low-level operations do not repeat that check at every recursive step.
A successful encoding establishes that its value fits a well-formed declaration.

Proof requests deliberately reject the root itself, empty requests, duplicate indices, and ancestor/descendant pairs.
This is stricter than the generalized-index arithmetic in the reference proof helpers.

A progressive collection is one whose Merkle tree grows with its data instead of being sized in advance.
It may declare a limit, which rules on its count alone.
Its spine is laid out from the data either way, so a declared bound never reaches the root.

A progressive container also carries a *layout*, a list of booleans saying which of its declared positions are present.
Take a progressive container with layout `[true, false, true]`.
It has two fields, and its serialization contains only those two.
Its Merkle tree, though, has three positions: the first field, a zero leaf, and the second field.
The layout is mixed into the root, so that an absent field differs from a present field whose value is zero.

### The JSON mapping

An SSZ schema defines a JSON encoding as well as a byte encoding, and both are implemented here.

SSZ gives the byte alias and a one-byte unsigned integer the same type, but the JSON mapping does not.
It writes the alias as a hex string, and the integer as decimal digits in a string.
A declaration alone therefore does not say how a value is written in JSON.
So the mapping takes a *spelling* beside the declaration, with one node for each node of the declaration, marking where the alias was used.
A declaration that never uses the alias needs no spelling of its own.

Only the spelling the mapping gives is accepted, which makes it stricter than the Python implementation in two cases:

| The document | Here | The Python implementation |
| --- | --- | --- |
| A bitfield or byte sequence written as an array of its elements | Refused as an element of the wrong kind | Accepted, on all three kinds |
| A hex byte string with no `0x` | Refused | Accepted on a byte array, refused on a bitfield |

Both are leniency in the reference rather than anything the mapping spells, and no vector asserts either.
The invalid vectors that write an array assert only the name the refusal carries.

## Proven properties

### The codec

The first group of results says that the byte encoding is exact.
[Codec equivalence](../Proofs/Ssz/Codec/Canonicality.lean) shows that encoding and decoding describe the same relation for every well-formed implemented type.
Values survive round trips, and every byte string the decoder accepts is canonical.

A value that decodes also has the right shape.
By [admissibility](../Proofs/Ssz/Codec/DecodeFits.lean), successful decoding produces a value of the declared shape, and for well-formed declarations successful encoding establishes the same.

[Encoding sizes](../Proofs/Ssz/Codec/Size.lean) characterizes successful serialization of admissible values by structural byte counts and the four-byte offset bounds, and the encoding has exactly the predicted size.
An admissible value can fail to serialize only through an offset overflow.

For [defaults](../Proofs/Ssz/Type/DefaultLaws.lean), every successfully constructed default fits its declaration.
The executable admissibility check agrees with the logical predicate for well-formed declarations.

[Byte aliases](../Proofs/Ssz/Codec/Aliases.lean) shows that byte arrays and sequences of eight-bit integers encode, decode, and root alike, refusals included.

### Compatibility

Two declarations are *compatible* when they use compatible Merkle layouts, which `isCompatible` checks.
The [compatibility](../Proofs/Ssz/Type/CompatibilitySymmetry.lean) checks are reflexive and symmetric, and matching progressive field positions preserve names and compatible types.
Compatibility is deliberately not transitive, as a checked counterexample shows.

What compatibility buys is [shared addresses](../Proofs/Ssz/Type/CompatibilityIndices.lean).
Compatible progressive containers place a field of one name at one generalized index, so appending fields leaves earlier fields where a proof can still read them.
Every option a union declares is compatible with every other, and each hangs at the same node whichever option the value carries.

### Merkle trees

The [tree construction](../Proofs/Ssz/Merkle/Tree.lean) results show that the executable bounded and progressive trees agree with their mathematical definitions.
Padding, subtree extraction, and upward construction preserve roots at arbitrary depths.

The [Merkleization cost](../Proofs/Ssz/Merkle/MerkleizeCost.lean) result bounds the work.
Merkleizing a nonempty run of `k` chunks under a width of `w` costs fewer than `2 * k + log2 w` hashes, so a capacity far above the data adds only its logarithm.
The hashes counted are the ones the implementation performs, established through a counting twin of the recursion that produces the same root.
Materializing every leaf instead would cost `w - 1` hashes, which is what the precomputed zero subtrees save.

For [progressive levels](../Proofs/Ssz/Merkle/ProgressiveLevels.lean), a chunk of a progressive collection keeps its index however long the collection grows, and it sits three levels deeper per factor of four.

Every admissible value of a well-formed type has a 32-byte root, as [value roots](../Proofs/Ssz/Codec/RootDomain.lean) shows, independently of the offset limit of serialization.

### Proofs of membership

A *branch* is the list of sibling hashes that links one node of the tree to the root.
By [constructed branches](../Proofs/Ssz/Codec/ProofCorrectness.lean), a branch built for any readable node reconstructs the value's root and passes verification, including across nested type boundaries.

A *multiproof* proves several nodes at once, sharing the hashes their branches have in common.
For [multiproofs](../Proofs/Ssz/Merkle/Multiproof.lean), the computed set of helper nodes suffices for reconstruction, and proofs read from a finite tree rebuild its root.
[Construction from values](../Proofs/Ssz/Codec/MultiproofConstruction.lean) derives the readability of the helpers and the reconstruction directly from successful value roots and reads of the claimed nodes.
No parent equations are required below the leaves.

The [multiproof size](../Proofs/Ssz/Merkle/MultiproofSize.lean) result counts the helpers exactly.
Take claims that all sit at one depth, and count the distinct nodes on their paths below the root, the claims included.
The helper count plus twice the claim count equals that node count plus two.
Claiming a whole level therefore needs no helpers, and claiming any `k` nodes of a level of depth `d` needs at most `k * (d - log2 k)`.
A run of `k` consecutive claims still needs at least `d - log2 k`.
By [single claims](../Proofs/Ssz/Merkle/Singleton.lean), the helpers of one claim are its branch in the same order, and a single-item proof gets the same verdict from the multi-item verifier.

[Type paths](../Proofs/Ssz/Codec/PathSelection.lean) shows that recursive selections through present fields and elements agree with the value walker across every supported type family.
Packed elements select their containing chunk, reserved steps select mixing words, and descent into a union follows the active option.
An index computed from the type alone can name an absent position without asserting that a value is present, and every readable padding node remains covered by the general branch theorem.

### Binding

The results so far show that honest proofs verify.
The binding results show that a dishonest proof cannot verify unless SHA-256 has a collision.

Two accepted branches at the same index and root open the same leaf, or `findBranchCollision` returns a collision ([authentication](../Proofs/Ssz/Merkle/Authentication.lean)).
That collision is two 64-byte messages with one SHA-256 hash, each one hashed along its own branch.
By [multiproof binding](../Proofs/Ssz/Merkle/MultiproofBinding.lean), two accepted requests for one root agree on every position they both claim, or a search returns a collision.
The search tries every 64-byte input one verifier hashes against every input the other hashes.

[Whole-value binding](../Proofs/Ssz/Codec/Binding.lean) lifts this to values.
Admissible values of the same well-formed type with equal roots are equal, or the same search returns a collision.
There it compares the hash inputs of the two root computations.
It requires [CommitmentSized](../Proofs/Ssz/Codec/BindingDomain.lean), that every nested variable collection count fit its 256-bit mixing word.
The proof recovers lengths, selectors, packed data, and nested values, and callers supply no assumption about tree alignment.

Layouts are bound too.
By [layout separation](../Proofs/Ssz/Codec/LayoutSeparation.lean), two legal progressive containers with one root have one layout, or a search returns a SHA-256 collision.
The search compares the 64-byte inputs of the last hash of the two roots, each a contents node followed by a layout word.
By [layout words](../Proofs/Ssz/Codec/LengthBinding.lean), legal layouts of any lengths with equal mixed-in words are equal, so an absent field never shares a root with a zero value.

### Summaries

A *summary* replaces a nested value by its root.
By [summaries](../Proofs/Ssz/Codec/Summary.lean), replacing a value nested in a struct, a progressive struct, or a union by any value with the same root leaves the outer root unchanged.
A vector, list, or progressive list of composite elements has the same root as the same collection holding each element's root as a 32-byte array.
Replacing a struct field by a 32-byte array holding its root is the special case, and deeper summaries follow by repeating the replacement.
So a party holding only the summary computes the same root as a party holding the value, and a proof about anything inside the replaced value verifies against both.

### Typed values

A protocol states its objects as Lean structures, not as declarations and values.
A *typed value* bridges the two.
Its Lean type names a declaration, and each value converts to an untyped value and back.
A length or a limit is part of the Lean type, so every typed value fits its declaration.
Serialization, deserialization and the root then run the codec above, with no second codec.
A container takes its root over its summary: the container of its field roots, each held as one 32-byte node.
So a field type may keep the tree of its values and give its root without hashing them again.

The basic types, byte vectors, byte lists, bitfields, vectors, lists, progressive lists and progressive bitlists have typed values.
A container gets them from the types of its fields.
A progressive container does too, and also places its fields on a layout of active positions and gaps.
A typed value is *lawful* when its declaration is well formed, every value fits it, and the two conversions undo each other.
Its root method must also give the root of its untyped value.
Collections and containers are lawful when their parts are, and fixed counts are positive.
A progressive container also needs a layout that ends on a set bit and sets one bit per field.
The layout has at most 256 bits.

By [typed round trips](../Proofs/Ssz/Typed/Class.lean), a lawful value deserializes from its bytes.
Conversely, bytes that deserialize are the bytes of the value they give.
By [typed roots](../Proofs/Ssz/Typed/Root.lean), every lawful value has a root.
Two values with one root are equal, or their root computations expose a SHA-256 collision.
The typed binding theorem is the whole-value binding above, under the same length condition.

### The JSON mapping

By [the JSON mapping](../Proofs/Ssz/Codec/JsonRoundTrip.lean), a document written for an admissible value of any well-formed type reads back as that value, at every shape of the universe.
[Basic shapes](../Proofs/Ssz/Codec/JsonLaws.lean) cover booleans, all six integer widths, the byte alias, both byte arrays, and all three bitfields.
A bitfield is the hex of its own encoding, so its case is the codec round trip.
By [hex](../Proofs/Ssz/Codec/JsonHex.lean), a hex string the mapping wrote reads back as the bytes it came from.

For objects, a name written into one is read back from it, and every name an object carries is one it was written from.
So a written struct never trips the refusal of undeclared fields.
The mapping is deliberately not canonical, and a checked counterexample gives two documents for one value.
By [missing fields](../Proofs/Ssz/Codec/JsonLaws.lean), a container or progressive container document that leaves out a declared field is refused.

### Domains and limits

Composite serialization and deserialization both require fewer than `2^32` bytes at each composite level.
Byte arrays are sequences of bytes, so they meet the same limit, though they write no offset table.
Roots meet no such limit.
A union adds its selector byte to the encoding of the chosen option.
These distinctions are part of the mathematical size relation, rather than implicit assumptions about machine sizes.

Commitment binding has a separate length domain: variable collection counts must be below `2^256` at every nesting level.
`Fits` expresses value shape and declared capacities, while `CommitmentSized` expresses that each length word can be represented exactly.
Outside that domain, the low-level `lengthWord` keeps the low 256 bits, so the totality of roots does not imply binding without restriction.
SSZ does not separate roots by type, and the whole-value theorem compares values under one declaration.
Its finite hash computation expands cached zero subtrees, preserving their mathematical hashes.

## Trust boundary

The proofs establish the stated properties of the formal definitions.
Agreement between those definitions and the English SSZ specification remains a review obligation.
No theorem assumes that SHA-256 is injective or collision-free.

Kernel checking trusts Lean's kernel and standard logical foundations.
`lake exe check-decls` checks the axioms of every declaration, and that no definition runs compiled code other than itself.
The package is a foundation for a later implementation-refinement proof, and such a proof must still relate that implementation's byte operations, errors, and resource limits to this model.

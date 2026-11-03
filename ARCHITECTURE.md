# Architecture

EthLib is written by many people at once.
Each contributor takes one part of the protocol, reads its specification and writes it in Lean.
For that work to compose, every contributor follows one plan, and this document is that plan.

It says what EthLib holds, which layer each module belongs to, what a module may import, and which types modules exchange.
With these fixed, two people can write two modules at the same time and expect them to fit, a reviewer can tell whether a new module does, and a reader can tell where a definition lives before opening a file.

## Scope

EthLib aims to specify the whole Ethereum protocol in Lean, and to prove what the protocol guarantees.
In its end state, from the bytes a node receives, EthLib defines every value a correct node computes, and its theorems say why the result is secure.

A definition is in scope when a published source specifies it: an EIP, an RFC, a paper, a specification repository, or another primary source.
EthLib is a specification in its own right, at the same level as the others.
It follows what they define, and none of them shapes how EthLib is organised.

The rest of this section lists what that goal covers, part by part.
Each part names the EIPs that define it where they exist, and a later fork adds to its part rather than starting a new one.

### Cryptography

- Hash functions: Keccak-256, SHA-256, RIPEMD-160, and the BLAKE2b compression function of EIP-152.
- secp256k1: ECDSA signatures, public key recovery, and the address of a public key.
- secp256r1: signature verification for the P256VERIFY precompile of EIP-7951.
- alt_bn128: the curve operations and the pairing of EIP-196 and EIP-197.
- BLS12-381: the fields, the curves, the pairing, hashing to the curve of RFC 9380, and BLS signatures with their aggregation.
- KZG: commitments and proofs to blobs of EIP-4844, and to cells of EIP-7594.
- Merkle trees: the binary trees of SSZ and of hash-based signatures, with their proofs.
- Post-quantum signatures: hash-based schemes such as XMSS and SPHINCS, proposed to replace BLS signatures.

### Serialization

- RLP: the encoding of execution-layer objects, and its canonical form.
- SSZ: basic and composite types, the progressive lists and containers of EIP-7916 and EIP-7495, merkleization, and Merkle proofs by generalized index.

### Networking

- Discovery: Ethereum Node Records of EIP-778, and the discovery protocols that exchange them.
- Execution-layer peers: the encrypted transport, and the wire protocol that carries blocks, transactions and receipts.
- Consensus-layer peers: gossip topics and their message IDs, request and response protocols, and the Snappy compression and length prefixes they use.
- Data availability: the sidecars that carry blobs, and the sampling of data columns of EIP-7594.

### Execution layer

- Transactions: the typed envelope of EIP-2718, and the legacy, access-list (EIP-2930), fee-market (EIP-1559), blob (EIP-4844) and set-code (EIP-7702) types, with their signatures and validity rules.
- Fees: the base fee of EIP-1559, the blob base fee of EIP-4844 with its later bounds, and the gas limit of a block.
- The EVM: the stack, memory and storage, every instruction, the gas schedule, calls and contract creation.
- Precompiles, which only the EVM calls: ECRECOVER, SHA-256, RIPEMD-160, IDENTITY, MODEXP, the alt_bn128 operations, BLAKE2F, point evaluation, the BLS12-381 operations of EIP-2537, and P256VERIFY.
- System contracts and requests: the beacon block root of EIP-4788, historical block hashes of EIP-2935, and the deposit, withdrawal and consolidation requests of EIP-6110, EIP-7002, EIP-7251 and EIP-7685.
- State: accounts, storage and code, committed by the Merkle Patricia Trie, and the trees proposed to replace it, such as the binary tree of EIP-7864.
- Blocks: the header, receipts and their logs bloom, withdrawals of EIP-4895, the block-level access lists of EIP-7928, and the state transition of a block from Frontier to the latest fork.

### Consensus layer

- The beacon chain state transition: slot processing, epoch processing, and block processing with each operation it applies.
- Epoch processing: justification and finalization, rewards and penalties, the validator registry, slashings, and effective balances.
- Validators: deposits, exits, withdrawals, consolidations, shuffling into committees, and the selection of proposers and sync committees.
- Fork choice: LMD-GHOST with Casper FFG, proposer boost, optimistic sync, and fast confirmation.
- The interface to the execution layer: what the consensus layer asks of an execution engine, and what it learns back.
- Honest validator duties: proposing, attesting, aggregating and serving on a sync committee.
- Light clients: the sync protocol that follows the chain from sync committee signatures.
- Weak subjectivity: how long a checkpoint stays safe to start from.
- Proposer-builder separation of EIP-7732, and fork-choice enforced inclusion lists of EIP-7805.
- The protocols proposed to replace the current ones: faster finality, available chains with a finality gadget, and a consensus layer built on post-quantum signatures.

### Models

- Signatures and commitments: unforgeability of each signature scheme, and binding of each commitment, in the random oracle model where the scheme needs it.
- Consensus: accountable safety and plausible liveness of Casper FFG, and the safety and liveness of each fork-choice rule and finality protocol, under its stated network and corruption model.
- Refinement: for each model, a theorem that the specification is an instance of it.

A client is out of scope.
Peer management, storage, sync strategies, the mempool and the RPC are choices each client makes, and no specification fixes them.
A client can build on EthLib, and the bindings exist so that clients can run its definitions.

An optimised implementation is in scope only as a refinement: a second definition, with a theorem that it computes the same function as the specification.

## Three kinds of content

EthLib holds three kinds of Lean code, and they answer different questions.

A **specification** says what the protocol computes.
It is executable, pure and total, and it follows its source definition by definition.
Clients and other Lean projects import it, and the bindings run it.

A **property** says what a specification guarantees.
Round trips of encodings, bounds on a fee, the rejection of malformed input and known answers are all properties.
They are stated about the specification itself, so they hold for exactly the code that runs.

A **model** says why the protocol is secure.
It is abstract where the specification is concrete: a hash becomes a random oracle, a network becomes an adversary that schedules messages.
The unforgeability of a signature scheme is proved about a model, and so are the safety and liveness of a consensus protocol.
A model connects to the specification by a refinement theorem, which says that the concrete definition is an instance of the abstract one.
Without that theorem, the security proof is about a different object than the one clients run.

Each kind depends only on the kinds before it.
A specification never imports a property or a model, and a property never imports a model.

## Layers

The specifications form layers.
Each layer is a directory under `EthLib/`, which `CONTRIBUTING.md` calls a domain, and a module imports only from its own layer or from the layers below it.

| Layer | Holds | Directory |
| --- | --- | --- |
| Consensus | the state transition and the fork choice of the consensus layer | `EthLib/Consensus/` |
| Execution | the EVM with its precompiles, the fees, and the state transition of the execution layer | `EthLib/Execution/` |
| Networking | the messages peers exchange, with their framing and compression | `EthLib/Networking/` |
| Serialization | the encodings the protocol sends and hashes | `EthLib/Serialization/` |
| Cryptography | hashes and Merkle trees, then the schemes built on them | `EthLib/Cryptography/` |
| Base | the bytes and integers every layer uses | `EthLib/Base/` |

Models sit above all of them, in their own package, described under [Packages](#packages).

The order follows what each layer needs.
SSZ merkleization hashes with SHA-256, so Serialization sits above Cryptography.
A gossip message ID hashes SSZ-encoded data, so Networking sits above Serialization.
The protocol layers use all of them.

Cryptography is split in two inside its directory.
Hashes and Merkle trees come first, and SSZ uses them.
Curves, signatures and commitments come second, and use hashes and one another, as KZG uses BLS12-381.
No cryptographic module imports Serialization.
When a scheme needs a wire encoding, such as the SSZ encoding of a signature, the encoding lives with the protocol that sends it.

Execution and Consensus sit side by side and never import each other.
The consensus layer needs one fact from the execution layer: whether an execution payload is valid.
So the execution engine that answers it is a parameter of the consensus state transition, not an import.
The consensus state transition can then be proved about with any engine, and instantiated with the Execution layer's.

The Networking layer holds formats that need no chain state.
A gossip validation rule that reads the beacon state, such as the checks on a `beacon_block` message, belongs to Consensus, which imports Networking.

## Rules

These rules follow from the layers.
A pull request that breaks one says why in its description.

- A module imports only from its own layer or from a lower one.
- Execution and Consensus never import each other.
- A cryptographic module never imports Serialization.
- A specification never imports a property, a C export or a model.
- A specification imports nothing outside the Lean toolchain, which ships `Init`, `Std` and `Lean`.
  Mathlib and the probability libraries enter only in properties and models.
- A construction shared by two modules is written once, in the lowest layer both can import.
  A binary Merkle tree used by SSZ and by a hash-based signature is one example.

## Shared types

Modules meet at their types.
When two modules represent the same value differently, every caller converts between them, and every conversion is a place to get a length or a range wrong.
So the types that cross a module boundary are fixed here, and `EthLib/Base/` defines the ones that no single layer owns.

- Bytes of any length are a `ByteArray`.
- Bytes of a fixed length `n` are a `Vector UInt8 n`.
  The length is then part of the type, as `CONTRIBUTING.md` asks, and a 48-byte commitment cannot be passed where a 96-byte signature is expected.
- A fixed-size type keeps the name its source gives it, defined once by the layer that owns the concept.
  `Hash32`, `Bytes32` and `Address` belong to Base, `BLSPubkey` to Cryptography, `Root` and `Slot` to Consensus.
- An integer keeps the range its source gives it.
  An unbounded integer is a `Nat`, and a 64-bit one is a `UInt64`.
  Where the source makes overflow invalid, an operation that would overflow is an error, never a silent wrap.
  The 256-bit words of the EVM are one `U256` type, with arithmetic modulo 2^256, defined in Base.
- A function that can fail returns `Except E α`, with one error type per module whose constructors name each reason.
  No specification runs in `IO` or panics.
- A construction that is generic in its hash, such as a Merkle tree or a hash-based signature, takes the hash as an argument.
  The specification passes the concrete hash.
  A model passes a random oracle, and its theorems then hold for the same definition.

## Forks

Ethereum changes its rules at forks.
A specification can restate every rule at each fork, or write each fork as its differences from the one before.
EthLib does neither: a rule is written once, and again only when a fork changes it.

- A rule that no fork has changed carries no fork in its name.
  Its doc comment names the fork that introduced it and the latest fork checked, at a pinned commit.
- A rule that a fork changed keeps both versions, in namespaces named after the forks that introduced them.
  The gossip message ID is one: Phase 0 and Altair compute it differently, and messages on a Phase 0 topic still use the Phase 0 rule.
- A constant whose value differs between presets, such as `SLOTS_PER_EPOCH` on mainnet and on the minimal preset, is a field of a preset structure that the specification takes as an argument.
  A constant with one value is a definition named as in its source.

Each fork has one module that assembles the rules active in it, such as the set of precompiles at that fork.
That module is the place to read a fork as a whole.

## Sources

Every definition cites its source with a link pinned to a commit.
Two modules that pin two commits of one repository can disagree without anyone noticing.
So each source repository has one pinned commit, recorded in one file, and every module that cites the repository uses it.
Update the pin in one pull request. Check every module that cites the repository.

## Packages

What a consumer imports decides what it must download and trust.
A client needs the specifications and nothing else, while a security proof needs the specifications, Mathlib and a probability library.
So EthLib splits into packages by what each part requires:

- a core package with the specifications, the properties that need nothing beyond the Lean toolchain, and the C exports;
- a package for the properties that need Mathlib;
- a package for the models, which need a library of probabilistic computations such as VCVio.

Each package depends on the ones before it, never the reverse.
A consumer then takes exactly what it needs, and the core moves to a new Lean version without waiting for Mathlib.

## Where a new module goes

A new module finds its place by answering three questions in order.

1. Which kind is it?
   Code that computes the protocol is a specification, a theorem about it is a property, and an abstract protocol is a model.
2. Which layer is it in?
   Take the highest layer whose concepts it needs, and check that it needs nothing above it.
   An Ethereum Node Record is signed with secp256k1 and encoded with RLP, so it sits in Networking, above both.
3. Does a shared construction already exist?
   Look in the layers below before writing a tree, an encoding or a field.
   If two modules need the same thing, write it once, in the lower of their layers.

Then the module follows the layout of `CONTRIBUTING.md`: the specification in `EthLib/<Domain>/<Module>/`, its theorems in `EthLib/<Domain>/Proofs/<Module>/`, and its C exports in `EthLib/<Domain>/Exports/`.
Modules of one kind share a directory, under the part of the layer that uses them.
The precompiles are one kind, and only the EVM calls them, so ECRECOVER sits in `EthLib/Execution/Evm/Precompiles/Ecrecover/`, and its theorems in `EthLib/Execution/Proofs/Evm/Precompiles/Ecrecover/`.

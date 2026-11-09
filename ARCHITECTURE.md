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

- Hash functions: Keccak-256, Keccak-512, SHA-256, RIPEMD-160, and the BLAKE2b compression function of EIP-152.
- Checksums: CRC-32 for the fork identifier of EIP-2124, and CRC-32C for the Snappy framing format.
- Symmetric encryption: AES with the CTR and GCM modes, which the RLPx transport and discv5 use.
- Key derivation over SHA-256: HMAC, HKDF, the Concatenation KDF, PBKDF2, and scrypt.
- secp256k1: ECDSA signatures with RFC 6979 nonces, public key recovery, the address of a public key, and ECDH.
- secp256r1: signature verification for the P256VERIFY precompile of EIP-7951.
- alt_bn128: the curve operations and the pairing of EIP-196 and EIP-197.
- BLS12-381: the fields, the curves, the pairing, hashing to the curve of RFC 9380, BLS signatures with their aggregation, and validator key derivation.
- KZG: commitments and proofs to blobs of EIP-4844, and to cells of EIP-7594.
- Merkle trees: the binary trees of SSZ and of hash-based signatures, with their proofs.
- Ethash: the proof of work of the execution layer before Paris.
- Post-quantum signatures: hash-based schemes such as XMSS and SPHINCS, proposed to replace BLS signatures.
- Verifiable random functions: a hash-based VRF built on a Merkle tree.

### Serialization

- RLP: the encoding of execution-layer objects, and its canonical form.
- SSZ: basic and composite types, the progressive lists and containers of EIP-7916 and EIP-7495, merkleization, and Merkle proofs by generalized index.

### Networking

- Discovery: Ethereum Node Records of EIP-778, and the discovery protocols that exchange them.
- Execution-layer peers: the encrypted RLPx transport, and the "p2p" capability that opens a session.
- Consensus-layer peers: gossip topics and their message IDs, request and response protocols, and the Snappy compression and length prefixes they use.

### Execution layer

- Transactions: the typed envelope of EIP-2718, and the legacy, access-list (EIP-2930), fee-market (EIP-1559), blob (EIP-4844) and set-code (EIP-7702) types, with their signatures and validity rules.
- Fees: the base fee of EIP-1559, the blob base fee of EIP-4844 with its later bounds, and the gas limit of a block.
- The EVM: the stack, memory and storage, every instruction, the gas schedule, calls and contract creation.
- Precompiles, which only the EVM calls: ECRECOVER, SHA-256, RIPEMD-160, IDENTITY, MODEXP, the alt_bn128 operations, BLAKE2F, point evaluation, the BLS12-381 operations of EIP-2537, and P256VERIFY.
- System contracts and requests: the beacon block root of EIP-4788, historical block hashes of EIP-2935, and the deposit, withdrawal and consolidation requests of EIP-6110, EIP-7002, EIP-7251 and EIP-7685.
- State: accounts, storage and code, committed by the Merkle Patricia Trie, and the trees proposed to replace it, such as the binary tree of EIP-7864.
- Blocks: the header, receipts and their logs bloom, withdrawals of EIP-4895, the block-level access lists of EIP-7928, and the state transition of a block from Frontier to the latest fork.
- The eth wire protocol of devp2p, which carries blocks, transactions and receipts between peers.

### Consensus layer

- The beacon chain state transition: slot processing, epoch processing, and block processing with each operation it applies.
- Epoch processing: justification and finalization, rewards and penalties, the validator registry, slashings, and effective balances.
- Validators: deposits, exits, withdrawals, consolidations, shuffling into committees, and the selection of proposers and sync committees.
- Fork choice: LMD-GHOST with Casper FFG, proposer boost, optimistic sync, and fast confirmation.
- The interface to the execution layer: what the consensus layer asks of an execution engine, and what it learns back.
- Honest validator duties: proposing, attesting, aggregating and serving on a sync committee.
- Light clients: the sync protocol that follows the chain from sync committee signatures.
- Weak subjectivity: how long a checkpoint stays safe to start from.
- Data availability: the sidecars that carry blobs, and the custody and sampling of data columns of EIP-7594.
- Proposer-builder separation of EIP-7732, and fork-choice enforced inclusion lists of EIP-7805.
- The protocols proposed to replace the current ones: faster finality, available chains with a finality gadget, and a consensus layer built on post-quantum signatures.

### Models

- Signatures and commitments: unforgeability of each signature scheme, and binding of each commitment, in the random oracle model where the scheme needs it.
- Consensus: accountable safety and plausible liveness of Casper FFG, and the safety and liveness of each fork-choice rule and finality protocol, under its stated network and corruption model.
- Refinement: for each model, a theorem that the specification is an instance of it.

A client is out of scope.
Peer management, storage, sync strategies, the mempool and the RPC are choices each client makes, and no specification fixes them.
A client can build on EthLib, and the bindings exist so that clients can run its definitions.

There is one definition of each function, and clients run that definition.
When a definition is too slow, a change makes that definition fast and keeps its theorems.

## Three kinds of content

EthLib holds three kinds of Lean code, and they answer different questions.

A **specification** says what the protocol computes.
It is executable, pure and total, and it follows its source definition by definition.
Clients and other Lean projects import it, and the bindings run it.

A **property** says what a specification guarantees.
Round trips of encodings, bounds on a fee and the rejection of malformed input are all properties.
They are stated about the specification itself, so they hold for exactly the code that runs.
A known answer fixes one input and its output, so it is a test and not a property.
Known answers live in the Python test suite, which runs the specification through the bindings.

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
| Engine | what needs the types of both protocol layers, such as the execution block of an execution payload | `EthLib/Engine/` |
| Consensus | the state transition and the fork choice of the consensus layer | `EthLib/Consensus/` |
| Execution | the EVM with its precompiles, the fees, and the state transition of the execution layer | `EthLib/Execution/` |
| Networking | the messages peers exchange, with their framing and compression | `EthLib/Networking/` |
| Serialization | the encodings the protocol sends and hashes | `EthLib/Serialization/` |
| Cryptography | hashes and Merkle trees, then the schemes built on them | `EthLib/Cryptography/` |
| Base | the bytes, the integers and the forks that every layer uses | `EthLib/Base/` |

Models sit above all of them, under `Proofs/` in the layer they are about, as [Packages](#packages) describes.

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

Some definitions need the types of both layers.
The execution payload of a beacon block stands for an execution block, and the conversion between them reads both.
Such a definition lives in the Engine layer, the only layer that imports both Execution and Consensus.

The Networking layer holds formats that need no chain state.
A gossip validation rule that reads the beacon state, such as the checks on a `beacon_block` message, belongs to Consensus, which imports Networking.
In the same way, the eth wire protocol of devp2p carries blocks, transactions and receipts.
So its messages live in `EthLib/Execution/Network/`, which has those types and imports Networking.

## Rules

These rules follow from the layers.
A pull request that breaks one says why in its description.
`scripts/check_layers.py` checks every rule that the import lines decide.

- A module imports only from its own layer or from a lower one.
- Execution and Consensus never import each other; only Engine imports both.
- No module with an `Xmss` component reaches one with a `Sphincs` component through its imports, nor the reverse.
  What both hash-based signatures use lives in a neutral module, such as `HashSig` or `Wots`.
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
- A fork is a `Fork`, one type for both layers, defined in Base, as [Forks](#forks) describes.
- A function that can fail returns `Except E α`, with one error type per module whose constructors name each reason.
  No specification runs in `IO` or panics.
- A construction that is generic in its hash, such as a Merkle tree or a hash-based signature, takes the hash as an argument.
  The specification passes the concrete hash.
  A model passes a random oracle, and its theorems then hold for the same definition.

## Forks

Ethereum changes its rules at forks, and EthLib specifies every fork of both layers, from Frontier and Phase 0 to the latest.
It does not restate the specification at each fork.
Each rule is written once, takes the fork as an argument, and branches only at the forks that changed it.

### One timeline

The type `Fork`, in `EthLib/Base/Fork.lean`, lists the forks of both layers in the order in which they activate on mainnet.
Before the Merge, the execution chain and the beacon chain forked apart, so their forks interleave: Muir Glacier, Phase 0, Berlin, London, Altair, Arrow Glacier.
From Shapella on, one upgrade changes both layers at once.
So one fork such as Pectra stands for Prague on the execution layer and Electra on the consensus layer.
Both layers read the same fork, so they cannot disagree on which fork is active.

The type holds only the order.
When a fork activates, by block number, timestamp or epoch, on mainnet or on a testnet, is chain configuration.
`EthLib/Base/ChainConfig.lean` gives the activations on an execution chain, in the order of the timeline.
A fork activates there by block number up to Paris, and by timestamp from Shapella on.
On the consensus layer, a fork activates at an epoch, and `EthLib/Consensus/ForkSchedule.lean` gives the fork of each epoch.
At each point of a chain, the active fork is the latest fork whose activation is at or before that point.
Two forks can activate at one block.
Constantinople and Petersburg did so on mainnet, and Petersburg is then the active fork, as EIP-1716 requires.

Some forks change little, and each of them is still a fork of the type, so the timeline matches the meta EIPs.
The DAO Fork changes no rule: at its first block, it moves the ether of a list of accounts to one contract.
Muir Glacier, Arrow Glacier and Gray Glacier only delay the difficulty bomb.
Bellatrix and Paris, the two halves of the Merge, are two forks, because Bellatrix activated on 6 September 2022 and Paris on 15 September.
A rule that none of these forks changed never mentions them.

A drafted change is not yet a point on the timeline.
The consensus specifications keep such drafts as features, most of them built on a named fork with a placeholder fork version.
For example, the draft of EIP-8321 starts from a Heze state, but "Heze with EIP-8321" is neither Heze nor the fork after it.
So one rule, for both layers, says when a change becomes work in EthLib: when a fork of the specifications includes it, and not before.
On the consensus layer, that is when its document leaves the feature drafts (`specs/_features` in consensus-specs) for a fork directory such as `specs/heze`.
On the execution layer, the default branch of execution-specs holds the next fork, and an EIP enters when it merges there.
The first merge creates the fork's tests directory, such as `tests/bogota`, and a `tests@` release that holds this directory marks the same event.
`scripts/check_spec_releases.py` reports both signals for the first EIP of a fork, and a reviewer checks the later merges.
Until then, a draft gets no fork branch in any rule.

The rule governs changes, not forks.
A fork such as Hegotá keeps its constructor of `Fork` once some of its changes have entered.
The rules that wait for its other changes reject it as not yet specified.
The parity catalogue lists the Bogota cases of each pinned devnet, but none of them runs.
Each waits, with its plan, for a merge into the Bogota fork branch or a release of Bogota.

A component that no fork uses yet, such as a new state tree, can still be specified on its own, outside `Fork`.
Its EIP must first be stable enough to cite.
For example, the binary tree of EIP-7864 could be specified with its root and its proofs, but no block rule would use it.
It joins the timeline by the same rule, when a fork includes it.
The Scope section lists what EthLib covers in the end, not the order of the work.

### A rule takes the fork

A rule that no fork changes, such as SHA-256 or the RLP encoding, takes no fork.
A rule that forks change takes the fork as an argument, and compares it with those forks, the latest first.
The order on `Fork` is decidable, so `fork ≥ .berlin` is a test in a rule and a hypothesis in a theorem.

The gas cost of SLOAD is one example.
It is 50 at Frontier, 200 from Tangerine Whistle (EIP-150) and 800 from Istanbul (EIP-1884).
From Berlin, EIP-2929 charges 2100 for a slot that the transaction has not accessed before, and 100 for a slot that it has:

```lean
def sloadCost (fork : Fork) (cold : Bool) : Nat :=
  if fork ≥ .berlin then (if cold then 2100 else 100)
  else if fork ≥ .istanbul then 800
  else if fork ≥ .tangerineWhistle then 200
  else 50
```

A theorem can then quantify over forks.
"At every fork from Berlin on, a warm SLOAD costs 100" reads `∀ fork, fork ≥ .berlin → sloadCost fork false = 100`.

A rule of one layer does not branch at a fork that changes only the other layer.
At Altair, an execution rule behaves as at London.
The beacon chain starts at Phase 0, so a theorem about the consensus layer assumes `fork ≥ .phase0` where it needs to.

### Constants that change at forks

A constant whose value changes at forks is a field of one structure, the parameters of the forks of its layer.
One function of the fork computes that structure, and branches at the forks that change a field, as a rule does.
Each value is then written once, at the fork that set it.

The blob schedule is one example.
The target and the maximum are 3 and 6 blobs per block from Dencun (EIP-4844), and 6 and 9 from Pectra (EIP-7691).
They are 10 and 15 from BPO1 (EIP-8134), and 14 and 21 from BPO2 (EIP-8135).
EIP-7892 makes this schedule chain configuration, so a testnet can set other values.
A rule therefore takes the blob schedule as an argument, and the function of the fork gives the mainnet values.

A constant with one value at every fork is a definition, named as in its source.

### Fields that appear at a fork

A type whose fields appear at forks, such as the execution block header, is one type indexed by the fork.
A field that appears at fork `f` has the type `Since f fork α`, a function from a proof of `f ≤ fork` to `α`.
Before `f`, no such proof exists, so the field has exactly one value and holds nothing.
From `f` on, the field holds one value of `α`.
Mathlib's `Part` uses the same idea for any proposition.

The withdrawals root of the header shows how this works.
EIP-4895 adds it at Shanghai, so in `Header fork` it has the type `Since .shapella fork Hash32`.
At London, the field holds nothing, and the RLP encoding of the header is a list of 16 items, with the base fee last.
At Shapella, the field holds the root of the withdrawals trie, and the list has 17 items, with that root last, as EIP-4895 shows.
A function that builds a header at any fork writes the root as `fun _ => root`, and a reader passes a proof of `fork ≥ .shapella`.

A field that a fork removes has the type `Until f fork α`, a function from a proof of `fork < f` to `α`.
It holds one value before `f`, and nothing from `f` on.
The attestations of a Phase 0 beacon state are one example, since Altair replaces them by participation flags.

The codecs then see only the present fields.
The RLP list of a header has only the fields whose fork is at or before `fork`, in their order.
The SSZ container of a beacon state works the same way.

The execution block header, in `EthLib/Execution/Blocks/Header.lean`, uses this design.
Its RLP codec is lawful at every fork, which validates the design for RLP.
The execution payload of the consensus layer, in `EthLib/Consensus/Containers/Execution.lean`, uses it with SSZ.
Its SSZ codec is lawful at every fork, which validates the design for SSZ.

The simpler form `if f ≤ fork then α else Unit` reduces to `α` or to `Unit` at a known fork.
At a fork variable, it needs a cast at each read and each write, and the function form needs none.

### The existing modules

The gossip message ID is one function of the fork, which branches at Altair.
The excess blob gas is one function of the fork too, which branches at Fusaka.
For the message ID, the argument is the fork of the topic, not the fork of the chain head.
A message on a topic with the Phase 0 fork digest keeps the Phase 0 rule.

A preset, such as the mainnet or the minimal preset of the consensus layer, is independent of the fork.
A constant that differs between presets, such as `SLOTS_PER_EPOCH` (32 on mainnet, 8 on minimal), stays a field of a preset structure that the rule takes as an argument.
When a constant depends on both, the function of the fork takes the preset as an argument too.
`EthLib/Consensus/Preset.lean` defines the preset structure, with the mainnet and minimal presets.

## Sources

EthLib is a specification at the same level as execution-specs and consensus-specs, so its code stands on its own.
The code cites only primary sources: an EIP or an RFC with its section, a NIST or SEC standard, or a paper.
Where no primary source states a rule, the doc comment states the rule itself, in words and in mathematics.
A reader then needs no other specification.
A contributor may read execution-specs and consensus-specs to understand a rule and to check the work, but the code does not cite them.

Test vectors are the exception, because a test must say what it checks against.
Each fixture keeps its pinned origin and digests in `tests/`.
Two tests that pin two commits of one repository can disagree without anyone noticing.
So each repository that fixtures come from has one pinned commit, recorded in `tests/sources.toml`, and every test that reads from the repository uses it.
Update the pin in one pull request, and check every test that reads from the repository.

## Packages

EthLib is one Lake package, and three libraries hold its code.

- The library `EthLib` holds the specifications.
- The library `Proofs` holds the properties and the models, in the `Proofs/` directory of each layer.
- The library `Exports` holds the C exports that the Python bindings call.

The package also builds two executables: `check-decls`, which checks the compiled declarations, and `gen-bindings`, which writes the binding contract from Lean.
A fourth library, `CheckDeclsTest`, holds the test cases of that executable, in `scripts/`.
It is not a default target, and `scripts/test_check_decls.sh` builds it.

The package requires Mathlib and VCVio, a library of probabilistic computations.
Only the properties and the models may import them, or Batteries.
A specification or an export imports nothing beyond the Lean toolchain.
So the code that clients and the bindings run depends on no other library.
Lake still downloads Mathlib and VCVio for a project that requires EthLib, because a requirement holds for the whole package.

A model is a module under `Proofs/`, like a property.
The rule that no property imports a model is a rule between modules, not between packages.

## Where a new module goes

A new module finds its place by answering three questions in order.

1. Which kind is it?
   Code that computes the protocol is a specification, a theorem about it is a property, and an abstract protocol is a model.
   A specification goes in the library `EthLib`, and a property or a model in the library `Proofs`.
2. Which layer is it in?
   Take the highest layer whose concepts it needs, and check that it needs nothing above it.
   An Ethereum Node Record is signed with secp256k1 and encoded with RLP, so it sits in Networking, above both.
3. Does a shared construction already exist?
   Look in the layers below before writing a tree, an encoding or a field.
   If two modules need the same thing, write it once, in the lower of their layers.

Then the module follows the layout of `CONTRIBUTING.md`: the specification in `EthLib/<Domain>/<Module>/`, its theorems in `EthLib/<Domain>/Proofs/<Module>/`, and its C exports in `EthLib/<Domain>/Exports/`.
A model goes under `Proofs/` too, as the models of Casper FFG and LMD-GHOST do in `EthLib/Consensus/Proofs/Models/`.
Modules of one kind share a directory, under the part of the layer that uses them.
The precompiles are one kind, and only the EVM calls them, so ECRECOVER sits in `EthLib/Execution/Evm/Precompiles/Ecrecover.lean`, and its theorems in `EthLib/Execution/Proofs/Evm/Precompiles/Ecrecover.lean`.

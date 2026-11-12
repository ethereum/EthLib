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

- e2store: the typed records of history files. The era1 and era files built on them belong to the execution and consensus layers.
- RLP: the encoding of execution-layer objects, and its canonical form.
- SSZ: basic and composite types, the progressive lists and containers of EIP-7916 and EIP-7495, merkleization, and Merkle proofs by generalized index.

### Networking

- Discovery: Ethereum Node Records of EIP-778, and the discovery protocols that exchange them.
- Execution-layer peers: the encrypted RLPx transport, the "p2p" capability that opens a session, the states that a session passes through, and the snap capability.
  A node uses snap to download the state of a recent block.
- Consensus-layer peers: gossip topics and their message IDs, request and response protocols, and the Snappy compression and length prefixes they use.
- Consensus-layer connections: the libp2p transports, the Noise handshake, the negotiation of protocols and the multiplexing of streams.
- Gossip: the gossipsub router that relays messages between consensus-layer peers.

### Execution layer

- Transactions: the typed envelope of EIP-2718, and the legacy, access-list (EIP-2930), fee-market (EIP-1559), blob (EIP-4844) and set-code (EIP-7702) types, with their signatures and validity rules.
- Fees: the base fee of EIP-1559, the blob base fee of EIP-4844 with its later bounds, and the gas limit of a block.
- The EVM: the stack, memory and storage, every instruction, the gas schedule, calls and contract creation.
- Precompiles, which only the EVM calls: ECRECOVER, SHA-256, RIPEMD-160, IDENTITY, MODEXP, the alt_bn128 operations, BLAKE2F, point evaluation, the BLS12-381 operations of EIP-2537, and P256VERIFY.
- System contracts and requests: the beacon block root of EIP-4788, historical block hashes of EIP-2935, and the deposit, withdrawal and consolidation requests of EIP-6110, EIP-7002, EIP-7251 and EIP-7685.
- State: accounts, storage and code, committed by the Merkle Patricia Trie, and the trees proposed to replace it, such as the binary tree of EIP-7864.
- Blocks: the header, receipts and their logs bloom, withdrawals of EIP-4895, the block-level access lists of EIP-7928, and the state transition of a block from Frontier to the latest fork.
- The eth wire protocol of devp2p, which carries blocks, transactions and receipts between peers.
- History files: the era1 files of the blocks before the Merge, with their accumulator and block index.

### Consensus layer

- The beacon chain state transition: slot processing, epoch processing, and block processing with each operation it applies.
- Epoch processing: justification and finalization, rewards and penalties, the validator registry, slashings, and effective balances.
- Validators: deposits, exits, withdrawals, consolidations, shuffling into committees, and the selection of proposers and sync committees.
- Fork choice: LMD-GHOST with Casper FFG, proposer boost, optimistic sync, and fast confirmation.
- The interface to the execution layer: what the consensus layer asks of an execution engine, and what it learns back.
  Between two clients, the Engine API of [Interfaces](#interfaces) carries these calls.
- Honest validator duties: proposing, attesting, aggregating and serving on a sync committee.
- Light clients: the sync protocol that follows the chain from sync committee signatures.
- Weak subjectivity: how long a checkpoint stays safe to start from.
- Data availability: the sidecars that carry blobs, and the custody and sampling of data columns of EIP-7594.
- Proposer-builder separation of EIP-7732, and fork-choice enforced inclusion lists of EIP-7805.
- History files: the era files of the beacon blocks and states, one group per era, with their slot indices.
- The protocols proposed to replace the current ones: faster finality, available chains with a finality gadget, and a consensus layer built on post-quantum signatures.

### Interfaces

Independent teams write the parts of a node and the tools around it.
So the interfaces between those parts have published specifications, and EthLib is to specify each of them:

- Engine API: the calls between the consensus client and the execution client of a node, from `ethereum/execution-apis`.
- Execution JSON-RPC API: the methods of an execution client, from `ethereum/execution-apis`, such as the account proof that `eth_getProof` returns (EIP-1186).
- Beacon API: the methods of a consensus client, from `ethereum/beacon-APIs`.
- Builder API: the messages between a proposer and the builders that bid for its payload, from `ethereum/builder-specs`.
- Relay API: what a relay serves to the builders that submit blocks and to anyone who reads its data, from `flashbots/relay-specs`.
- Keymanager API: the calls that management tools make to a validator client, which holds the keys and the anti-slashing database, from `ethereum/keymanager-APIs`.
- Remote-signing API: the calls that a validator client makes to a remote signer, which holds the keys and signs for it, from `ethereum/remote-signing-api`.

The relay API and the two validator-client APIs come after the others in the order of work.
The relay API stays in scope because no rule excludes it.
Its containers build on the builder API and on the consensus containers.
So EthLib keeps those compatible with it: each relay container can be written with EthLib's types, and encodes as `flashbots/relay-specs` defines it.

The keymanager API and the remote-signing API need feedback from the implementers that use them: validator clients, key-management tools and remote signers.
That feedback settles what their sources leave open, and which parts come first.
Work on them can start before it, but their specification is accepted only with it.

### Models

- Signatures and commitments: unforgeability of each signature scheme, and binding of each commitment, in the random oracle model where the scheme needs it.
- Consensus: accountable safety and plausible liveness of Casper FFG, and the safety and liveness of each fork-choice rule and finality protocol, under its stated network and corruption model.
- Refinement: for each model, a theorem that the specification is an instance of it.

A client is out of scope.
Peer management, storage, sync strategies and the mempool are choices each client makes, and no specification fixes them.
What a client must share with other nodes, or with the other parts of a node, is in scope where a published specification fixes it.
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
Known answers stay out of the default build.
They run in the Python test suite, which runs the specification through the bindings, and in Lean only outside the default build, as `CONTRIBUTING.md` describes.

A **model** says why the protocol is secure.
It is abstract where the specification is concrete: a hash becomes a random oracle, a network becomes an adversary that schedules messages.
The unforgeability of a signature scheme is proved about a model, and so are the safety and liveness of a consensus protocol.
A model connects to the specification by a refinement theorem, which says that the concrete definition is an instance of the abstract one.
Without that theorem, the security proof is about a different object than the one clients run.

A refinement theorem is a property.
A **refinement module** is a property module that states a refinement theorem, or uses one in a proof.
A refinement that holds by definition is still stated as a theorem, so that a reader can find it.
Its proof unfolds the definitions, often with `rfl`.
`rootWith_hash` in `EthLib/Cryptography/Proofs/Vrf/Unpredictability.lean` is one.

A module is a model because of what it says, not because of what it imports.
A module that imports VCVio is a property when its theorems are about the specification.

Each kind imports directly only the kinds before it, and refinement modules are the one exception.
A specification never imports a property or a model.
A property never imports a model directly, unless it is a refinement module.
So a property module that imports a model directly, but neither states nor uses a refinement theorem, breaks the rule.
A property may import a refinement module, and so reach a model through it, without being a refinement module itself.
No file lists the refinement modules yet, and no check enforces the rule.

## Layers

The specifications form layers.
Each layer is a directory under `EthLib/`, which `CONTRIBUTING.md` calls a domain, and a module imports only from its own layer or from the layers below it.

| Layer | Holds | Directory |
| --- | --- | --- |
| Engine | what needs the types of both protocol layers, such as the execution block of an execution payload | `EthLib/Engine/` |
| Consensus | the state transition and the fork choice of the consensus layer | `EthLib/Consensus/` |
| Execution | the EVM with its precompiles, the fees, and the state transition of the execution layer | `EthLib/Execution/` |
| Networking | the messages peers exchange, with their framing and compression | `EthLib/Networking/` |
| Serialization | the encodings the protocol sends, hashes and stores | `EthLib/Serialization/` |
| Cryptography | hashes and Merkle trees, then the schemes built on them | `EthLib/Cryptography/` |
| Base | the bytes, the integers and the forks that every layer uses, and the protocol rules that Execution and Consensus share, such as the blob schedule and the gas limit step | `EthLib/Base/` |

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
So the execution engine that answers it is a parameter, never an import, of each consensus function that asks.
From Bellatrix until Glamsterdam, `processExecutionPayload` asks, and from Glamsterdam, `verifyExecutionPayloadEnvelope` does.
Each such function can then be proved about with any engine, and instantiated with the Engine layer's.

Some definitions need the types of both layers.
The execution payload of a beacon block stands for an execution block, and the conversion between them reads both.
Such a definition lives in the Engine layer, the only layer that imports both Execution and Consensus.

The engine shows the general rule for an operation that a module needs from a layer it cannot import.
The module declares the operations it needs, in its own types, and takes them as a resource, as [Shared types](#shared-types) describes.
By that rule, their production instance lives in the lowest layer that imports both sides, which is Engine for Execution and Consensus.
So `ExecutionEngine` in `EthLib/Consensus/Transition/Execution.lean` declares the checks of a payload, and `executionEngine` in `EthLib/Engine/ExecutionEngine.lean` builds them from the Execution layer.
A module imports an operation of a lower layer directly.
When a test must replace such an operation, the function takes it as a resource too, and the test passes a test stub.
`SignatureChecks` is one example: the stub `SignatureChecks.acceptAll` replaces the BLS checks for the consensus test vectors that carry placeholder signatures.

The Networking layer holds formats that need no chain state.
A gossip validation rule that reads the beacon state, such as the checks on a `beacon_block` message, belongs to Consensus, which imports Networking.
In the same way, the eth wire protocol of devp2p carries blocks, transactions and receipts.
So its messages live in `EthLib/Execution/Network/`, which has those types and imports Networking.

A protocol layer owns the tables that give bytes their meaning.
For example, Consensus gives the SSZ type of each gossip topic, of each request and of each response chunk, in `EthLib/Consensus/Gossip/Bounds.lean`, `EthLib/Consensus/ReqResp/Bounds.lean` and `EthLib/Consensus/ReqResp/ResponseBounds.lean`.
Networking owns the framing and its own payload cap.
It applies the smaller of that cap and the length bound that its caller passes, as `decodePayload` does in `EthLib/Networking/Gossip/Payload.lean` and in `EthLib/Networking/ReqResp/Encoding.lean`.

## Rules

These rules follow from the layers.
A pull request that breaks one says why in its description.
`scripts/check_layers.py` checks every rule that the import lines decide.

- A module imports only from its own layer or from a lower one.
- Execution and Consensus never import each other; only Engine imports both.
- No module with an `Xmss` component reaches one with a `Sphincs` component through its imports, nor the reverse.
  What both hash-based signatures use lives in a neutral module, such as `HashSig` or `Wots`.
- A specification under `Cryptography/Hash/` or `Cryptography/Merkle/`, or in their roots `Hash.lean` and `Merkle.lean`, imports no other part of Cryptography.
- A cryptographic module never imports Serialization.
- A specification never imports a property, a C export or a model.
- A specification imports nothing outside the Lean toolchain, which ships `Init`, `Std` and `Lean`.
  Mathlib and the probability libraries enter only in properties and models.
- No export runs specification code while it is elaborated.
  No export, and no module that an export reaches through its imports, meta-imports a module that reaches a specification.
  A specification never uses `meta import`, since an export may reach it later.
  The command that derives the Python conversions of an export runs while the export is elaborated, and its module meta-imports only the Lean toolchain.
- A C export imports only EthLib and the Lean toolchain, and a property that it imports reaches nothing else, directly or through other properties.
- A construction shared by two modules is written once, in the lowest layer both can import.
  A binary Merkle tree used by SSZ and by a hash-based signature is one example.

## Shared types

Modules meet at their types.
When two modules represent the same value differently, every caller converts between them, and every conversion is a place to get a length or a range wrong.
So the types that cross a module boundary are fixed here, and `EthLib/Base/` defines the ones that no single layer owns.

- Bytes of any length are a `ByteArray`.
- Bytes of a fixed length `n` are a `Vector UInt8 n`.
  The length is then part of the type, as `CONTRIBUTING.md` asks, and a 48-byte commitment cannot be passed where a 96-byte signature is expected.
  Such a value crosses a module boundary in its typed form, not as a `ByteArray`.
  The exceptions today are `kzgCommitmentToVersionedHash`, `Bls.Signatures.verify` and `messageId`, which later pull requests convert.
  At an external interface, one parser turns the bytes into the typed value or a typed error.
  A C export, EVM call data and a wire format are such interfaces.
- A fixed-size type keeps the name its source gives it, defined once by the layer that owns the concept.
  `Hash32`, `Bytes32` and `Address` belong to Base, `BLSPubkey` to Cryptography, `Root` and `Slot` to Consensus.
- Two of these types can have the same bytes and different meanings.
  A KZG commitment and a KZG proof are both 48 bytes.
  In consensus-specs, a Merkle root and the hash of an execution block are two classes of 32 bytes.
  A one-field structure over `Vector UInt8 n` keeps such types apart, because Lean then rejects one where the other is expected.
  This form applies to `KZGCommitment` and `VersionedHash`, which stay abbreviations until a pull request converts them.
  Another type takes the form only by a pull request that converts it and reports the cost of its port.
  That cost is the conversions at call sites, the edited theorems and the breaking change for Lean importers.
- Such a structure follows its source.
  It names a role, not validity, so a check such as `KeyValidate` stays a function or a separate type.
  A conversion between two of these types appears only where the source converts, as `Root(header.execution_block_hash)` does in consensus-specs.
  A name that the source only aliases, such as `Hash32 = Bytes32` in execution-specs, stays an `abbrev`.
  Two sources can disagree on whether a name is a type of its own, as they do for `Hash32`.
  Its definition then records both readings and the choice.
  `EthLib/Base/Hash32.lean` does not record them yet.
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
- A hash taken as an argument is one case of a resource.
  A resource is what a specification takes as an argument, so that a model, a test or another layer can supply it.
  The KZG trusted setup, the BLS signature checks and the execution engine are other cases.
  A resource enters as an explicit argument, either data or a record of operations.
  Resources that one caller supplies together can share one record, as in `BlockSources`.
  A hash that no model or test replaces is not a resource, and stays concrete, as Keccak-256 does in the EVM.
- A resource is one of two kinds.
  A protocol resource has a value that the protocol fixes or computes, such as the trusted setup or the BLS checks.
  It has one named production instance.
  That instance lives in the lowest layer that can import both the declaration of the resource and the code that computes its value.
  So `SignatureChecks.bls` lives in Consensus, `TrustedSetup.ofHex` in Cryptography, and `executionEngine` in Engine.
  An environment oracle answers what the specification leaves to the node, such as `BlockSources.blobsAndProofs`.
  It has no production instance, and the theorems about it hold for every answer, or for every answer that meets its laws.
- The laws of a resource are a separate `Prop`, written as a property in the proof library of the lowest layer that can state it.
  A theorem shows that the production instance meets them.
  Where no theorem does yet, `SOUNDNESS.md` names the missing proof as an assumption.
- A security property that holds only with high probability is not such a law.
  The theorems take it as a hypothesis, and `SOUNDNESS.md` names it as an assumption, as it does for `SignatureChecks.AggregateSound`.
- A test stub of a resource is an instance written for tests.
  It has a name, and a docstring that says which answers it fixes.
  Where a theorem can show it, a theorem shows that the stub breaks the laws or the assumptions.
  `SignatureChecks.acceptAll` accepts every signature, and `SignatureChecks.not_aggregateSound_acceptAll` shows that it fails `AggregateSound` when no key signed anything.
  A C export passes the production instance, unless it replays test vectors built for a stub.
  Its docstring then says so.
- A gas meter is not a resource.
  The protocol computes gas, and the EVM takes the meter as a class so that one definition runs with the meter of each fork.
  The two meters, `Nat` and `StateGasMeter`, and the class of their laws, `LawfulGasMeter`, stay in the specification library.
  The definition of a message call, `processMessage`, needs those laws to show that execution ends.

## Boundaries

A boundary is a resource that is a record of operations, declared by the module that uses them and supplied by its callers, such as `ExecutionEngine`.
[Shared types](#shared-types) says where its production instance, its laws and its test stubs live.
The shared types make the two sides fit, but they do not make them compose.
Each side must also know what the other guarantees, what it assumes, and what happens when an operation fails.
So a boundary also has a contract card: a short list of facts in the doc comment of the module that declares the operations.

New boundaries follow this rule.
Existing ones, such as `ExecutionEngine`, `SignatureChecks` and `BlockSources`, do not yet carry cards.

The conversions between Lean values and Python values, `ToPy`, `FromPy`, `ToPyItems` and `FromPyItems`, are not boundaries.
No specification takes them as an argument, so their laws `LawfulPy` and `LawfulPyItems` stay with them in the Lake library `Exports`.

The card is a list in the doc comment, with one item per field, in this order:

- Boundary: which layer uses the operations, which provides them, and where the production instance lives, or that an environment oracle has none.
- Owns: each type and state that crosses the boundary, with the layer that owns it.
- Operations: what each operation answers, and what each test stub answers.
- Laws: what the laws require, and whether a theorem or an assumption in `SOUNDNESS.md` covers the production instance.
- Failure: the error type, what each outcome means, and what the user must do on each.
- Guarantees: what success implies, and what it does not.
- Assumes: what each side assumes of the other.
- Readings: where the primary sources disagree or are silent, the reading taken, with the EIP, paper, RFC or standard that supports it.

A field with nothing to record says "none", so a reader can tell an empty field from a forgotten one.
The card holds the coarse facts that the types do not show.
It describes the operations and the laws, and does not restate their definitions.
It is a plain list, not a `text` block, so that each field reads as prose under the rules for doc comments in [`CONTRIBUTING.md`](CONTRIBUTING.md#doc-comments-in-lean).
A field with several facts has one sub-item per fact, each one sentence on its own line, within 100 columns.
Its fields describe behaviour and name no function or theorem, so that a renamed definition leaves the card correct.
A type that crosses the boundary is named in backticks.
Like the rest of the code, the Readings field cites only primary sources as the authority, as [Sources](#sources) says.
Where none of them settles a reading, the field states the reading itself.
It may name execution-specs or consensus-specs only in a provenance note, as [Sources](#sources) allows.

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

### When a change enters EthLib

A change to the protocol reaches mainnet through the stages of a network upgrade, which [EIP-7723](https://github.com/ethereum/EIPs/blob/b4552f44e3e3a79fa522abc346f065924142232d/EIPS/eip-7723.md) defines.
An EIP is first Proposed for Inclusion in an upgrade, then Considered for Inclusion, which means client teams intend to try it on devnets.
It is then Scheduled for Inclusion, and finally Included when the upgrade activates.
At any stage it can be Declined for Inclusion.
These stages, and not the status of the EIP document itself, decide where the specification of a change lives.

- An EIP that no upgrade has yet considered stays outside EthLib.
  To prototype or verify it, work in a fork of the repository.
  Another project can also import a pinned revision of EthLib and build on it.
- An EIP Considered or Scheduled for Inclusion in a named upgrade lives on a branch of ethereum/EthLib named after that upgrade.
  The work is then visible to everyone, and it follows the devnets of the upgrade.
- An upgrade merges into `master` once its meta EIP records a mainnet activation, with only its Scheduled EIPs.
  EIP-7723 gives stages to EIPs, not to upgrades, so the activation table of the meta EIP is the signal.
  An EIP Declined for Inclusion leaves the branch.
- EIP-7723 lets a Scheduled EIP move back to Considered or to Declined.
  If that happens after the merge, the EIP leaves `master`, and a Considered EIP returns to the branch.

So a contribution that adds an EIP ahead of its stage is not accepted, whoever or whatever writes it.
This keeps the repository free of changes that may never activate.

Two kinds of change have no stage of their own.

- A blob-parameter-only fork of EIP-7892 changes parameters and no rule.
  It enters when a meta EIP records its mainnet activation, as EIP-7607 of Fusaka does for BPO1 and BPO2.
  The code cites the EIP that fixes its parameters: EIP-8134 for BPO1 and EIP-8135 for BPO2.
- A standard outside the EIP process has no inclusion stages.
  A version that an upgrade requires, such as a version of the Engine API or of a libp2p protocol, enters with that upgrade.
  A standard that nodes of a deployed fork already use enters once it can be cited at a pinned commit.
  The beacon API and the era file format are such standards.
  Any other standard enters only as an exception that the maintainers choose, as the next paragraph says.

A few components are the exception, because EthLib means to be their reference by the time they reach mainnet, several upgrades ahead.
The maintainers choose these components, and record each decision in an issue.
The two components on the list have no such issue yet, only the issues that started their work:

- the hash-based signature XMSS, in [#29](https://github.com/ethereum/EthLib/issues/29),
- the hash-based signature SPHINCS, in [#41](https://github.com/ethereum/EthLib/issues/41).

Each is specified on its own, outside `Fork`, so no rule of an upgrade uses it.
It joins the timeline by the rule above, when an upgrade schedules it.

The stages apply to changes, not to forks.
On the branch of an upgrade, its constructor of `Fork`, such as Hegotá, exists from the first change that enters.
On `master`, the constructor appears when the upgrade merges.
The rules that wait for its other changes reject it as not yet specified.
The parity catalogue lists the cases of each pinned devnet, and a case runs only once its change has entered.
`scripts/check_spec_releases.py` reports when the specification repositories start the tests of a new upgrade, which tells a reviewer that a branch is due.

The Scope section lists what EthLib covers in the end.
It gives no order of work, except that the relay API and the two validator-client APIs come last.

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
The code cites only primary sources as the authority for a rule.
Such a source is an EIP or an RFC with its section, a NIST or SEC standard, or a paper.
Where no primary source states a rule, the doc comment states the rule itself, in words and in mathematics.
A reader then needs no other specification.
A contributor may read execution-specs and consensus-specs to understand a rule and to check the work.
The code does not cite them as the authority for a rule.

A comment in the code may still name execution-specs or consensus-specs in a provenance note.
The note names the text and the commit where a rule is stated.
If it is known, the note also names the commit that EthLib took the rule from.
[`CONTRIBUTING.md`](CONTRIBUTING.md#sources-of-truth) says when to write one, and where.
A provenance note is not a citation of authority.

Test vectors are a further exception, because a test must say what it checks against.
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
The rule that, among the properties, only a refinement module imports a model directly is a rule between modules, not between packages.

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
A theorem stays in the specification file in two cases, because a specification never imports a property:

- A definition or an instance of the specification uses it.
  `gasHeld_runFrame_le` in `EthLib/Execution/Evm/Interpreter.lean` is one, since the recursion of messages needs its bound.
- The users of a definition rely on it, such as a `@[simp]` lemma.
  A project that imports only the specification can then still use it.

Every other theorem goes under `Proofs/`.
Specification files already hold theorems that fit neither case, and a later change sorts them.
A model goes under `Proofs/` too, as the models of Casper FFG and LMD-GHOST do in `EthLib/Consensus/Proofs/Models/`.
Modules of one kind share a directory, under the part of the layer that uses them.
The precompiles are one kind, and only the EVM calls them, so ECRECOVER sits in `EthLib/Execution/Evm/Precompiles/Ecrecover.lean`, and its theorems in `EthLib/Execution/Proofs/Evm/Precompiles/Ecrecover.lean`.

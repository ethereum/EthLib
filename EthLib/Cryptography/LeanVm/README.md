# leanVM

A post-quantum Ethereum signs with hash-based signatures, and each one is a few kilobytes: a leanXMSS signature is 2404 bytes.
A block cannot carry one such signature per validator.
leanVM answers this with a proof: a prover runs a program that verifies the signatures, and publishes a short proof that the run was correct.
A verifier checks the proof instead of the signatures.

leanVM is a proof system for the executions of a small virtual machine, leanISA, over the binary fields `GF(2^64)` and `GF(2^128)`.
Its only hash is the Keccak-f[1600] permutation.
A program can verify earlier proofs as well as signatures, so proofs aggregate recursively.

The work in this directory specifies the leanVM prover, the leanVM verifier and the cryptography of aggregation, and proves them correct.
It is in progress: most of the files named here do not exist yet, and none of the theorems it names is proved yet.
This file says what the work proves, in which model, and where each part lives.
Each pull request of the work adds its part and keeps this file true.

## The three end theorems

The work ends in three theorems.

### Completeness

The verifier must accept honest proofs.
Take a valid execution of a program within the machine's size limits, and a rate exponent from 1 to 4 for the code that commits the execution.
The verifier accepts the honest prover's proof of that execution.
There is one exception.
At some steps the prover must find a nonce whose hash has a given number of zero bits, a proof of work.
The theorem excludes the case where that search finds no nonce within its budget of trials.

### Knowledge soundness

An accepted proof must come from a valid execution.
An adversary outputs a program, a public input and a proof, and the verifier checks them.
The extractor is an algorithm that reads the proof and the adversary's queries to the hash, and rebuilds an execution.
For every adversary that makes at most `Q <= 2^128` queries, the probability that the verifier accepts and the extractor returns no valid execution of the program on that input is at most

```text
(Q + 2^14) 2^-125 + 5 (Q + 2^14)^2 2^-256.
```

For `Q = 2^64` queries the first term is about `2^-61` and the second is below `2^-125`.
This is leanVM's bound.
If EthLib's proof gives a different constant, the theorem states that constant.

### One-hop unforgeability of aggregation

Aggregation combines signatures, and earlier aggregates, into one proof.
The guest program is the leanVM program that checks the signatures and the inner proofs.
EthLib defines the aggregation interface of [Hofheinz, Reichle and Wagner](https://eprint.iacr.org/2026/723), instantiates it with leanVM, and proves the instance correct and unforgeable across one level of recursion.
The theorem assumes the guest program's completeness and knowledge soundness as explicit hypotheses.

### What is not proved

- Soundness across several levels of recursion is an open research question, and no theorem claims it.
- Security against a quantum adversary is out of scope.
- The guest program, the leanXMSS and leanSPHINCS signature schemes inside aggregation, and the LeanDA data-availability check are later work.
  Aggregation takes the two signature schemes and the data-availability check as parameters.

## The model

The security theorems need an ideal hash, so they replace Keccak-f[1600] by a random permutation.
This permutation `pi` of `{0,1}^1600` is drawn uniformly and sampled lazily, and the adversary may query both `pi` and its inverse.
Keccak-256 becomes the sponge over `pi`, and the transcript calls `pi` directly.
The adversary is classical, and its code is fixed before `pi` is drawn.
Its query budget bounds the number of queries on every execution path, not on average.
Probabilities are `OracleComp` computations of VCVio, as in EthLib's leanXMSS security proof.

The interactive protocol is proved round-by-round sound, in the sense of [Canetti et al. (STOC 2019)](https://doi.org/10.1145/3313276.3316380).
Each verifier message has its own error, the probability that a cheating prover gets lucky at that message.
Every message is held to an error of at most `2^-125`.
A message whose error is `N / 2^128` is preceded by a proof of work of `b = max(0, ceil(log2 N) - 3)` bits, and each bit halves the error.

Take a message with `N = 46`:

```text
b      = ceil(log2 46) - 3 = 6 - 3 = 3
error  = 46 * 2^-128 * 2^-3
       = 46 * 2^-131
       < 64 * 2^-131
       = 2^-125
```

A message with `N <= 8` needs no proof of work, which is the case of every sumcheck round.

The proof is made non-interactive with a duplex sponge over Keccak-f, which derives each verifier message from the transcript so far.
Soundness transfers to the random permutation model query by query, following [Ben-Sasson, Chiesa and Spooner](https://eprint.iacr.org/2016/116) and Canetti et al.

The extractor is a Lean function.
It reads only the proof and the adversary's query log, and it never rewinds the adversary.
Its definition uses no choice axiom, and `lake exe check-decls` lists its axioms to confirm it.
EthLib states knowledge soundness with this explicit extractor and does not measure the extractor's running time.

## Dependencies

The specification files import only the Lean toolchain, as every specification in EthLib does.
The proof files may also import Mathlib, Batteries, VCVio and [ArkLib](https://github.com/Verified-zkEVM/ArkLib), a Lean library of interactive oracle proofs and coding theory.
ArkLib is pinned at commit `51a35e417c2ebbace76e4fff746d3f521bf1f812`.
That commit proves Theorem 4.10 of [Chiesa, Weissenberg, Yogev and Zheng](https://eprint.iacr.org/2026/2863), on affine combiners for Reed-Solomon proximity gaps, which the soundness of WHIR with affine folds needs.

EthLib uses each ArkLib result through one bridge theorem.
A bridge theorem restates the result over EthLib's definitions and derives the restatement from ArkLib's theorem.
EthLib never copies an ArkLib proof.

## Where things are

The specification lives under `EthLib/Cryptography/`, in the namespace `EthLib.Cryptography.<Module>`.
Each part follows a section of the [leanVM whitepaper](https://github.com/leanEthereum/leanVM/blob/fa4b43935667234e8e29c6cc19ffcfb3ab5164d5/doc/leanvm/main.tex), named in parentheses.

| Path | Contents | Whitepaper section |
| --- | --- | --- |
| `BinaryField/` | `K = GF(2^64)`, `E = K[y]/(y^2 + xy + 1)`, byte encodings | VM specification |
| `Multilinear/` | the hypercube, the equality polynomial, extension, suffixes, stacking, claims | Proving primitives; Committing the witness |
| `Sumcheck/` | the sumcheck verifier, compressed rounds, the equality-factored sumcheck, zerocheck | Proving primitives |
| `FiatShamir/` | the duplex sponge, grinding, the seed, the verifier's transcript | Proving primitives; End-to-end protocol |
| `AdditiveCode/` | subspace polynomials, the novel basis, the additive NTT, multiplication by `X`, column weights | Novel polynomial basis and additive NTT |
| `Whir/` | parameters, Merkle trees, affine folds, commitment, verifier, prover | Our PCS: WHIR / Ligerito with affine folds |
| `RingSwitching.lean` | the reduction of a claim over `E` to a commitment over `K` | Ring switching |
| `GrandProduct/` | fingerprints, the grand-product GKR | Arithmetization framework |
| `LeanVm/KeccakGkr/` | the GKR proof of Keccak-f[1600] | Proving Keccak by GKR |
| `LeanVm/Isa/` | instructions, machine state, one step, executions, bytecode, the interpreter | VM specification |
| `LeanVm/Arithmetization/` | the bus, lookups, size limits, the six instruction tables, the witness | Arithmetization framework; Bus interactions; The instruction tables |
| `LeanVm/Protocol/` | everything between the tables and the final opening | Committing the witness; End-to-end protocol |
| `LeanVm/Verifier.lean`, `LeanVm/Prover/`, `LeanVm/Extractor.lean` | the end-to-end verifier, the honest prover, the extractor | End-to-end protocol |
| `Aggregation/` | the interface, node statements, deferred checks, batching, the leanVM instance | Ethereum use cases |

The proofs mirror these paths under `EthLib/Cryptography/Proofs/`.
The random permutation model is `Proofs/Models/RandomPermutation.lean`, and round-by-round soundness and the Fiat-Shamir transfer are in `Proofs/Interaction/`.
The C exports are `EthLib/Cryptography/Exports/LeanVm.lean`, and the Python tests are in `bindings/python/tests/leanvm/`.

Test vectors are in `tests/cryptography/leanvm/<area>/<function>/<case>/data.yaml`, with a `format.md` and a `SHA256SUMS` per area.
A Rust program outside the EthLib tree computes them with the leanVM crates, and `format.md` records its command and commit.
No expected value comes from EthLib.

## Reading order

Each layer uses only the layers before it.

1. The binary fields `K` and `E`: every value of the protocol lies in one of them.
2. Multilinear polynomials: they represent every table column and every claim.
3. Sumcheck and zerocheck: they reduce a claim about a sum over the hypercube to a claim at one random point.
4. Fiat-Shamir: it derives the verifier's random messages from hashes.
5. Reed-Solomon codes on additive domains: the code that the commitment scheme tests.
6. WHIR: it commits to a polynomial and opens it at a point.
7. Ring switching: the prover commits over `K` while the protocol works over `E`.
8. The grand product, proved by GKR: it checks that the bus balances.
9. Keccak-f[1600] by GKR: the machine calls the permutation as one instruction.
10. The leanISA machine: it defines a valid execution.
11. The arithmetization: tables whose constraints and bus hold exactly when the execution is valid.
12. The protocol pieces: they reduce all table claims to one opening of one commitment.
13. The end-to-end verifier and prover, and the end theorems.
14. Recursive aggregation: the guest program runs the leanVM verifier.

## Review

Each piece of work is one pull request with a Conventional Commits title, `feat(leanvm): ...` for definitions and `proof(leanvm): ...` for proofs, and the `leanVM` label.
Automated review skips that label.
Each pull request needs a cryptographer's approval for its definitions and statements, and a Lean reviewer's approval for its proofs.
A definitions pull request contains no `sorry`; its theorems come in the next pull request.
A disagreement with leanVM goes on the issue, with the file and line on both sides, and is never fixed silently.

## Sources

- B. E. Diamond and J. Posen, [Polylogarithmic Proofs for Multilinears over Binary Towers](https://eprint.iacr.org/2024/504).
- B. E. Diamond and J. Posen, [Succinct Arguments over Towers of Binary Fields](https://eprint.iacr.org/2023/1784).
- G. Arnon, A. Chiesa, G. Fenzi and E. Yogev, [WHIR: Reed-Solomon Proximity Testing with Super-Fast Verification](https://eprint.iacr.org/2024/1586).
- A. Chiesa, G. Weissenberg, E. Yogev and K. Z. Zheng, [Affine Combiners for Reed-Solomon Proximity Gaps](https://eprint.iacr.org/2026/2863).
- A. Gruen, [Some Improvements for the PIOP for ZeroCheck](https://eprint.iacr.org/2024/108).
- S.-J. Lin, W.-H. Chung and Y. S. Han, [Novel Polynomial Basis and Its Application to Reed-Solomon Erasure Codes](https://arxiv.org/abs/1404.3458).
- E. Ben-Sasson, A. Chiesa and N. Spooner, [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116).
- R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G. N. Rothblum, R. D. Rothblum and D. Wichs, [Fiat-Shamir: From Practice to Theory](https://doi.org/10.1145/3313276.3316380).
- D. Hofheinz, M. Reichle and B. Wagner, [Hint-Free Multi-Signatures](https://eprint.iacr.org/2026/723).

Lean doc comments cite the papers, or state the rule when no paper does.

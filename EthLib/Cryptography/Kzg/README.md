# KZG polynomial commitments

A rollup posts its data to Ethereum in blobs.
A node must be able to check a piece of a blob without downloading all of it.
KZG commitments make that possible.

A blob is 4096 field elements, read as the values of a polynomial.
A KZG commitment binds the whole blob into 48 bytes.
A 48-byte proof then opens the committed polynomial at any point.
It convinces a verifier that the polynomial takes a given value there, without revealing the rest.

Ethereum uses KZG for blobs, by [EIP-4844][eip-4844].
It also uses KZG for the cells of data availability sampling, by [EIP-7594][eip-7594].

[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844
[eip-7594]: https://eips.ethereum.org/EIPS/eip-7594

This page was checked against EthLib commit `a0838f3`.
Check it again when a definition it names changes.

## Source

The commitment scheme is the one of Kate, Zaverucha and Goldberg, at ASIACRYPT 2010:
[Constant-Size Commitments to Polynomials and Their Applications][kzg10].
The module evaluates a blob's polynomial on the 4096-th roots of unity, in bit-reversed order.
A proof of one value is a commitment to the quotient polynomial.

The cell proofs follow Feist and Khovratovich,
[Fast amortized KZG proofs](https://eprint.iacr.org/2023/033).
The batch check of cell proofs is the [universal verification equation][uve].
Recovery follows the [FFT method for Reed-Solomon erasure recovery][rs-fft].

[kzg10]: https://doi.org/10.1007/978-3-642-17373-8_11
[uve]: https://ethresear.ch/t/a-universal-verification-equation-for-data-availability-sampling/13240
[rs-fft]: https://ethresear.ch/t/reed-solomon-erasure-code-recovery-in-n-log-2-n-time-with-ffts/3039

The trusted setup is the output of the KZG ceremony.
`TrustedSetupData.lean` records the file it comes from and its sha256.

## Operations

These ten operations are public:

| C export | Lean | File |
| --- | --- | --- |
| `eth_kzg_blob_to_kzg_commitment` | `blobToKzgCommitment` | `Core.lean` |
| `eth_kzg_compute_kzg_proof` | `computeKzgProof` | `Core.lean` |
| `eth_kzg_compute_blob_kzg_proof` | `computeBlobKzgProof` | `Core.lean` |
| `eth_kzg_verify_kzg_proof` | `verifyKzgProof` | `Core.lean` |
| `eth_kzg_verify_blob_kzg_proof` | `verifyBlobKzgProof` | `Core.lean` |
| `eth_kzg_verify_blob_kzg_proof_batch` | `verifyBlobKzgProofBatch` | `Core.lean` |
| `eth_kzg_compute_cells` | `computeCells` | `Cells.lean` |
| `eth_kzg_compute_cells_and_kzg_proofs` | `computeCellsAndKzgProofs` | `Cells.lean` |
| `eth_kzg_verify_cell_kzg_proof_batch` | `verifyCellKzgProofBatch` | `Cells.lean` |
| `eth_kzg_recover_cells_and_kzg_proofs` | `recoverCellsAndKzgProofs` | `Recovery.lean` |

Two internal functions also have test vectors and C exports.
They compute the challenge of a blob, and the challenge of the batch check of cell proofs.

Each of the ten operations returns `Except KzgError`, so it can fail with a typed error.
All of them except `computeCells` read the trusted setup, which they take as their first argument.
`TrustedSetup.ofHex` decodes the embedded setup.
The C exports decode it once, when their module is initialized.
The two challenge helpers return a field element.

Blobs, cells, commitments, proofs and field elements are byte vectors.
Their length is part of their type, as in the source.
The C exports read untyped bytes into these types, and reject a wrong length there.

## Test vectors

`tests/cryptography/kzg/` holds 344 cases:

| Handler | Cases |
| --- | ---: |
| `blob_to_kzg_commitment` | 11 |
| `compute_blob_kzg_proof` | 15 |
| `compute_cells` | 11 |
| `compute_cells_and_kzg_proofs` | 11 |
| `compute_challenge` | 9 |
| `compute_kzg_proof` | 52 |
| `compute_verify_cell_kzg_proof_batch_challenge` | 10 |
| `recover_cells_and_kzg_proofs` | 18 |
| `verify_blob_kzg_proof` | 29 |
| `verify_blob_kzg_proof_batch` | 24 |
| `verify_cell_kzg_proof_batch` | 32 |
| `verify_kzg_proof` | 122 |

They match the consensus-specs `v1.7.0-alpha.12` general vectors and the `ethereum/c-kzg-4844` cases byte for byte.
Their expected values come from the Python specification, not from EthLib.
`tests/cryptography/kzg/SHA256SUMS` pins each one, and CI checks the pins.

[`tests/cryptography/README.md`](../../../tests/cryptography/README.md) explains the pins and the check against the upstream archive.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Kzg/`.
Apart from the rejection of malformed input, they cover the steps the operations are built from.
They do not cover the operations' results.

**Malformed input.**
The public operations reject a wrong size, and lists of different lengths, with a typed error.
Those proofs are in `Core.lean`, `Cells.lean` and `Recovery.lean`.

**Bytes.**
Field elements travel as 32-byte big-endian integers, so decoding must not merge two inputs.
Those proofs are in `Polynomials.lean`.

Big-endian decoding is injective on byte strings of one length (`bytesBEToNat_inj`).
The length matters: without it decoding is not injective, since `00` and `00 00` both decode to 0.

In the other direction, take the `len`-byte encoding of `n`.
Its decoding is `n` when `n < 256^len` (`bytesBEToNat_intToBytesBE_of_lt`).
Otherwise it is `n mod 256^len` (`bytesBEToNat_intToBytesBE`).
Encoding a decoded string at its own length returns that string (`intToBytesBE_bytesBEToNat`).

**Bit reversal.**
A blob stores its values in bit-reversed order of the roots of unity.
So the code permutes indices by reversing their bits (`BitReversal.lean`).
Reversing the bits of an index below `2^k` twice returns it (`reverseBits_reverseBits`).
So the bit-reversal permutation of an array of `2^k` elements is its own inverse.
The theorem is `bitReversalPermutation_bitReversalPermutation`.

**Evaluation.**
A proof opens the polynomial at a point `z`.
So the code must compute the polynomial's value at `z` from the blob alone.

Take a blob that holds the values of a polynomial `f` of degree below 4096.
The values are at the bit-reversed roots of unity.
Barycentric evaluation of that blob at any `z` returns `f(z)`.
The theorem is `evaluatePolynomialInEvaluationForm_eq_eval`, in `Evaluation.lean`.

**FFT.**
The FFT moves a polynomial between its coefficients and its values on the roots of unity.
Take `2^k` points with a primitive `2^k`-th root.
The inverse FFT undoes the FFT, and the FFT undoes the inverse.
The theorems are `fftField_fftField_inv` and `fftField_inv_fftField`, in `FftInverse.lean`.

The same round trips hold on a coset and on the extended domain of 8192 points.
Those proofs are in `CosetInverse.lean` and `ExtendedFft.lean`.
The outputs are the values of the coefficient polynomial on the domain and on a coset.
Those proofs are in `FftEvaluation.lean`.

**Interpolation and division.**
Interpolation through fewer than 8192 distinct points returns a polynomial through every point.
The theorem is `interpolatePolynomialcoeff_spec_of_distinct`.
Long division returns a quotient `q` with `a(x) = q(x) * b(x) + r(x)`.
Here `r` is the remainder it computes (`dividePolynomialcoeff_eval_identity`).

**Recovery.**
Data availability sampling extends a blob to 128 cells, so that any half of them determine it.
Take at least 64 of the 128 cells, at distinct valid indices.
They hold the values of a polynomial with 4096 coefficients.
Recovery returns that polynomial.
The theorem is `recoverPolynomialcoeff_correct_of_valid_indices`, in `RecoveryReconstruction.lean`.

Along the way, recovery divides by values on a coset.
The coset avoids every root, so no division by zero occurs.
Those proofs are in `RecoveryCoset.lean` and `VanishingNonzero.lean`.

**Linear combinations.**
A commitment is a linear combination of the setup's points, computed by `g1LincombPoints`.
For arrays of equal length, `g1LincombPoints` returns `Bls.G1.msm` of its points and scalars.
The theorem is `g1LincombPoints_eq_msm`, in `Core.lean`.
That theorem is an equality of two definitions.

The mathematical sum comes from `Bls.G1.toPoint_msm`, in `Proofs/Bls/G1Msm.lean`.
Let every point be valid, which means a nonsingular point of the curve.
Then `msm` returns a valid point equal to `sum_i scalars_i * points_i` in the curve group.

**The commitment.**
A setup is well formed for a secret `τ` when its points represent `τ^i` and the Lagrange basis at `τ`.
For such a setup, `blobToKzgCommitment_represents`, in `Proofs/Kzg/Commitment.lean`, proves that a blob's commitment represents its polynomial at `τ`.
That a secret makes the embedded setup well formed is an assumption, recorded in SOUNDNESS.md D3.

**The proofs.**
Under the pairing law and for a well-formed setup, honest single proofs and blob proofs verify.
`Proofs/Kzg/Verify.lean` proves both, at every point, inside or outside the domain.

**Binding.**
For single proofs, a theorem reduces binding to a hard problem.
Two accepted openings to different values give a strong Diffie–Hellman solution,
in `Proofs/Kzg/Binding.lean`.

**The ceremony.**
The trusted setup came from a ceremony in which many participants each mixed in a secret.

`checksSufficient_of_subgroupChecks`, in `CeremonyChecks.lean`, is about the ceremony's pairing checks.
They force each point of a contribution to represent the expected power of the secret.
A point represents a scalar when its group element is that multiple of the generator.
The coordinates of the point do not matter, so the theorem applies to decoded points.
It assumes the pairing law, the subgroup checks, and that two points are not at infinity.

## What is not proved

- No theorem states what the batch check of blobs returns on valid input.
  For the batch check of openings, `Proofs/Kzg/BatchBinding.lean` states it and proves binding.
  An accepted batch has every opening valid, or its challenge is a root of a nonzero polynomial.
  `Proofs/Kzg/BatchChallenge.lean` bounds the probability of that root with the hash as a random oracle.
  The adversary may query the oracle `q` times, and the bound is `(q + 1) (n - 1) / r` for `n` openings.
  `Proofs/Kzg/CellBatchBinding.lean` states what the batch check of cells returns on accepted input, with the bound.
- Binding of the batch check of blobs is not proved.
  For cells, `Proofs/Kzg/CellBinding.lean` proves binding.
  Two accepted cells at one index with different values give a solution of the bilinear variant of the problem, or the challenge is a root.
  `Proofs/Kzg/CellVerifier.lean` states both results for the outer check, which removes repeated commitments.
  Binding also needs the ceremony secret to stay unknown, which no proof can show.
- The trusted setup itself is not proved correct.
  Its bytes match the pinned file that `TrustedSetupData.lean` names.
  `TrustedSetup.ofHex_valid` proves that each point of the embedded setup is on its curve,
  if the setup decodes.
  No theorem says that it decodes, that its points lie in the subgroup,
  or that they are powers of one secret.
  The Python suite checks that each point decodes and lies in the subgroup,
  in `bindings/python/tests/kzg/test_trusted_setup.py`.
- The pairing law that the ceremony theorem assumes is not proved.
  It is bilinearity together with non-degeneracy.

## What the kernel cannot evaluate

This section is about a limit on computing results inside Lean.
It is separate from the missing theorems in the previous section.

The operations are ordinary definitions.
The trusted setup is an argument of each one that reads it.
So the kernel can unfold an operation, and `scripts/check_decls_baseline.txt` lists nothing for KZG.
To compute a known answer on the embedded setup, the kernel must first decode its 8257 points.
No theorem does that yet.
`computeCells` and the two challenge helpers do not read the setup.

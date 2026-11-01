# KZG polynomial commitments

A rollup posts its data to Ethereum in blobs, and a node must be able to check a piece of a blob without downloading all of it.
KZG commitments make that possible.
A blob is 4096 field elements, read as the values of a polynomial, and a KZG commitment binds the whole blob into 48 bytes.
A 48-byte proof then opens the committed polynomial at any point: it convinces a verifier that the polynomial takes a given value there, without revealing the rest.

Ethereum uses KZG for blobs (EIP-4844, from Deneb) and for the cells of data availability sampling (EIP-7594, from Fulu).

This page was checked against EthLib commit `a0838f3`.
Check it again when a definition it names changes.

## Source

The specification was two documents in `ethereum/consensus-specs`:

- [`specs/deneb/polynomial-commitments.md`](https://github.com/ethereum/consensus-specs/blob/8a3df1d79d70000801407e33d660171be9cd06d1/specs/deneb/polynomial-commitments.md) covers blobs: commitments, proofs and their verification.
- [`specs/fulu/polynomial-commitments-sampling.md`](https://github.com/ethereum/consensus-specs/blob/8a3df1d79d70000801407e33d660171be9cd06d1/specs/fulu/polynomial-commitments-sampling.md) covers cells: cell proofs, batch verification and recovery.

[ethereum/consensus-specs#5398](https://github.com/ethereum/consensus-specs/pull/5398) removed both, on the grounds that the KZG specification should exist only in `ethereum/cryptography-specs`, which is now this repository.
The links point to consensus-specs commit `8a3df1d79d70000801407e33d660171be9cd06d1`, the parent of that removal, so they hold the last text of both documents.

Every function of the two documents has a Lean definition, except `is_power_of_two`.
Each keeps its name in Lean's casing, so `compute_cells_and_kzg_proofs` is `computeCellsAndKzgProofs`, and the private `_fft_field` is `fftFieldAux`.

The trusted setup is consensus-specs `presets/mainnet/trusted_setups/trusted_setup_4096.json`.
`TrustedSetupData.lean` records the commit it comes from and its sha256.

## Operations

The two documents mark these ten functions as public methods:

| consensus-specs | Lean | File |
| --- | --- | --- |
| `blob_to_kzg_commitment` | `blobToKzgCommitment` | `Core.lean` |
| `compute_kzg_proof` | `computeKzgProof` | `Core.lean` |
| `compute_blob_kzg_proof` | `computeBlobKzgProof` | `Core.lean` |
| `verify_kzg_proof` | `verifyKzgProof` | `Core.lean` |
| `verify_blob_kzg_proof` | `verifyBlobKzgProof` | `Core.lean` |
| `verify_blob_kzg_proof_batch` | `verifyBlobKzgProofBatch` | `Core.lean` |
| `compute_cells` | `computeCells` | `Cells.lean` |
| `compute_cells_and_kzg_proofs` | `computeCellsAndKzgProofs` | `Cells.lean` |
| `verify_cell_kzg_proof_batch` | `verifyCellKzgProofBatch` | `Cells.lean` |
| `recover_cells_and_kzg_proofs` | `recoverCellsAndKzgProofs` | `Recovery.lean` |

Two internal functions, `compute_challenge` and `compute_verify_cell_kzg_proof_batch_challenge`, also have test vectors and C exports.
Each of the twelve has a C export named `eth_kzg_` followed by its consensus-specs name.

Each of the ten operations returns in `KzgM`, an `ExceptT` over `IO`, so it can fail with a typed error.
All of them except `computeCells` read the trusted setup, with `TrustedSetup.get!`.
The two challenge helpers are pure: each returns a field element.

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

They match the consensus-specs `v1.7.0-alpha.12` general vectors byte for byte, and their expected values come from the Python specification, not from EthLib.
`tests/cryptography/kzg/SHA256SUMS` pins each one, and CI checks the pins.

The vectors are pinned to `v1.7.0-alpha.12`, while the source links point to `8a3df1d`.
Between the two, the documents changed only the capitalization of their integer types, such as `uint64` to `Uint64` and `uint256` to `Uint256`, which changes no value and no behaviour.

[`tests/cryptography/README.md`](../../../tests/cryptography/README.md) explains the pins and the check against the upstream archive.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Kzg/`.
Apart from the rejection of malformed input, they cover the steps the operations are built from, not the operations' results.

**Malformed input.**
The public operations reject a wrong size, and lists of different lengths, with a typed error (`Core.lean`, `Cells.lean`, `Recovery.lean`).

**Bytes.**
Field elements travel as 32-byte big-endian integers, so decoding must not merge two inputs (`Polynomials.lean`).
Big-endian decoding is injective on byte strings of one length (`bytesBEToNat_inj`).
The length matters: without it decoding is not injective, since `00` and `00 00` both decode to 0.
In the other direction, decoding the `len`-byte encoding of `n` returns `n` when `n < 256^len` (`bytesBEToNat_intToBytesBE_of_lt`), and `n mod 256^len` otherwise (`bytesBEToNat_intToBytesBE`).
Encoding a decoded string at its own length returns that string (`intToBytesBE_bytesBEToNat`).

**Bit reversal.**
A blob stores its values in bit-reversed order of the roots of unity, so the code permutes indices by reversing their bits (`BitReversal.lean`).
Reversing the bits of an index below `2^k` twice returns it (`reverseBits_reverseBits`), and so the bit-reversal permutation of an array of `2^k` elements is its own inverse (`bitReversalPermutation_bitReversalPermutation`).

**Evaluation.**
A proof opens the polynomial at a point `z`, so the code must compute the polynomial's value at `z` from the blob alone.
Take a blob holding the values of a polynomial `f` of degree below 4096 at the bit-reversed roots of unity.
Barycentric evaluation of that blob at any `z` returns `f(z)` (`evaluatePolynomialInEvaluationForm_eq_eval`, `Evaluation.lean`).

**FFT.**
The FFT moves a polynomial between its coefficients and its values on the roots of unity.
On `2^k` points with a primitive `2^k`-th root, the inverse FFT undoes the FFT, and the FFT undoes the inverse (`fftField_fftField_inv`, `fftField_inv_fftField`, `FftInverse.lean`).
The same round trips hold on a coset and on the extended domain of 8192 points (`CosetInverse.lean`, `ExtendedFft.lean`).
The outputs are the evaluations of the coefficient polynomial, on the domain and on a coset (`FftEvaluation.lean`).

**Interpolation and division.**
Interpolation through fewer than 8192 distinct points returns a polynomial through every point (`interpolatePolynomialcoeff_spec_of_distinct`).
Long division returns a quotient `q` with `a(x) = q(x) * b(x) + r(x)`, where `r` is the remainder it computes (`dividePolynomialcoeff_eval_identity`).

**Recovery.**
Data availability sampling extends a blob to 128 cells, so that any half of them determine it.
Take at least 64 of the 128 cells, at distinct valid indices, holding the values of a polynomial with 4096 coefficients.
Recovery returns that polynomial (`recoverPolynomialcoeff_correct_of_valid_indices`, `RecoveryReconstruction.lean`).
Along the way it divides by values on a coset, and the coset it uses avoids every root, so no division by zero occurs (`RecoveryCoset.lean`, `VanishingNonzero.lean`).

**Linear combinations.**
A commitment is a linear combination of the setup's points, computed by `g1LincombPoints`.
For arrays of equal length, `g1LincombPoints` returns `Bls.G1.msm` of its points and scalars (`g1LincombPoints_eq_msm`, `Core.lean`).
That theorem is an equality of two definitions; the mathematical sum comes from `Bls.G1.toPoint_msm` (`Proofs/Bls/G1Msm.lean`).
When every point is valid, which means a nonsingular point of the curve, `msm` returns a valid point equal to `sum_i scalars_i * points_i` in the curve group.

**The ceremony.**
The trusted setup came from a ceremony in which many participants each mixed in a secret.
`checksSufficient` (`CeremonyChecks.lean`) shows that the ceremony's pairing checks force each point of a contribution to be the expected power of the secret.
It assumes `ConcreteBlsLaws`, `SubgroupExponents`, and that two points are not at infinity.

## What is not proved

- No theorem states the result of an operation on valid input; in particular, none says that an honest proof verifies.
- No security property, such as binding, is proved.
  Binding also needs the ceremony secret to stay unknown, which no proof can show.
- The trusted setup itself is not proved correct.
  Its bytes match the consensus-specs file, but no theorem says that they decode to valid points, or that they are powers of one secret.
- `ConcreteBlsLaws`, the law of the BLS pairing that `checksSufficient` assumes, is not proved: it is `pairingEq_mul_iff`, bilinearity together with non-degeneracy.
- `SubgroupExponents`, which stands in for the subgroup checks in `checksSufficient`, is not proved.

## What the kernel cannot evaluate

This is a limit on computing results inside Lean, separate from the missing theorems in the previous section.

The operations are ordinary definitions, and the kernel can unfold them.
The setup, though, lives in `TrustedSetup.globalRef`, an `IO.Ref` created when the module is initialized, and that reference is opaque to the kernel.
So the kernel cannot compute the result of an operation that reads the setup, for example to check a known answer.
`computeCells` and the two challenge helpers do not read it.

`scripts/check_decls_baseline.txt` lists `TrustedSetup.globalRef` as `opaque`, and `TrustedSetup.get!` and `KzgM` as `reaches-opaque`.
That second kind means a definition reaches an opaque constant when unfolded, not that it is opaque itself.

The pairing that verification uses comes from the BLS module.
The baseline lists its `Fp2.powNat` and `Fp12.powNat` as `partial`, and its `millerLoop` as `reaches-opaque`.

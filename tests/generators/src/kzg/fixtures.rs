//! The inputs every KZG generator draws from: field elements, blobs, points and cells.
//!
//! The values follow the consensus-specs KZG generators, so the pinned cases come out byte for byte.
//! Field arithmetic uses the `bls12_381` crate, independent of the Lean code under test.

use std::array;
use std::sync::LazyLock;

use bls12_381::{G1Affine, G1Projective, Scalar};
use ethlib::{Error, kzg};
use ethlib_vectors::Bytes;

use crate::memo::Memo;

/// The generator of the multiplicative group of the scalar field.
///
/// `PRIMITIVE_ROOT_OF_UNITY` in consensus-specs, `deneb/polynomial-commitments.md`.
const PRIMITIVE_ROOT_OF_UNITY: u64 = 7;

/// The big-endian encoding of a field element, as a blob stores it.
pub(crate) fn field_element(x: Scalar) -> [u8; 32] {
    // The crate encodes little-endian, and the specification big-endian.
    let mut bytes = x.to_bytes();
    bytes.reverse();
    bytes
}

/// `base^exponent` in the scalar field.
fn pow(base: u64, exponent: u64) -> Scalar {
    Scalar::from(base).pow_vartime(&[exponent, 0, 0, 0])
}

/// The 256-bit big-endian integer `r + k`, where `r` is the scalar field modulus.
///
/// Every such integer is at least `r`, so none of them is a canonical field element.
fn modulus_plus(k: u8) -> [u8; 32] {
    // Start from r - 1, the largest field element, and add 1 + k with carry.
    //
    //     r - 1 = -1 in the field
    //     r + k = (r - 1) + (1 + k), which stays below 2^256
    let mut bytes = field_element(-Scalar::one());
    let mut carry = u16::from(k) + 1;
    for byte in bytes.iter_mut().rev() {
        let sum = u16::from(*byte) + carry;
        *byte = sum.to_le_bytes()[0];
        carry = sum >> 8;
    }
    bytes
}

/// A primitive root of unity of the given order in the scalar field.
///
/// It is `7^((r - 1) / order)`, and the order must be a power of two dividing `r - 1`.
fn root_of_unity(order: usize) -> Scalar {
    // r - 1 = 2^32 * t with t odd, so any power of two up to 2^32 divides it.
    assert!(order.is_power_of_two() && order.trailing_zeros() <= 32, "the order divides r - 1");

    // Compute (r - 1) / order as a right shift of r - 1, limb by limb.
    let little_endian = (-Scalar::one()).to_bytes();
    let limbs: [u64; 4] = array::from_fn(|i| {
        u64::from_le_bytes(little_endian[8 * i..8 * i + 8].try_into().expect("eight bytes per limb"))
    });
    let shift = order.trailing_zeros();
    let exponent: [u64; 4] = array::from_fn(|i| {
        // Each limb takes its low bits from the limb above, except the top limb.
        let carried = match limbs.get(i + 1) {
            Some(next) if shift > 0 => next << (64 - shift),
            _ => 0,
        };
        (limbs[i] >> shift) | carried
    });
    Scalar::from(PRIMITIVE_ROOT_OF_UNITY).pow_vartime(&exponent)
}

/// A blob or cell whose `i`-th field element is `element(i)`.
fn elements(count: usize, element: impl Fn(u64) -> [u8; 32]) -> Vec<u8> {
    (0..count as u64).flat_map(element).collect()
}

/// The number of well-formed field elements.
pub(crate) const FIELD_ELEMENT_COUNT: usize = 6;

/// The well-formed field elements, numbered as the case names number them.
///
/// ```text
///     0 : 0                          2 : 2               4 : r - 1
///     1 : 1                          3 : 5^1235          5 : the primitive 4096-th root of unity
/// ```
pub(crate) static VALID_FIELD_ELEMENTS: LazyLock<[[u8; 32]; FIELD_ELEMENT_COUNT]> = LazyLock::new(|| {
    [
        field_element(Scalar::zero()),
        field_element(Scalar::one()),
        field_element(Scalar::from(2)),
        field_element(pow(5, 1235)),
        field_element(-Scalar::one()),
        // The second element of the evaluation domain, in natural order.
        field_element(root_of_unity(kzg::constants().field_elements_per_blob)),
    ]
});

/// 32-byte strings that are not canonical field elements, and strings of the wrong length.
///
/// ```text
///     0 : r              2 : 2^256 - 1             4 : 33 bytes
///     1 : r + 1          3 : 2^256 - 2^128         5 : 31 bytes
/// ```
pub(crate) static INVALID_FIELD_ELEMENTS: LazyLock<[Vec<u8>; 6]> = LazyLock::new(|| {
    let zero = VALID_FIELD_ELEMENTS[0];
    [
        modulus_plus(0).to_vec(),
        modulus_plus(1).to_vec(),
        vec![0xff; 32],
        [[0xff; 16], [0x00; 16]].concat(),
        [&zero[..], &[0]].concat(),
        zero[..31].to_vec(),
    ]
});

/// The well-formed blobs, numbered as the case names number them.
///
/// ```text
///     0 : all zeros              4 : 5^(i + 256)
///     1 : all twos               5 : all r - 1
///     2 : 2^(i + 256)            6 : zero but a one at index 3211
///     3 : 3^(i + 256)
/// ```
static VALID_BLOBS: LazyLock<[Vec<u8>; ValidBlob::COUNT]> = LazyLock::new(|| {
    let n = kzg::constants().field_elements_per_blob;
    [
        vec![0; kzg::constants().bytes_per_blob],
        elements(n, |_| field_element(Scalar::from(2))),
        elements(n, |i| field_element(pow(2, i + 256))),
        elements(n, |i| field_element(pow(3, i + 256))),
        elements(n, |i| field_element(pow(5, i + 256))),
        elements(n, |_| field_element(-Scalar::one())),
        elements(n, |i| field_element(if i == 3211 { Scalar::one() } else { Scalar::zero() })),
    ]
});

/// Malformed blobs.
///
/// ```text
///     0 : all 0xff bytes                    2 : blob 2 with one extra byte
///     1 : zero but r at index 2111          3 : blob 2 without its last byte
/// ```
pub(crate) static INVALID_BLOBS: LazyLock<[Vec<u8>; 4]> = LazyLock::new(|| {
    let n = kzg::constants().field_elements_per_blob;
    let random = ValidBlob::RANDOM_VALID1.slice();
    [
        vec![0xff; kzg::constants().bytes_per_blob],
        elements(n, |i| if i == 2111 { modulus_plus(0) } else { [0; 32] }),
        [random, &[0]].concat(),
        random[..random.len() - 1].to_vec(),
    ]
});

/// The compressed G1 generator.
pub(crate) static G1: LazyLock<[u8; 48]> = LazyLock::new(|| G1Affine::generator().to_compressed());

/// The compressed G1 point at infinity: `0xc0` followed by zeros.
pub(crate) static G1_POINT_AT_INFINITY: LazyLock<[u8; 48]> = LazyLock::new(|| G1Affine::identity().to_compressed());

/// Malformed compressed G1 points.
///
/// ```text
///     0 : 47 bytes                 2 : on the curve, outside the G1 subgroup
///     1 : 49 bytes                 3 : not on the curve
/// ```
pub(crate) static INVALID_G1_POINTS: LazyLock<[Vec<u8>; 4]> = LazyLock::new(|| {
    [
        G1[..G1.len() - 1].to_vec(),
        [&G1[..], &[0]].concat(),
        hex::decode("8123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")
            .expect("valid hex"),
        hex::decode("8123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde0")
            .expect("valid hex"),
    ]
});

/// Well-formed cells: `b^(i + 256)` for the bases 2, 3 and 5.
pub(crate) static VALID_CELLS: LazyLock<[Vec<u8>; 3]> = LazyLock::new(|| {
    let n = kzg::constants().field_elements_per_cell;
    [2, 3, 5].map(|base| elements(n, |i| field_element(pow(base, i + 256))))
});

/// Malformed cells.
///
/// ```text
///     0 : every element 2^256 - 1          2 : cell 0 without its last byte
///     1 : zero but r at index 7            3 : cell 1 with one extra byte
/// ```
pub(crate) static INVALID_CELLS: LazyLock<[Vec<u8>; 4]> = LazyLock::new(|| {
    let n = kzg::constants().field_elements_per_cell;
    let [first, second, _] = &*VALID_CELLS;
    [
        elements(n, |_| [0xff; 32]),
        elements(n, |i| if i == 7 { modulus_plus(0) } else { [0; 32] }),
        first[..first.len() - 1].to_vec(),
        [&second[..], &[0]].concat(),
    ]
});

/// `point + G1`, compressed.
///
/// It turns a correct proof or commitment into a well-formed but wrong one.
///
/// # Panics
///
/// Panics if `point` is not a valid compressed G1 point.
pub(crate) fn add_generator(point: &[u8]) -> Bytes {
    let bytes: &[u8; 48] = point.try_into().expect("a compressed G1 point is 48 bytes");
    let point = G1Affine::from_compressed(bytes).expect("a valid G1 point");
    G1Affine::from(G1Projective::from(point) + G1Affine::generator()).to_compressed().into()
}

/// A cell split into its field elements, the form the batch challenge takes.
pub(crate) fn coset_evals(cell: &[u8]) -> Vec<Bytes> {
    cell.chunks(kzg::constants().bytes_per_field_element).map(Bytes::from).collect()
}

/// Every cell of an extended blob, and one proof per cell.
pub(crate) type CellsAndProofs = (Vec<Bytes>, Vec<Bytes>);

/// `blob_to_kzg_commitment`, computed once per blob.
pub(crate) fn blob_to_kzg_commitment(blob: &[u8]) -> Result<Bytes, Error> {
    static MEMO: Memo<Result<Bytes, Error>> = Memo::new();
    MEMO.get(&[blob], || kzg::blob_to_kzg_commitment(blob).map(Bytes))
}

/// `compute_blob_kzg_proof`, computed once per input.
pub(crate) fn compute_blob_kzg_proof(blob: &[u8], commitment: &[u8]) -> Result<Bytes, Error> {
    static MEMO: Memo<Result<Bytes, Error>> = Memo::new();
    MEMO.get(&[blob, commitment], || kzg::compute_blob_kzg_proof(blob, commitment).map(Bytes))
}

/// `compute_kzg_proof`, computed once per input: the proof, and the value `y`.
pub(crate) fn compute_kzg_proof(blob: &[u8], z: &[u8]) -> Result<(Bytes, Bytes), Error> {
    static MEMO: Memo<Result<(Bytes, Bytes), Error>> = Memo::new();
    MEMO.get(&[blob, z], || kzg::compute_kzg_proof(blob, z).map(|(proof, y)| (Bytes(proof), Bytes(y))))
}

/// `compute_cells_and_kzg_proofs`, computed once per blob.
///
/// It is the slowest operation, and every cell case builds on it.
pub(crate) fn compute_cells_and_kzg_proofs(blob: &[u8]) -> Result<CellsAndProofs, Error> {
    static MEMO: Memo<Result<CellsAndProofs, Error>> = Memo::new();
    let bytes = |items: Vec<Vec<u8>>| items.into_iter().map(Bytes).collect();
    MEMO.get(&[blob], || kzg::compute_cells_and_kzg_proofs(blob).map(|(cells, proofs)| (bytes(cells), bytes(proofs))))
}

/// One of the well-formed blobs, and the Lean outputs that other cases build on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ValidBlob(usize);

impl ValidBlob {
    /// The number of well-formed blobs.
    pub(crate) const COUNT: usize = 7;

    /// The blob of zeros: its polynomial is zero.
    pub(crate) const ALL_ZEROS: Self = Self(0);

    /// The blob of twos: its polynomial is the constant 2.
    pub(crate) const ALL_TWOS: Self = Self(1);

    /// The blob of powers of two.
    pub(crate) const RANDOM_VALID1: Self = Self(2);

    /// The blob numbered `index` in the case names.
    pub(crate) fn at(index: usize) -> Self {
        assert!(index < Self::COUNT, "there are {} valid blobs", Self::COUNT);
        Self(index)
    }

    /// Every well-formed blob, in order.
    pub(crate) fn all() -> impl Iterator<Item = Self> + Clone {
        (0..Self::COUNT).map(Self)
    }

    /// The number of the blob in case names.
    pub(crate) fn index(self) -> usize {
        self.0
    }

    /// The blob itself.
    pub(crate) fn bytes(self) -> Bytes {
        self.slice().into()
    }

    /// The blob's commitment.
    pub(crate) fn commitment(self) -> Bytes {
        honest(blob_to_kzg_commitment(self.slice()))
    }

    /// The proof of the blob against its commitment.
    pub(crate) fn blob_kzg_proof(self) -> Bytes {
        honest(compute_blob_kzg_proof(self.slice(), &self.commitment()))
    }

    /// The proof and the value of the blob's polynomial at the well-formed field element `z`.
    pub(crate) fn kzg_proof(self, z: usize) -> (Bytes, Bytes) {
        honest(compute_kzg_proof(self.slice(), &VALID_FIELD_ELEMENTS[z]))
    }

    /// Every cell of the extended blob, and one proof per cell.
    pub(crate) fn cells_and_proofs(self) -> CellsAndProofs {
        honest(compute_cells_and_kzg_proofs(self.slice()))
    }

    /// The blob, borrowed from the fixture table.
    fn slice(self) -> &'static [u8] {
        &VALID_BLOBS[self.0]
    }
}

/// The output of an operation on a well-formed fixture, which must succeed.
fn honest<T>(result: Result<T, Error>) -> T {
    result.unwrap_or_else(|err| panic!("EthLib rejected a well-formed fixture: {err}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn root_of_unity_has_the_requested_order() {
        // w is a primitive n-th root exactly when w^n = 1 and w^(n/2) = -1.
        let n = 4096;
        let w = root_of_unity(n);
        assert_eq!(w.pow_vartime(&[n as u64, 0, 0, 0]), Scalar::one());
        assert_eq!(w.pow_vartime(&[n as u64 / 2, 0, 0, 0]), -Scalar::one());
    }

    #[test]
    fn modulus_encodings_are_one_apart() {
        // r and r + 1 differ only in the last byte, which ends in 0x01 and 0x02.
        //
        //     r = 0x73eda753...00000001
        let (r, r_plus_one) = (modulus_plus(0), modulus_plus(1));
        assert_eq!(r[..31], r_plus_one[..31]);
        assert_eq!((r[0], r[31], r_plus_one[31]), (0x73, 0x01, 0x02));
    }

    #[test]
    fn field_elements_are_big_endian() {
        // One is 31 zero bytes then 0x01.
        let one = field_element(Scalar::one());
        assert_eq!(one[31], 1);
        assert!(one[..31].iter().all(|&b| b == 0));
    }
}

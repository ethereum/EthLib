//! The bindings reach Lean, carry its answers back, and work from any thread.
//!
//! Each test runs only cheap calls: a rejection at the boundary, or a constant.
//! The full behaviour of each operation is pinned by the test vectors.

use std::thread;

use ethlib::{bls, kzg};

#[test]
fn kzg_sizes_match_the_specification() {
    // Expected values, from consensus-specs:
    //
    //     deneb : FIELD_ELEMENTS_PER_BLOB = 4096, BYTES_PER_FIELD_ELEMENT = 32
    //             KZGCommitment and KZGProof are Bytes48
    //     fulu  : FIELD_ELEMENTS_PER_CELL = 64, CELLS_PER_EXT_BLOB = 128
    let c = kzg::constants();
    assert_eq!(c.bytes_per_field_element, 32);
    assert_eq!(c.bytes_per_commitment, 48);
    assert_eq!(c.bytes_per_proof, 48);
    assert_eq!(c.field_elements_per_blob, 4096);
    assert_eq!(c.field_elements_per_cell, 64);
    assert_eq!(c.cells_per_ext_blob, 128);

    // The byte sizes follow from the counts.
    //
    //     blob : 4096 * 32 = 131072
    //     cell :   64 * 32 =   2048
    assert_eq!(c.bytes_per_blob, c.field_elements_per_blob * c.bytes_per_field_element);
    assert_eq!(c.bytes_per_cell, c.field_elements_per_cell * c.bytes_per_field_element);
}

#[test]
fn bls_sizes_match_the_specification() {
    // A compressed G1 point is 48 bytes, a compressed G2 point 96.
    let c = bls::constants();
    assert_eq!(c.bytes_per_pubkey, 48);
    assert_eq!(c.bytes_per_signature, 96);
}

#[test]
fn short_blob_is_rejected_by_lean() {
    // Mutation: a blob one byte short.
    //
    //     expected: 131072 bytes
    //     given   : 131071 bytes   → Lean's length check throws
    //
    // The bindings pass the length through, so the error comes from Lean, not from Rust.
    let blob = vec![0; kzg::constants().bytes_per_blob - 1];
    let err = kzg::blob_to_kzg_commitment(&blob).expect_err("a short blob is invalid");
    assert!(!err.message().is_empty(), "Lean names the failed check");
}

#[test]
fn empty_pubkey_list_is_rejected_by_lean() {
    // The sum of no public keys is undefined, so aggregation rejects it.
    let none: [&[u8]; 0] = [];
    assert!(bls::eth_aggregate_pubkeys(&none).is_err());
}

#[test]
fn infinity_signature_verifies_for_no_pubkeys() {
    // The one input for which an empty key list verifies: the G2 point at infinity.
    //
    //     0xc0 00 .. 00 (96 bytes) : compression and infinity flags set
    let mut infinity = vec![0; bls::constants().bytes_per_signature];
    infinity[0] = 0xc0;
    let none: [&[u8]; 0] = [];
    assert!(bls::eth_fast_aggregate_verify(&none, &[0; 32], &infinity));

    // The all-zero string is not a valid encoding, so it fails.
    let zero = vec![0; bls::constants().bytes_per_signature];
    assert!(!bls::eth_fast_aggregate_verify(&none, &[0; 32], &zero));
}

#[test]
fn calls_from_many_threads() {
    // Every thread registers with the Lean runtime on its first call.
    //
    //     thread 0..8 : allocate inputs, call Lean, release the result
    //
    // A thread that skipped registration would corrupt Lean's per-thread allocator.
    let handles: Vec<_> = (0..8)
        .map(|_| {
            thread::spawn(|| {
                let blob = vec![0xff; kzg::constants().bytes_per_blob];
                kzg::blob_to_kzg_commitment(&blob).is_err()
            })
        })
        .collect();
    for handle in handles {
        // A blob of 0xff bytes holds field elements above the modulus.
        assert!(handle.join().expect("no thread panics"));
    }
}

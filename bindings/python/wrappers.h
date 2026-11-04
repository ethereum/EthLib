/*
 * Shared declarations for the EthLib.Cryptography CPython extension.
 *
 * `module.c` defines `PyInit__native`, the method table, the spec-size
 * globals, and the marshalling helpers.
 */
#ifndef ETHCS_WRAPPERS_H
#define ETHCS_WRAPPERS_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

/* ---- Spec sizes (initialized in `PyInit__native`) -------------------- */

extern size_t BYTES_PER_PUBKEY;
extern size_t BYTES_PER_SIGNATURE;

extern size_t BYTES_PER_FIELD_ELEMENT;
extern size_t BYTES_PER_COMMITMENT;
extern size_t BYTES_PER_PROOF;
extern size_t FIELD_ELEMENTS_PER_BLOB;
extern size_t BYTES_PER_BLOB;
extern size_t FIELD_ELEMENTS_PER_CELL;
extern size_t BYTES_PER_CELL;
extern size_t CELLS_PER_EXT_BLOB;

extern size_t XMSS_MESSAGE_LEN;
extern size_t XMSS_SEED_LEN;
extern size_t XMSS_PUB_KEY_SIZE;
extern size_t XMSS_SIG_SIZE;

extern size_t SPHINCS_MESSAGE_LEN;
extern size_t SPHINCS_SEED_LEN;
extern size_t SPHINCS_PUB_KEY_SIZE;
extern size_t SPHINCS_SIG_SIZE;

extern size_t MODEXP_LENGTH_HEADER_BYTES;
extern size_t MODEXP_MAX_LENGTH_BYTES;

extern size_t RIPEMD160_OUTPUT_BYTES;
extern size_t SHA256_PRECOMPILE_OUTPUT_BYTES;
extern size_t SECP256K1_HASH_LEN;
extern size_t SECP256K1_SIGNATURE_LEN;
extern size_t SECP256R1_PUBLIC_KEY_LEN;
extern size_t SECP256R1_HASH_LEN;
extern size_t SECP256R1_SIGNATURE_LEN;

extern size_t ECRECOVER_GAS;

extern size_t ENR_MAX_RECORD_SIZE;
extern size_t REQRESP_MAX_ERROR_MESSAGE_SIZE;

/* ---- Lean ↔ C marshalling helpers ------------------------------------ */

lean_object*
mk_bytearray(
  const uint8_t* data,
  size_t len
);

lean_object*
mk_bytearray_array(
  const uint8_t* data,
  size_t n,
  size_t stride
);

/* Each export that can fail returns a Lean `Except (UInt32 × String) α`.
 *
 * The helpers below consume that result.
 *
 * On an error they raise `error_class` with the code and the message of the error. */

/* Copy the bytes of a successful result into `out`, which holds `out_len` bytes.
 *
 * Returns 0 on success, and 1 with a Python exception set otherwise. */
int
except_into_buffer(
  lean_object* result,
  PyObject* error_class,
  uint8_t* out,
  size_t out_len
);

/* Read the `UInt8` boolean of a successful result into `out_ok`.
 *
 * Returns 0 on success, and 1 with a Python exception set otherwise. */
int
except_into_flag(
  lean_object* result,
  PyObject* error_class,
  uint8_t* out_ok
);

/* Raise the error of a failed result as `error_class`, with its code and message.
 *
 * The result is freed. */
void
raise_lean_error(
  lean_object* result,
  PyObject* error_class
);

/* The bytes of a `ByteArray` that a total export returns, as a Python `bytes`.
 *
 * The `ByteArray` is freed. */
PyObject*
pybytes_of_bytearray(
  lean_object* bytes
);

/* The `ByteArray` of a successful result as a Python `bytes`, or NULL with an exception set. */
PyObject*
except_into_pybytes(
  lean_object* result,
  PyObject* error_class
);

/* The `UInt64` of a successful result as a Python `int`, or NULL with an exception set. */
PyObject*
except_into_pyint(
  lean_object* result,
  PyObject* error_class
);

/* The `UInt8` boolean of a successful result as a Python `bool`, or NULL with an exception set. */
PyObject*
except_into_pybool(
  lean_object* result,
  PyObject* error_class
);

/* ---- Exception classes (looked up in `PyInit__native`) --------------- */

/* One class of `ethlib.errors` per primitive. */
extern PyObject* KZG_ERROR;
extern PyObject* BLS_ERROR;
extern PyObject* XMSS_ERROR;
extern PyObject* SPHINCS_ERROR;
extern PyObject* SECP256K1_ERROR;
extern PyObject* SECP256R1_ERROR;
extern PyObject* ENR_ERROR;
extern PyObject* ECRECOVER_ERROR;
extern PyObject* MODEXP_ERROR;
extern PyObject* SHA256_PRECOMPILE_ERROR;
extern PyObject* PRECOMPILE_ERROR;
extern PyObject* STATE_ERROR;
extern PyObject* KECCAK_ERROR;
extern PyObject* REQRESP_ERROR;
extern PyObject* CONSENSUS_ERROR;
extern PyObject* HKDF_ERROR;
extern PyObject* AES_ERROR;
extern PyObject* CONCAT_KDF_ERROR;
extern PyObject* BLOCK_ERROR;
extern PyObject* RLP_ERROR;
extern PyObject* SNAPPY_ERROR;
extern PyObject* VARINT_ERROR;
extern PyObject* DISCV5_ERROR;
extern PyObject* RLPX_ERROR;
extern PyObject* DEVP2P_ERROR;
extern PyObject* TRANSACTION_ERROR;
extern PyObject* VRF_ERROR;
extern PyObject* TRIE_ERROR;
extern PyObject* EVM_ERROR;
extern PyObject* FEES_ERROR;

/* ---- Argument parsing helpers ---------------------------------------- */

/* A Python `int` in [0, 2^64), or -1 with an exception set. */
int
parse_uint64(
  PyObject* obj,
  const char* name,
  uint64_t* out
);

const uint8_t*
parse_bytes_of_size(
  PyObject* obj,
  Py_ssize_t expected,
  const char* name
);

uint8_t*
pack_bytes_sequence(
  PyObject* seq,
  Py_ssize_t stride,
  Py_ssize_t* out_len,
  const char* name
);

/* ---- Wrapper functions ----------------------------------------------- */

PyObject* py_eth_aggregate_pubkeys                        (PyObject* self, PyObject* args);
PyObject* py_eth_fast_aggregate_verify                    (PyObject* self, PyObject* args);
PyObject* py_bls_key_gen                                  (PyObject* self, PyObject* args);
PyObject* py_bls_sign                                     (PyObject* self, PyObject* args);
PyObject* py_bls_verify                                   (PyObject* self, PyObject* args);
PyObject* py_bls_aggregate                                (PyObject* self, PyObject* args);
PyObject* py_bls_aggregate_verify                         (PyObject* self, PyObject* args);
PyObject* py_bls_fast_aggregate_verify                    (PyObject* self, PyObject* args);
PyObject* py_bls_pop_prove                                (PyObject* self, PyObject* args);
PyObject* py_bls_pop_verify                               (PyObject* self, PyObject* args);
PyObject* py_bls_expand_message_xmd                       (PyObject* self, PyObject* args);
PyObject* py_bls_hash_to_g2                               (PyObject* self, PyObject* args);
PyObject* py_bls_pairing                                  (PyObject* self, PyObject* args);

PyObject* py_blob_to_kzg_commitment                       (PyObject* self, PyObject* args);
PyObject* py_compute_challenge                            (PyObject* self, PyObject* args);
PyObject* py_compute_kzg_proof                            (PyObject* self, PyObject* args);
PyObject* py_verify_kzg_proof                             (PyObject* self, PyObject* args);
PyObject* py_compute_blob_kzg_proof                       (PyObject* self, PyObject* args);
PyObject* py_verify_blob_kzg_proof                        (PyObject* self, PyObject* args);
PyObject* py_verify_blob_kzg_proof_batch                  (PyObject* self, PyObject* args);
PyObject* py_compute_cells                                (PyObject* self, PyObject* args);
PyObject* py_compute_cells_and_kzg_proofs                 (PyObject* self, PyObject* args);
PyObject* py_compute_verify_cell_kzg_proof_batch_challenge(PyObject* self, PyObject* args);
PyObject* py_verify_cell_kzg_proof_batch                  (PyObject* self, PyObject* args);
PyObject* py_recover_cells_and_kzg_proofs                 (PyObject* self, PyObject* args);

PyObject* py_xmss_key_gen                                 (PyObject* self, PyObject* args);
PyObject* py_xmss_sign                                    (PyObject* self, PyObject* args);
PyObject* py_xmss_verify                                  (PyObject* self, PyObject* args);
PyObject* py_xmss_signature_index                         (PyObject* self, PyObject* args);
PyObject* py_sphincs_key_gen                              (PyObject* self, PyObject* args);
PyObject* py_sphincs_sign                                 (PyObject* self, PyObject* args);
PyObject* py_sphincs_verify                               (PyObject* self, PyObject* args);
PyObject* py_modexp                                       (PyObject* self, PyObject* args);
PyObject* py_modexp_gas_cost                              (PyObject* self, PyObject* args);
PyObject* py_sha256                                       (PyObject* self, PyObject* args);
PyObject* py_keccak256                                    (PyObject* self, PyObject* args);
PyObject* py_keccak_f1600                                 (PyObject* self, PyObject* args);
PyObject* py_trie_root                                    (PyObject* self, PyObject* args);
PyObject* py_trie_verify_proof                            (PyObject* self, PyObject* args);
PyObject* py_trie_hex_prefix                              (PyObject* self, PyObject* args);
PyObject* py_vrf_verify                                   (PyObject* self, PyObject* args);
PyObject* py_vrf_secret                                   (PyObject* self, PyObject* args);
PyObject* py_vrf_evaluate                                 (PyObject* self, PyObject* args);
PyObject* py_crc32c                                      (PyObject* self, PyObject* args);
PyObject* py_aes_encrypt_block                            (PyObject* self, PyObject* args);
PyObject* py_aes_decrypt_block                            (PyObject* self, PyObject* args);
PyObject* py_aes_ctr                                      (PyObject* self, PyObject* args);
PyObject* py_aes_gcm_encrypt                              (PyObject* self, PyObject* args);
PyObject* py_aes_gcm_decrypt                              (PyObject* self, PyObject* args);
PyObject* py_hmac_sha256                                 (PyObject* self, PyObject* args);
PyObject* py_hkdf_sha256                                 (PyObject* self, PyObject* args);
PyObject* py_concat_kdf_sha256                           (PyObject* self, PyObject* args);
PyObject* py_ripemd160                                    (PyObject* self, PyObject* args);
PyObject* py_sha256_precompile                            (PyObject* self, PyObject* args);
PyObject* py_sha256_precompile_gas_cost                   (PyObject* self, PyObject* args);

PyObject* py_secp256k1_verify                             (PyObject* self, PyObject* args);
PyObject* py_secp256k1_is_low_s                           (PyObject* self, PyObject* args);
PyObject* py_secp256k1_recover                            (PyObject* self, PyObject* args);
PyObject* py_secp256k1_sign                               (PyObject* self, PyObject* args);
PyObject* py_secp256k1_ecdh                               (PyObject* self, PyObject* args);
PyObject* py_secp256k1_address                            (PyObject* self, PyObject* args);

PyObject* py_secp256r1_verify                             (PyObject* self, PyObject* args);

PyObject* py_ecrecover                                    (PyObject* self, PyObject* args);

PyObject* py_enr_from_text                                (PyObject* self, PyObject* args);
PyObject* py_enr_seq                                      (PyObject* self, PyObject* args);
PyObject* py_enr_verify_v4                                (PyObject* self, PyObject* args);
PyObject* py_enr_node_id                                  (PyObject* self, PyObject* args);
PyObject* py_enr_consensus_entries                        (PyObject* self, PyObject* args);

PyObject* py_discv5_log_distance                          (PyObject* self, PyObject* args);
PyObject* py_discv5_ecdh                                  (PyObject* self, PyObject* args);
PyObject* py_discv5_derive_keys                           (PyObject* self, PyObject* args);
PyObject* py_discv5_id_sign                               (PyObject* self, PyObject* args);
PyObject* py_discv5_id_verify                             (PyObject* self, PyObject* args);
PyObject* py_discv5_decode_packet                         (PyObject* self, PyObject* args);
PyObject* py_discv5_reencode_packet                       (PyObject* self, PyObject* args);
PyObject* py_discv5_encrypt_message                       (PyObject* self, PyObject* args);
PyObject* py_discv5_decrypt_message                       (PyObject* self, PyObject* args);
PyObject* py_discv5_decode_message                        (PyObject* self, PyObject* args);
PyObject* py_discv5_reencode_message                      (PyObject* self, PyObject* args);
PyObject* py_consensus_preset                             (PyObject* self, PyObject* args);
PyObject* py_consensus_config                             (PyObject* self, PyObject* args);
PyObject* py_consensus_parameters                         (PyObject* self, PyObject* args);
PyObject* py_consensus_get_custody_groups                 (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_columns_for_custody_group  (PyObject* self, PyObject* args);

PyObject* py_reqresp_max_compressed_len                   (PyObject* self, PyObject* args);
PyObject* py_reqresp_max_payload_size                     (PyObject* self, PyObject* args);
PyObject* py_reqresp_decode_payload                       (PyObject* self, PyObject* args);
PyObject* py_reqresp_decode_response_chunk                (PyObject* self, PyObject* args);
PyObject* py_block_header_hash                            (PyObject* self, PyObject* args);
PyObject* py_block_reencode                               (PyObject* self, PyObject* args);
PyObject* py_fees_base_fee_per_gas                        (PyObject* self, PyObject* args);
PyObject* py_fees_fake_exponential                        (PyObject* self, PyObject* args);
PyObject* py_fees_base_fee_per_blob_gas                   (PyObject* self, PyObject* args);
PyObject* py_fees_excess_blob_gas                         (PyObject* self, PyObject* args);
PyObject* py_evm_word_op                                  (PyObject* self, PyObject* args);
PyObject* py_evm_memory_gas_cost                          (PyObject* self, PyObject* args);
PyObject* py_evm_extend_memory_cost                       (PyObject* self, PyObject* args);
PyObject* py_evm_extend_memory_expand_by                  (PyObject* self, PyObject* args);
PyObject* py_rlp_encode                                   (PyObject* self, PyObject* args);
PyObject* py_rlp_decode                                   (PyObject* self, PyObject* args);
PyObject* py_rlp_decode_as                                (PyObject* self, PyObject* args);
PyObject* py_snappy_decompress                            (PyObject* self, PyObject* args);
PyObject* py_snappy_compress_literal                      (PyObject* self, PyObject* args);
PyObject* py_snappy_decode_frames                         (PyObject* self, PyObject* args);
PyObject* py_snappy_encode_frames_literal                 (PyObject* self, PyObject* args);
PyObject* py_snappy_masked_crc                            (PyObject* self, PyObject* args);
PyObject* py_varint_encode                                (PyObject* self, PyObject* args);
PyObject* py_varint_decode                                (PyObject* self, PyObject* args);
PyObject* py_gossip_message_id_phase0                     (PyObject* self, PyObject* args);
PyObject* py_gossip_message_id_altair                     (PyObject* self, PyObject* args);

PyObject* py_rlpx_ecies_encrypt                           (PyObject* self, PyObject* args);
PyObject* py_rlpx_ecies_decrypt                           (PyObject* self, PyObject* args);
PyObject* py_devp2p_decode_message                        (PyObject* self, PyObject* args);
PyObject* py_devp2p_encode_message                        (PyObject* self, PyObject* args);
PyObject* py_receipt_reencode                             (PyObject* self, PyObject* args);
PyObject* py_receipt_logs_bloom                           (PyObject* self, PyObject* args);
PyObject* py_tx_type                                      (PyObject* self, PyObject* args);
PyObject* py_tx_hash                                      (PyObject* self, PyObject* args);
PyObject* py_tx_recover_sender                            (PyObject* self, PyObject* args);
PyObject* py_tx_intrinsic_gas                             (PyObject* self, PyObject* args);
PyObject* py_tx_check                                     (PyObject* self, PyObject* args);
PyObject* py_rlpx_make_auth                               (PyObject* self, PyObject* args);
PyObject* py_rlpx_respond                                 (PyObject* self, PyObject* args);
PyObject* py_rlpx_recipient_secrets                       (PyObject* self, PyObject* args);
PyObject* py_rlpx_finish                                  (PyObject* self, PyObject* args);
PyObject* py_block_validate_header                        (PyObject* self, PyObject* args);

PyObject* py_precompile_run                               (PyObject* self, PyObject* args);

PyObject* py_state_root                                   (PyObject* self, PyObject* args);

#endif /* ETHCS_WRAPPERS_H */

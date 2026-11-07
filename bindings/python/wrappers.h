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


extern size_t SECP256K1_HASH_LEN;
extern size_t SECP256K1_SIGNATURE_LEN;
extern size_t SECP256R1_PUBLIC_KEY_LEN;
extern size_t SECP256R1_HASH_LEN;
extern size_t SECP256R1_SIGNATURE_LEN;


extern size_t ENR_MAX_RECORD_SIZE;
extern size_t REQRESP_MAX_PAYLOAD_SIZE;
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

/* The `Array ByteArray` of a successful result as a Python `list` of `bytes`.
 *
 * On an error it returns NULL with an exception set. */
PyObject*
except_into_pybytes_list(
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
extern PyObject* PRECOMPILE_ERROR;
extern PyObject* STATE_ERROR;
extern PyObject* KECCAK_ERROR;
extern PyObject* ETHASH_ERROR;
extern PyObject* REQRESP_ERROR;
extern PyObject* CONSENSUS_ERROR;
extern PyObject* HKDF_ERROR;
extern PyObject* AES_ERROR;
extern PyObject* CONCAT_KDF_ERROR;
extern PyObject* BLOCK_ERROR;
extern PyObject* RLP_ERROR;
extern PyObject* SSZ_ERROR;
extern PyObject* SNAPPY_ERROR;
extern PyObject* VARINT_ERROR;
extern PyObject* GOSSIP_ERROR;
extern PyObject* DISCV5_ERROR;
extern PyObject* RLPX_ERROR;
extern PyObject* DEVP2P_ERROR;
extern PyObject* DISCV4_ERROR;
extern PyObject* FORK_ID_ERROR;
extern PyObject* ETH_WIRE_ERROR;
extern PyObject* SNAP_ERROR;
extern PyObject* TRANSACTION_ERROR;
extern PyObject* VRF_ERROR;
extern PyObject* TRIE_ERROR;
extern PyObject* EVM_ERROR;
extern PyObject* FEES_ERROR;
extern PyObject* ENGINE_ERROR;
extern PyObject* TRANSITION_ERROR;
extern PyObject* LIGHT_CLIENT_ERROR;
extern PyObject* FORK_CHOICE_ERROR;
extern PyObject* CHAIN_ERROR;
extern PyObject* WEAK_SUBJECTIVITY_ERROR;
extern PyObject* VALIDATOR_DUTY_ERROR;
extern PyObject* PROPOSER_ERROR;
extern PyObject* SLASHING_PROTECTION_ERROR;

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

/* Read a sequence of `bytes` of any lengths into a Lean `Array ByteArray`.
 * Returns 0, or 1 with a Python exception set. */
int
parse_bytes_sequence(
  PyObject* seq,
  const char* name,
  lean_object** out
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
PyObject* py_bls_decode_g1                                (PyObject* self, PyObject* args);
PyObject* py_bls_decode_g2                                (PyObject* self, PyObject* args);
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
PyObject* py_sha256                                       (PyObject* self, PyObject* args);
PyObject* py_keccak256                                    (PyObject* self, PyObject* args);
PyObject* py_keccak512                                    (PyObject* self, PyObject* args);
PyObject* py_ethash_cache_size                            (PyObject* self, PyObject* args);
PyObject* py_ethash_dataset_size                          (PyObject* self, PyObject* args);
PyObject* py_ethash_seed                                  (PyObject* self, PyObject* args);
PyObject* py_ethash_cache                                 (PyObject* self, PyObject* args);
PyObject* py_ethash_dataset_item                          (PyObject* self, PyObject* args);
PyObject* py_ethash_hashimoto_light                       (PyObject* self, PyObject* args);
PyObject* py_keccak_f1600                                 (PyObject* self, PyObject* args);
PyObject* py_trie_root                                    (PyObject* self, PyObject* args);
PyObject* py_trie_verify_proof                            (PyObject* self, PyObject* args);
PyObject* py_trie_hex_prefix                              (PyObject* self, PyObject* args);
PyObject* py_trie_verify_account_proof                    (PyObject* self, PyObject* args);
PyObject* py_vrf_verify                                   (PyObject* self, PyObject* args);
PyObject* py_vrf_secret                                   (PyObject* self, PyObject* args);
PyObject* py_vrf_evaluate                                 (PyObject* self, PyObject* args);
PyObject* py_crc32                                       (PyObject* self, PyObject* args);
PyObject* py_crc32c                                      (PyObject* self, PyObject* args);
PyObject* py_aes_encrypt_block                            (PyObject* self, PyObject* args);
PyObject* py_aes_decrypt_block                            (PyObject* self, PyObject* args);
PyObject* py_aes_ctr                                      (PyObject* self, PyObject* args);
PyObject* py_aes_gcm_encrypt                              (PyObject* self, PyObject* args);
PyObject* py_aes_gcm_decrypt                              (PyObject* self, PyObject* args);
PyObject* py_hmac_sha256                                 (PyObject* self, PyObject* args);
PyObject* py_hkdf_sha256                                 (PyObject* self, PyObject* args);
PyObject* py_concat_kdf_sha256                           (PyObject* self, PyObject* args);

PyObject* py_secp256k1_verify                             (PyObject* self, PyObject* args);
PyObject* py_secp256k1_is_low_s                           (PyObject* self, PyObject* args);
PyObject* py_secp256k1_recover                            (PyObject* self, PyObject* args);
PyObject* py_secp256k1_sign                               (PyObject* self, PyObject* args);
PyObject* py_secp256k1_ecdh                               (PyObject* self, PyObject* args);
PyObject* py_secp256k1_address                            (PyObject* self, PyObject* args);

PyObject* py_secp256r1_verify                             (PyObject* self, PyObject* args);


PyObject* py_enr_from_text                                (PyObject* self, PyObject* args);
PyObject* py_enr_seq                                      (PyObject* self, PyObject* args);
PyObject* py_enr_verify_v4                                (PyObject* self, PyObject* args);
PyObject* py_enr_node_id                                  (PyObject* self, PyObject* args);
PyObject* py_enr_sign_v4                                  (PyObject* self, PyObject* args);
PyObject* py_enr_make_record_v4                           (PyObject* self, PyObject* args);
PyObject* py_enr_eth_fork_id                              (PyObject* self, PyObject* args);
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
PyObject* py_discv5_make_whoareyou                        (PyObject* self, PyObject* args);
PyObject* py_discv5_read_whoareyou                        (PyObject* self, PyObject* args);
PyObject* py_discv5_seal_message                          (PyObject* self, PyObject* args);
PyObject* py_discv5_open_message                          (PyObject* self, PyObject* args);
PyObject* py_discv5_seal_handshake                        (PyObject* self, PyObject* args);
PyObject* py_discv5_open_handshake                        (PyObject* self, PyObject* args);
PyObject* py_consensus_preset                             (PyObject* self, PyObject* args);
PyObject* py_consensus_config                             (PyObject* self, PyObject* args);
PyObject* py_consensus_parameters                         (PyObject* self, PyObject* args);
PyObject* py_consensus_get_custody_groups                 (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_columns_for_custody_group  (PyObject* self, PyObject* args);
PyObject* py_consensus_ssz_static                         (PyObject* self, PyObject* args);
PyObject* py_consensus_merkle_proof                       (PyObject* self, PyObject* args);
PyObject* py_consensus_verify_blob_sidecar_inclusion_proof (PyObject* self, PyObject* args);
PyObject* py_consensus_process_operation (PyObject* self, PyObject* args);
PyObject* py_consensus_upgrade_state (PyObject* self, PyObject* args);
PyObject* py_consensus_process_epoch (PyObject* self, PyObject* args);
PyObject* py_consensus_rewards_deltas (PyObject* self, PyObject* args);
PyObject* py_consensus_rewards_deltas_batch (PyObject* self, PyObject* args);
PyObject* py_consensus_process_slots (PyObject* self, PyObject* args);
PyObject* py_consensus_state_transition (PyObject* self, PyObject* args);
PyObject* py_consensus_state_transition_across (PyObject* self, PyObject* args);
PyObject* py_consensus_state_transitions (PyObject* self, PyObject* args);
PyObject* py_consensus_state_transitions_across (PyObject* self, PyObject* args);
PyObject* py_consensus_fork_choice (PyObject* self, PyObject* args);
PyObject* py_consensus_gossip_validation (PyObject* self, PyObject* args);
PyObject* py_consensus_initialize_genesis (PyObject* self, PyObject* args);
PyObject* py_consensus_is_valid_genesis_state (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_weak_subjectivity_period (PyObject* self, PyObject* args);
PyObject* py_consensus_is_within_weak_subjectivity_period (PyObject* self, PyObject* args);
PyObject* py_consensus_get_committee_assignment (PyObject* self, PyObject* args);
PyObject* py_consensus_is_proposer (PyObject* self, PyObject* args);
PyObject* py_consensus_is_assigned_to_sync_committee (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_subnets_for_sync_committee (PyObject* self, PyObject* args);
PyObject* py_consensus_get_ptc_assignment (PyObject* self, PyObject* args);
PyObject* py_consensus_get_upcoming_proposal_slots (PyObject* self, PyObject* args);
PyObject* py_consensus_get_validator_signature (PyObject* self, PyObject* args);
PyObject* py_consensus_get_eth1_vote (PyObject* self, PyObject* args);
PyObject* py_consensus_is_execution_block (PyObject* self, PyObject* args);
PyObject* py_consensus_is_optimistic_candidate_block (PyObject* self, PyObject* args);
PyObject* py_consensus_latest_verified_ancestor (PyObject* self, PyObject* args);
PyObject* py_consensus_on_valid_payload (PyObject* self, PyObject* args);
PyObject* py_consensus_on_invalidated_payload (PyObject* self, PyObject* args);
PyObject* py_consensus_is_optimistic_restricted_domain (PyObject* self, PyObject* args);
PyObject* py_consensus_read_slashing_interchange (PyObject* self, PyObject* args);
PyObject* py_consensus_import_slashing_interchange (PyObject* self, PyObject* args);
PyObject* py_consensus_check_block_signing (PyObject* self, PyObject* args);
PyObject* py_consensus_check_attestation_signing (PyObject* self, PyObject* args);
PyObject* py_consensus_record_block_signing (PyObject* self, PyObject* args);
PyObject* py_consensus_record_attestation_signing (PyObject* self, PyObject* args);
PyObject* py_consensus_get_attestation_data (PyObject* self, PyObject* args);
PyObject* py_consensus_get_aggregate_signature (PyObject* self, PyObject* args);
PyObject* py_consensus_construct_attestation (PyObject* self, PyObject* args);
PyObject* py_consensus_construct_single_attestation (PyObject* self, PyObject* args);
PyObject* py_consensus_construct_aggregate (PyObject* self, PyObject* args);
PyObject* py_consensus_construct_aggregate_of_single_attestations (PyObject* self, PyObject* args);
PyObject* py_consensus_construct_sync_committee_contribution (PyObject* self, PyObject* args);
PyObject* py_consensus_process_sync_committee_contributions (PyObject* self, PyObject* args);
PyObject* py_consensus_get_eth1_pending_deposit_count (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_new_state_root (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_on_chain_aggregate (PyObject* self, PyObject* args);
PyObject* py_consensus_get_execution_requests (PyObject* self, PyObject* args);
PyObject* py_consensus_get_validators_custody_requirement (PyObject* self, PyObject* args);
PyObject* py_pq_keys_ssz                                  (PyObject* self, PyObject* args);
PyObject* py_pq_keys_possession_signing_root              (PyObject* self, PyObject* args);
PyObject* py_pq_keys_is_valid_possession_proof            (PyObject* self, PyObject* args);
PyObject* py_consensus_verify_data_column_sidecar         (PyObject* self, PyObject* args);
PyObject* py_consensus_verify_data_column_sidecar_inclusion_proof(PyObject* self, PyObject* args);
PyObject* py_consensus_verify_data_column_sidecar_kzg_proofs(PyObject* self, PyObject* args);
PyObject* py_consensus_verify_partial_data_column_header_inclusion_proof(PyObject* self, PyObject* args);
PyObject* py_consensus_verify_partial_data_column_sidecar_kzg_proofs(PyObject* self, PyObject* args);
PyObject* py_consensus_compute_matrix                     (PyObject* self, PyObject* args);
PyObject* py_consensus_recover_matrix                     (PyObject* self, PyObject* args);
PyObject* py_consensus_light_client_sync                 (PyObject* self, PyObject* args);
PyObject* py_consensus_is_better_update                  (PyObject* self, PyObject* args);
PyObject* py_consensus_genesis_block                     (PyObject* self, PyObject* args);
PyObject* py_consensus_create_light_client_bootstrap     (PyObject* self, PyObject* args);
PyObject* py_consensus_create_light_client_update        (PyObject* self, PyObject* args);
PyObject* py_consensus_block_to_light_client_header      (PyObject* self, PyObject* args);
PyObject* py_consensus_light_client_update_proofs        (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_fork_digest               (PyObject* self, PyObject* args);
PyObject* py_consensus_get_data_column_sidecars_from_block(PyObject* self, PyObject* args);
PyObject* py_consensus_get_data_column_sidecars_from_column_sidecar(PyObject* self, PyObject* args);
PyObject* py_consensus_compute_shuffled_permutation      (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_shuffled_index            (PyObject* self, PyObject* args);
PyObject* py_consensus_reqresp_protocol_ids               (PyObject* self, PyObject* args);
PyObject* py_consensus_reqresp_parse_protocol_id          (PyObject* self, PyObject* args);
PyObject* py_consensus_reqresp_message                    (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_min_epochs_for_block_requests(PyObject* self, PyObject* args);
PyObject* py_consensus_gossip_topics                      (PyObject* self, PyObject* args);
PyObject* py_consensus_reqresp_request_bounds             (PyObject* self, PyObject* args);
PyObject* py_consensus_reqresp_response_bounds            (PyObject* self, PyObject* args);
PyObject* py_consensus_gossip_topic_bound                 (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_subnet_for_attestation     (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_subnet_for_blob_sidecar    (PyObject* self, PyObject* args);
PyObject* py_consensus_compute_subnet_for_data_column_sidecar(PyObject* self, PyObject* args);
PyObject* py_consensus_compute_subscribed_subnets         (PyObject* self, PyObject* args);

PyObject* py_reqresp_max_compressed_len                   (PyObject* self, PyObject* args);
PyObject* py_reqresp_decode_payload                       (PyObject* self, PyObject* args);
PyObject* py_reqresp_decode_response_chunk                (PyObject* self, PyObject* args);
PyObject* py_block_header_hash                            (PyObject* self, PyObject* args);
PyObject* py_block_reencode                               (PyObject* self, PyObject* args);
PyObject* py_pow_block_difficulty                         (PyObject* self, PyObject* args);
PyObject* py_pow_seal_hash                                (PyObject* self, PyObject* args);
PyObject* py_pow_check                                    (PyObject* self, PyObject* args);
PyObject* py_pow_validate_ommers                          (PyObject* self, PyObject* args);
PyObject* py_block_transactions_root                      (PyObject* self, PyObject* args);
PyObject* py_block_withdrawals_root                       (PyObject* self, PyObject* args);
PyObject* py_block_deposit_requests                       (PyObject* self, PyObject* args);
PyObject* py_block_requests_hash                          (PyObject* self, PyObject* args);
PyObject* py_block_access_list_hash                       (PyObject* self, PyObject* args);
PyObject* py_block_access_list_check                      (PyObject* self, PyObject* args);
PyObject* py_block_validate_size                          (PyObject* self, PyObject* args);
PyObject* py_fees_base_fee_per_gas                        (PyObject* self, PyObject* args);
PyObject* py_fees_fake_exponential                        (PyObject* self, PyObject* args);
PyObject* py_fees_base_fee_per_blob_gas                   (PyObject* self, PyObject* args);
PyObject* py_fees_excess_blob_gas                         (PyObject* self, PyObject* args);
PyObject* py_fees_blob_data_fee                           (PyObject* self, PyObject* args);
PyObject* py_evm_word_op                                  (PyObject* self, PyObject* args);
PyObject* py_evm_immediate_depths                         (PyObject* self, PyObject* args);
PyObject* py_evm_memory_gas_cost                          (PyObject* self, PyObject* args);
PyObject* py_evm_extend_memory_cost                       (PyObject* self, PyObject* args);
PyObject* py_evm_extend_memory_expand_by                  (PyObject* self, PyObject* args);
PyObject* py_evm_create_address                           (PyObject* self, PyObject* args);
PyObject* py_evm_create2_address                          (PyObject* self, PyObject* args);
PyObject* py_rlp_encode                                   (PyObject* self, PyObject* args);
PyObject* py_rlp_decode                                   (PyObject* self, PyObject* args);
PyObject* py_rlp_decode_as                                (PyObject* self, PyObject* args);
PyObject* py_ssz_serialize                                (PyObject* self, PyObject* args);
PyObject* py_ssz_deserialize                              (PyObject* self, PyObject* args);
PyObject* py_ssz_hash_tree_root                           (PyObject* self, PyObject* args);
PyObject* py_snappy_decompress                            (PyObject* self, PyObject* args);
PyObject* py_snappy_compress                              (PyObject* self, PyObject* args);
PyObject* py_snappy_decode_frames                         (PyObject* self, PyObject* args);
PyObject* py_snappy_encode_frames_literal                 (PyObject* self, PyObject* args);
PyObject* py_snappy_encode_frames                         (PyObject* self, PyObject* args);
PyObject* py_snappy_masked_crc                            (PyObject* self, PyObject* args);
PyObject* py_varint_encode                                (PyObject* self, PyObject* args);
PyObject* py_varint_decode                                (PyObject* self, PyObject* args);
PyObject* py_gossip_message_id                            (PyObject* self, PyObject* args);
PyObject* py_gossip_decode_payload                        (PyObject* self, PyObject* args);

PyObject* py_rlpx_ecies_encrypt                           (PyObject* self, PyObject* args);
PyObject* py_rlpx_ecies_decrypt                           (PyObject* self, PyObject* args);
PyObject* py_devp2p_decode_message                        (PyObject* self, PyObject* args);
PyObject* py_devp2p_encode_message                        (PyObject* self, PyObject* args);
PyObject* py_discv4_decode                                (PyObject* self, PyObject* args);
PyObject* py_discv4_encode                                (PyObject* self, PyObject* args);
PyObject* py_discv4_record_signed_by                      (PyObject* self, PyObject* args);
PyObject* py_fork_id                                      (PyObject* self, PyObject* args);
PyObject* py_mainnet_fork_id                              (PyObject* self, PyObject* args);
PyObject* py_fork_id_validate                             (PyObject* self, PyObject* args);
PyObject* py_eth_message_decode                           (PyObject* self, PyObject* args);
PyObject* py_eth_check_status                             (PyObject* self, PyObject* args);
PyObject* py_eth_check_headers                            (PyObject* self, PyObject* args);
PyObject* py_eth_check_pooled                             (PyObject* self, PyObject* args);
PyObject* py_eth_wire_hash                                (PyObject* self, PyObject* args);
PyObject* py_eth_receipts_match                           (PyObject* self, PyObject* args);
PyObject* py_eth_access_lists_answer                      (PyObject* self, PyObject* args);
PyObject* py_eth_check_partial_receipts                   (PyObject* self, PyObject* args);
PyObject* py_snap_message_decode                          (PyObject* self, PyObject* args);
PyObject* py_snap_codes_answer                            (PyObject* self, PyObject* args);
PyObject* py_snap_access_lists_answer                     (PyObject* self, PyObject* args);
PyObject* py_snap_full_account                            (PyObject* self, PyObject* args);
PyObject* py_receipt_reencode                             (PyObject* self, PyObject* args);
PyObject* py_receipt_logs_bloom                           (PyObject* self, PyObject* args);
PyObject* py_block_make_receipts                          (PyObject* self, PyObject* args);
PyObject* py_tx_type                                      (PyObject* self, PyObject* args);
PyObject* py_tx_hash                                      (PyObject* self, PyObject* args);
PyObject* py_tx_recover_sender                            (PyObject* self, PyObject* args);
PyObject* py_tx_intrinsic_gas                             (PyObject* self, PyObject* args);
PyObject* py_tx_check                                     (PyObject* self, PyObject* args);
PyObject* py_tx_check_in_block                           (PyObject* self, PyObject* args);
PyObject* py_tx_run                                      (PyObject* self, PyObject* args);
PyObject* py_tx_settle                                    (PyObject* self, PyObject* args);
PyObject* py_tx_network_check                             (PyObject* self, PyObject* args);
PyObject* py_rlpx_make_auth                               (PyObject* self, PyObject* args);
PyObject* py_rlpx_respond                                 (PyObject* self, PyObject* args);
PyObject* py_rlpx_recipient_secrets                       (PyObject* self, PyObject* args);
PyObject* py_rlpx_finish                                  (PyObject* self, PyObject* args);
PyObject* py_rlpx_write_frames                            (PyObject* self, PyObject* args);
PyObject* py_rlpx_read_frames                             (PyObject* self, PyObject* args);
PyObject* py_block_validate_header                        (PyObject* self, PyObject* args);
PyObject* py_block_check_header                           (PyObject* self, PyObject* args);
PyObject* py_block_dao_extra_data_valid                   (PyObject* self, PyObject* args);
PyObject* py_state_transition                             (PyObject* self, PyObject* args);
PyObject* py_genesis_block                                (PyObject* self, PyObject* args);

PyObject* py_precompile_run                               (PyObject* self, PyObject* args);
PyObject* py_precompile_price                             (PyObject* self, PyObject* args);

PyObject* py_state_root                                   (PyObject* self, PyObject* args);
PyObject* py_state_withdrawals_root                       (PyObject* self, PyObject* args);
PyObject* py_state_dao_fork_root                         (PyObject* self, PyObject* args);
PyObject* py_state_rewards_root                           (PyObject* self, PyObject* args);

PyObject* py_mainnet_active_fork                          (PyObject* self, PyObject* args);
PyObject* py_hoodi_active_fork                            (PyObject* self, PyObject* args);
PyObject* py_active_fork                                  (PyObject* self, PyObject* args);

PyObject* py_engine_new_payload                          (PyObject* self, PyObject* args);
PyObject* py_engine_new_payload_on_chain                 (PyObject* self, PyObject* args);
PyObject* py_engine_forkchoice_updated                   (PyObject* self, PyObject* args);
PyObject* py_engine_prepare_execution_payload            (PyObject* self, PyObject* args);
PyObject* py_engine_prepare_execution_payload_gloas      (PyObject* self, PyObject* args);

#endif /* ETHCS_WRAPPERS_H */

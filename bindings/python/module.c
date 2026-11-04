/*
 * CPython extension entry point. Boots the Lean runtime, wires up the
 * spec-preset size constants, and assembles the method table from the
 * per-domain wrappers.
 */
#include "wrappers.h"
#include "docstrings.h"

/* ---- Spec sizes (populated in `PyInit__native`) ---------------------- */

size_t BYTES_PER_PUBKEY;
size_t BYTES_PER_SIGNATURE;

size_t BYTES_PER_FIELD_ELEMENT;
size_t BYTES_PER_COMMITMENT;
size_t BYTES_PER_PROOF;
size_t FIELD_ELEMENTS_PER_BLOB;
size_t BYTES_PER_BLOB;
size_t FIELD_ELEMENTS_PER_CELL;
size_t BYTES_PER_CELL;
size_t CELLS_PER_EXT_BLOB;

size_t XMSS_MESSAGE_LEN;
size_t XMSS_SEED_LEN;
size_t XMSS_PUB_KEY_SIZE;
size_t XMSS_SIG_SIZE;

size_t SPHINCS_MESSAGE_LEN;
size_t SPHINCS_SEED_LEN;
size_t SPHINCS_PUB_KEY_SIZE;
size_t SPHINCS_SIG_SIZE;

size_t MODEXP_LENGTH_HEADER_BYTES;
size_t MODEXP_MAX_LENGTH_BYTES;
size_t RIPEMD160_OUTPUT_BYTES;
size_t SHA256_PRECOMPILE_OUTPUT_BYTES;

size_t ENR_MAX_RECORD_SIZE;
size_t REQRESP_MAX_PAYLOAD_SIZE;
size_t REQRESP_MAX_ERROR_MESSAGE_SIZE;
size_t SECP256K1_HASH_LEN;
size_t SECP256K1_SIGNATURE_LEN;

size_t SECP256R1_PUBLIC_KEY_LEN;
size_t SECP256R1_HASH_LEN;
size_t SECP256R1_SIGNATURE_LEN;

size_t ECRECOVER_GAS;

/* ---- Exception classes (looked up in `PyInit__native`) --------------- */

PyObject* KZG_ERROR;
PyObject* BLS_ERROR;
PyObject* XMSS_ERROR;
PyObject* SPHINCS_ERROR;
PyObject* SECP256K1_ERROR;
PyObject* SECP256R1_ERROR;
PyObject* ENR_ERROR;
PyObject* ECRECOVER_ERROR;
PyObject* MODEXP_ERROR;
PyObject* SHA256_PRECOMPILE_ERROR;
PyObject* PRECOMPILE_ERROR;
PyObject* STATE_ERROR;
PyObject* KECCAK_ERROR;
PyObject* REQRESP_ERROR;
PyObject* CONSENSUS_ERROR;
PyObject* HKDF_ERROR;
PyObject* AES_ERROR;
PyObject* CONCAT_KDF_ERROR;
PyObject* BLOCK_ERROR;
PyObject* RLP_ERROR;
PyObject* SSZ_ERROR;
PyObject* SNAPPY_ERROR;
PyObject* VARINT_ERROR;
PyObject* DISCV5_ERROR;
PyObject* RLPX_ERROR;
PyObject* DEVP2P_ERROR;
PyObject* DISCV4_ERROR;
PyObject* TRANSACTION_ERROR;
PyObject* VRF_ERROR;
PyObject* TRIE_ERROR;
PyObject* EVM_ERROR;
PyObject* FEES_ERROR;

/* ---- Lean externs: size accessors ------------------------------------ */

extern uint64_t
eth_bls_const_bytes_per_pubkey(
  lean_object* unit
);

extern uint64_t
eth_bls_const_bytes_per_signature(
  lean_object* unit
);

extern uint64_t
eth_kzg_const_bytes_per_field_element(
  lean_object* unit
);

extern uint64_t
eth_kzg_const_bytes_per_commitment(
  lean_object* unit
);

extern uint64_t
eth_kzg_const_bytes_per_proof(
  lean_object* unit
);

extern uint64_t
eth_kzg_const_field_elements_per_blob(
  lean_object* unit
);

extern uint64_t
eth_kzg_const_bytes_per_blob(
  lean_object* unit
);

extern uint64_t
eth_kzg_const_field_elements_per_cell(
  lean_object* unit
);

extern uint64_t
eth_kzg_const_bytes_per_cell(
  lean_object* unit
);

extern uint64_t
eth_kzg_const_cells_per_ext_blob(
  lean_object* unit
);

extern uint64_t
eth_xmss_const_message_len(
  lean_object* unit
);

extern uint64_t
eth_xmss_const_seed_len(
  lean_object* unit
);

extern uint64_t
eth_xmss_const_pub_key_size(
  lean_object* unit
);

extern uint64_t
eth_xmss_const_sig_size(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_message_len(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_seed_len(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_pub_key_size(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_sig_size(
  lean_object* unit
);

extern uint64_t
eth_modexp_const_length_header_bytes(
  lean_object* unit
);

extern uint64_t
eth_modexp_const_max_length_bytes(
  lean_object* unit
);

extern uint64_t
eth_ripemd160_const_output_bytes(
  lean_object* unit
);

extern uint64_t
eth_sha256_precompile_const_output_bytes(
  lean_object* unit
);

extern uint64_t
eth_secp256k1_const_hash_len(
  lean_object* unit
);

extern uint64_t
eth_secp256k1_const_signature_len(
  lean_object* unit
);

extern uint64_t
eth_secp256r1_const_public_key_len(
  lean_object* unit
);

extern uint64_t
eth_secp256r1_const_hash_len(
  lean_object* unit
);

extern uint64_t
eth_secp256r1_const_signature_len(
  lean_object* unit
);

extern uint64_t
eth_ecrecover_const_gas(
  lean_object* unit
);

extern uint64_t
eth_enr_const_max_record_size(
  lean_object* unit
);

extern uint64_t
eth_reqresp_const_max_payload_size(
  lean_object* unit
);

extern uint64_t
eth_reqresp_const_max_error_message_size(
  lean_object* unit
);

/* ---- Lean externs: runtime + module init ----------------------------- */

extern void
lean_initialize_runtime_module(void);

/* We boot the export root of each domain, not the library root `EthLib.Exports`.
 *
 * Lake writes a `.c` file for the library root but never compiles it.
 *
 * So the init symbol of the library root is never linked in.
 *
 * The init of a module runs the init of everything it imports.
 *
 * So booting the export roots boots the specification too. */
extern lean_object*
initialize_EthLib_EthLib_Cryptography_Exports(
  uint8_t builtin
);

extern lean_object*
initialize_EthLib_EthLib_Networking_Exports(
  uint8_t builtin
);

extern lean_object*
initialize_EthLib_EthLib_Execution_Exports(
  uint8_t builtin
);

extern lean_object*
initialize_EthLib_EthLib_Consensus_Exports(
  uint8_t builtin
);

extern lean_object*
initialize_EthLib_EthLib_Serialization_Exports(
  uint8_t builtin
);

extern lean_object*
initialize_EthLib_EthLib_Base_Exports_ChainConfig(
  uint8_t builtin
);

/*
 * Note on linker hygiene:
 *   `lean_initialize()` and `initialize_Lean` live in libleancpp.a's
 *   `init.cpp.o`, which references most of the Lean *compiler* and
 *   would drag in the 224MB `libLean.a`. We avoid them by calling only
 *   `lean_initialize_runtime_module()` (from libleanrt.a, which is the
 *   minimal runtime: GC, allocator, IO primitives) plus our package's
 *   per-module init `initialize_EthLib_*`. Together that's
 *   enough to run any code we'd actually call from Python.
 */

/* ---- Lean ↔ C marshalling helpers ------------------------------------ */

lean_object*
mk_bytearray(
  const uint8_t* data,
  size_t len
) {
  lean_object* arr = lean_alloc_sarray(1, len, len);
  memcpy(lean_sarray_cptr(arr), data, len);
  return arr;
}

lean_object*
mk_bytearray_array(
  const uint8_t* data,
  size_t n,
  size_t stride
) {
  lean_object* arr = lean_alloc_array(n, n);
  for (size_t i = 0; i < n; i++) {
    lean_array_set_core(arr, i, mk_bytearray(data + i * stride, stride));
  }
  return arr;
}

/* Raise the error of a failed result, and free the result.
 *
 * The error is the pair of a `UInt32` code and a `String` message.
 *
 * `Prod` is polymorphic, so the code is boxed. */
void
raise_lean_error(
  lean_object* result,
  PyObject* error_class
) {
  lean_object* pair = lean_ctor_get(result, 0);
  uint32_t code = lean_unbox_uint32(lean_ctor_get(pair, 0));
  const char* message = lean_string_cstr(lean_ctor_get(pair, 1));
  PyObject* exc = PyObject_CallFunction(error_class, "Is", (unsigned int) code, message);
  if (exc) {
    PyErr_SetObject(error_class, exc);
    Py_DECREF(exc);
  }
  lean_dec(result);
}

/* `Except.error` is the first constructor of `Except`, so its tag is 0. */
static int
is_error(
  lean_object* result
) {
  return lean_obj_tag(result) == 0;
}

/* The value of `Except.ok` is borrowed, so only the result is freed. */
int
except_into_buffer(
  lean_object* result,
  PyObject* error_class,
  uint8_t* out,
  size_t out_len
) {
  if (is_error(result)) {
    raise_lean_error(result, error_class);
    return 1;
  }
  lean_object* ba = lean_ctor_get(result, 0);
  size_t got = lean_sarray_size(ba);
  if (got != out_len) {
    lean_dec(result);
    PyErr_Format(PyExc_RuntimeError, "Lean returned %zu bytes, expected %zu", got, out_len);
    return 1;
  }
  memcpy(out, lean_sarray_cptr(ba), out_len);
  lean_dec(result);
  return 0;
}

int
except_into_flag(
  lean_object* result,
  PyObject* error_class,
  uint8_t* out_ok
) {
  if (is_error(result)) {
    raise_lean_error(result, error_class);
    return 1;
  }
  *out_ok = (uint8_t) lean_unbox(lean_ctor_get(result, 0));
  lean_dec(result);
  return 0;
}

PyObject*
pybytes_of_bytearray(
  lean_object* bytes
) {
  PyObject* out = PyBytes_FromStringAndSize(
    (const char*) lean_sarray_cptr(bytes), (Py_ssize_t) lean_sarray_size(bytes));
  lean_dec(bytes);
  return out;
}

PyObject*
except_into_pybytes(
  lean_object* result,
  PyObject* error_class
) {
  if (is_error(result)) {
    raise_lean_error(result, error_class);
    return NULL;
  }
  lean_object* ba = lean_ctor_get(result, 0);
  PyObject* out = PyBytes_FromStringAndSize(
    (const char*) lean_sarray_cptr(ba), (Py_ssize_t) lean_sarray_size(ba));
  lean_dec(result);
  return out;
}

PyObject*
except_into_pyint(
  lean_object* result,
  PyObject* error_class
) {
  if (is_error(result)) {
    raise_lean_error(result, error_class);
    return NULL;
  }
  uint64_t value = lean_unbox_uint64(lean_ctor_get(result, 0));
  lean_dec(result);
  return PyLong_FromUnsignedLongLong(value);
}

PyObject*
except_into_pybool(
  lean_object* result,
  PyObject* error_class
) {
  uint8_t ok;
  if (except_into_flag(result, error_class, &ok)) return NULL;
  if (ok) Py_RETURN_TRUE; else Py_RETURN_FALSE;
}

/* ---- Argument parsing helpers ---------------------------------------- */

/* A Python `int` in [0, 2^64), or -1 with an exception set. */
int
parse_uint64(
  PyObject* obj,
  const char* name,
  uint64_t* out
) {
  if (!PyLong_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be int", name);
    return -1;
  }
  unsigned long long value = PyLong_AsUnsignedLongLong(obj);
  if (value == (unsigned long long) -1 && PyErr_Occurred()) {
    PyErr_Format(PyExc_ValueError, "%s must be in [0, 2^64)", name);
    return -1;
  }
  *out = (uint64_t) value;
  return 0;
}

/* Validate that `obj` is a `bytes` of exactly `expected` length. Returns
 * a pointer to its data on success, NULL on failure (and sets an error). */
const uint8_t*
parse_bytes_of_size(
  PyObject* obj,
  Py_ssize_t expected,
  const char* name
) {
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s: expected bytes", name);
    return NULL;
  }
  Py_ssize_t got = PyBytes_GET_SIZE(obj);
  if (got != expected) {
    PyErr_Format(PyExc_ValueError, "%s: expected %zd bytes, got %zd",
                 name, expected, got);
    return NULL;
  }
  return (const uint8_t*) PyBytes_AS_STRING(obj);
}

/* Pack `seq[i]` (each must be `bytes` of `stride`) into a contiguous buffer.
 * Returns malloc'd buffer (caller frees) of size `*out_len * stride`,
 * or NULL on error (sets a Python exception). */
uint8_t*
pack_bytes_sequence(
  PyObject* seq,
  Py_ssize_t stride,
  Py_ssize_t* out_len,
  const char* name
) {
  PyObject* fast = PySequence_Fast(seq, "expected a sequence");
  if (!fast) return NULL;
  Py_ssize_t n = PySequence_Fast_GET_SIZE(fast);
  uint8_t* buf = (uint8_t*) PyMem_Malloc(n * stride);
  if (!buf) {
    Py_DECREF(fast);
    PyErr_NoMemory();
    return NULL;
  }
  for (Py_ssize_t i = 0; i < n; i++) {
    PyObject* item = PySequence_Fast_GET_ITEM(fast, i);
    const uint8_t* p = parse_bytes_of_size(item, stride, name);
    if (!p) { PyMem_Free(buf); Py_DECREF(fast); return NULL; }
    memcpy(buf + i * stride, p, stride);
  }
  Py_DECREF(fast);
  *out_len = n;
  return buf;
}

/* ---- Module table ---------------------------------------------------- */

static PyMethodDef methods[] = {
  {"eth_aggregate_pubkeys", py_eth_aggregate_pubkeys, METH_VARARGS, DOC_eth_aggregate_pubkeys},
  {"eth_fast_aggregate_verify", py_eth_fast_aggregate_verify, METH_VARARGS, DOC_eth_fast_aggregate_verify},
  {"bls_key_gen", py_bls_key_gen, METH_VARARGS, DOC_bls_key_gen},
  {"bls_sign", py_bls_sign, METH_VARARGS, DOC_bls_sign},
  {"bls_verify", py_bls_verify, METH_VARARGS, DOC_bls_verify},
  {"bls_aggregate", py_bls_aggregate, METH_VARARGS, DOC_bls_aggregate},
  {"bls_aggregate_verify", py_bls_aggregate_verify, METH_VARARGS, DOC_bls_aggregate_verify},
  {"bls_fast_aggregate_verify", py_bls_fast_aggregate_verify, METH_VARARGS, DOC_bls_fast_aggregate_verify},
  {"bls_pop_prove", py_bls_pop_prove, METH_VARARGS, DOC_bls_pop_prove},
  {"bls_pop_verify", py_bls_pop_verify, METH_VARARGS, DOC_bls_pop_verify},
  {"bls_decode_g1", py_bls_decode_g1, METH_VARARGS, DOC_bls_decode_g1},
  {"bls_decode_g2", py_bls_decode_g2, METH_VARARGS, DOC_bls_decode_g2},
  {"bls_expand_message_xmd", py_bls_expand_message_xmd, METH_VARARGS, DOC_bls_expand_message_xmd},
  {"bls_hash_to_g2", py_bls_hash_to_g2, METH_VARARGS, DOC_bls_hash_to_g2},
  {"bls_pairing", py_bls_pairing, METH_VARARGS, DOC_bls_pairing},
  {"blob_to_kzg_commitment", py_blob_to_kzg_commitment, METH_VARARGS, DOC_blob_to_kzg_commitment},
  {"compute_challenge", py_compute_challenge, METH_VARARGS, DOC_compute_challenge},
  {"compute_kzg_proof", py_compute_kzg_proof, METH_VARARGS, DOC_compute_kzg_proof},
  {"verify_kzg_proof", py_verify_kzg_proof, METH_VARARGS, DOC_verify_kzg_proof},
  {"compute_blob_kzg_proof", py_compute_blob_kzg_proof, METH_VARARGS, DOC_compute_blob_kzg_proof},
  {"verify_blob_kzg_proof", py_verify_blob_kzg_proof, METH_VARARGS, DOC_verify_blob_kzg_proof},
  {"verify_blob_kzg_proof_batch", py_verify_blob_kzg_proof_batch, METH_VARARGS, DOC_verify_blob_kzg_proof_batch},
  {"compute_cells", py_compute_cells, METH_VARARGS, DOC_compute_cells},
  {"compute_cells_and_kzg_proofs", py_compute_cells_and_kzg_proofs, METH_VARARGS, DOC_compute_cells_and_kzg_proofs},
  {"compute_verify_cell_kzg_proof_batch_challenge", py_compute_verify_cell_kzg_proof_batch_challenge, METH_VARARGS, DOC_compute_verify_cell_kzg_proof_batch_challenge},
  {"verify_cell_kzg_proof_batch", py_verify_cell_kzg_proof_batch, METH_VARARGS, DOC_verify_cell_kzg_proof_batch},
  {"recover_cells_and_kzg_proofs", py_recover_cells_and_kzg_proofs, METH_VARARGS, DOC_recover_cells_and_kzg_proofs},
  {"xmss_key_gen", py_xmss_key_gen, METH_VARARGS, DOC_xmss_key_gen},
  {"xmss_sign", py_xmss_sign, METH_VARARGS, DOC_xmss_sign},
  {"xmss_verify", py_xmss_verify, METH_VARARGS, DOC_xmss_verify},
  {"xmss_signature_index", py_xmss_signature_index, METH_VARARGS, DOC_xmss_signature_index},
  {"sphincs_key_gen", py_sphincs_key_gen, METH_VARARGS, DOC_sphincs_key_gen},
  {"sphincs_sign", py_sphincs_sign, METH_VARARGS, DOC_sphincs_sign},
  {"sphincs_verify", py_sphincs_verify, METH_VARARGS, DOC_sphincs_verify},
  {"modexp", py_modexp, METH_VARARGS, DOC_modexp},
  {"modexp_gas_cost", py_modexp_gas_cost, METH_VARARGS, DOC_modexp_gas_cost},
  {"sha256", py_sha256, METH_VARARGS, DOC_sha256},
  {"keccak256", py_keccak256, METH_VARARGS, DOC_keccak256},
  {"keccak512", py_keccak512, METH_VARARGS, DOC_keccak512},
  {"keccak_f1600", py_keccak_f1600, METH_VARARGS, DOC_keccak_f1600},
  {"trie_root", py_trie_root, METH_VARARGS, DOC_trie_root},
  {"trie_verify_proof", py_trie_verify_proof, METH_VARARGS, DOC_trie_verify_proof},
  {"trie_hex_prefix", py_trie_hex_prefix, METH_VARARGS, DOC_trie_hex_prefix},
  {"vrf_verify", py_vrf_verify, METH_VARARGS, DOC_vrf_verify},
  {"vrf_secret", py_vrf_secret, METH_VARARGS, DOC_vrf_secret},
  {"vrf_evaluate", py_vrf_evaluate, METH_VARARGS, DOC_vrf_evaluate},
  {"crc32", py_crc32, METH_VARARGS, DOC_crc32},
  {"crc32c", py_crc32c, METH_VARARGS, DOC_crc32c},
  {"aes_encrypt_block", py_aes_encrypt_block, METH_VARARGS, DOC_aes_encrypt_block},
  {"aes_decrypt_block", py_aes_decrypt_block, METH_VARARGS, DOC_aes_decrypt_block},
  {"aes_ctr", py_aes_ctr, METH_VARARGS, DOC_aes_ctr},
  {"aes_gcm_encrypt", py_aes_gcm_encrypt, METH_VARARGS, DOC_aes_gcm_encrypt},
  {"aes_gcm_decrypt", py_aes_gcm_decrypt, METH_VARARGS, DOC_aes_gcm_decrypt},
  {"hmac_sha256", py_hmac_sha256, METH_VARARGS, DOC_hmac_sha256},
  {"hkdf_sha256", py_hkdf_sha256, METH_VARARGS, DOC_hkdf_sha256},
  {"concat_kdf_sha256", py_concat_kdf_sha256, METH_VARARGS, DOC_concat_kdf_sha256},
  {"ripemd160", py_ripemd160, METH_VARARGS, DOC_ripemd160},
  {"sha256_precompile", py_sha256_precompile, METH_VARARGS, DOC_sha256_precompile},
  {"sha256_precompile_gas_cost", py_sha256_precompile_gas_cost, METH_VARARGS, DOC_sha256_precompile_gas_cost},
  {"secp256k1_verify", py_secp256k1_verify, METH_VARARGS, DOC_secp256k1_verify},
  {"secp256k1_is_low_s", py_secp256k1_is_low_s, METH_VARARGS, DOC_secp256k1_is_low_s},
  {"secp256k1_recover", py_secp256k1_recover, METH_VARARGS, DOC_secp256k1_recover},
  {"secp256k1_sign", py_secp256k1_sign, METH_VARARGS, DOC_secp256k1_sign},
  {"secp256k1_ecdh", py_secp256k1_ecdh, METH_VARARGS, DOC_secp256k1_ecdh},
  {"secp256k1_address", py_secp256k1_address, METH_VARARGS, DOC_secp256k1_address},
  {"secp256r1_verify", py_secp256r1_verify, METH_VARARGS, DOC_secp256r1_verify},
  {"ecrecover", py_ecrecover, METH_VARARGS, DOC_ecrecover},
  {"enr_from_text", py_enr_from_text, METH_VARARGS, DOC_enr_from_text},
  {"enr_seq", py_enr_seq, METH_VARARGS, DOC_enr_seq},
  {"enr_verify_v4", py_enr_verify_v4, METH_VARARGS, DOC_enr_verify_v4},
  {"enr_node_id", py_enr_node_id, METH_VARARGS, DOC_enr_node_id},
  {"enr_consensus_entries", py_enr_consensus_entries, METH_VARARGS, DOC_enr_consensus_entries},
  {"discv5_log_distance", py_discv5_log_distance, METH_VARARGS, DOC_discv5_log_distance},
  {"discv5_ecdh", py_discv5_ecdh, METH_VARARGS, DOC_discv5_ecdh},
  {"discv5_derive_keys", py_discv5_derive_keys, METH_VARARGS, DOC_discv5_derive_keys},
  {"discv5_id_sign", py_discv5_id_sign, METH_VARARGS, DOC_discv5_id_sign},
  {"discv5_id_verify", py_discv5_id_verify, METH_VARARGS, DOC_discv5_id_verify},
  {"discv5_decode_packet", py_discv5_decode_packet, METH_VARARGS, DOC_discv5_decode_packet},
  {"discv5_reencode_packet", py_discv5_reencode_packet, METH_VARARGS, DOC_discv5_reencode_packet},
  {"discv5_encrypt_message", py_discv5_encrypt_message, METH_VARARGS, DOC_discv5_encrypt_message},
  {"discv5_decrypt_message", py_discv5_decrypt_message, METH_VARARGS, DOC_discv5_decrypt_message},
  {"discv5_decode_message", py_discv5_decode_message, METH_VARARGS, DOC_discv5_decode_message},
  {"discv5_reencode_message", py_discv5_reencode_message, METH_VARARGS, DOC_discv5_reencode_message},
  {"consensus_preset", py_consensus_preset, METH_VARARGS, DOC_consensus_preset},
  {"consensus_config", py_consensus_config, METH_VARARGS, DOC_consensus_config},
  {"consensus_parameters", py_consensus_parameters, METH_VARARGS, DOC_consensus_parameters},
  {"consensus_get_custody_groups", py_consensus_get_custody_groups, METH_VARARGS, DOC_consensus_get_custody_groups},
  {"consensus_compute_columns_for_custody_group", py_consensus_compute_columns_for_custody_group,
   METH_VARARGS, DOC_consensus_compute_columns_for_custody_group},
  {"consensus_ssz_static", py_consensus_ssz_static, METH_VARARGS, DOC_consensus_ssz_static},
  {"consensus_compute_shuffled_permutation", py_consensus_compute_shuffled_permutation,
   METH_VARARGS, DOC_consensus_compute_shuffled_permutation},
  {"consensus_compute_shuffled_index", py_consensus_compute_shuffled_index, METH_VARARGS,
   DOC_consensus_compute_shuffled_index},
  {"reqresp_max_compressed_len", py_reqresp_max_compressed_len, METH_VARARGS, DOC_reqresp_max_compressed_len},
  {"reqresp_decode_payload", py_reqresp_decode_payload, METH_VARARGS, DOC_reqresp_decode_payload},
  {"reqresp_decode_response_chunk", py_reqresp_decode_response_chunk, METH_VARARGS, DOC_reqresp_decode_response_chunk},
  {"block_header_hash", py_block_header_hash, METH_VARARGS, DOC_block_header_hash},
  {"block_reencode", py_block_reencode, METH_VARARGS, DOC_block_reencode},
  {"pow_block_difficulty", py_pow_block_difficulty, METH_VARARGS, DOC_pow_block_difficulty},
  {"block_transactions_root", py_block_transactions_root, METH_VARARGS, DOC_block_transactions_root},
  {"block_withdrawals_root", py_block_withdrawals_root, METH_VARARGS, DOC_block_withdrawals_root},
  {"fees_base_fee_per_gas", py_fees_base_fee_per_gas, METH_VARARGS, DOC_fees_base_fee_per_gas},
  {"fees_fake_exponential", py_fees_fake_exponential, METH_VARARGS, DOC_fees_fake_exponential},
  {"fees_base_fee_per_blob_gas", py_fees_base_fee_per_blob_gas, METH_VARARGS, DOC_fees_base_fee_per_blob_gas},
  {"fees_excess_blob_gas", py_fees_excess_blob_gas, METH_VARARGS, DOC_fees_excess_blob_gas},
  {"evm_word_op", py_evm_word_op, METH_VARARGS, DOC_evm_word_op},
  {"evm_memory_gas_cost", py_evm_memory_gas_cost, METH_VARARGS, DOC_evm_memory_gas_cost},
  {"evm_extend_memory_cost", py_evm_extend_memory_cost, METH_VARARGS, DOC_evm_extend_memory_cost},
  {"evm_extend_memory_expand_by", py_evm_extend_memory_expand_by, METH_VARARGS, DOC_evm_extend_memory_expand_by},
  {"rlp_encode", py_rlp_encode, METH_VARARGS, DOC_rlp_encode},
  {"rlp_decode", py_rlp_decode, METH_VARARGS, DOC_rlp_decode},
  {"rlp_decode_as", py_rlp_decode_as, METH_VARARGS, DOC_rlp_decode_as},
  {"ssz_serialize", py_ssz_serialize, METH_VARARGS, DOC_ssz_serialize},
  {"ssz_deserialize", py_ssz_deserialize, METH_VARARGS, DOC_ssz_deserialize},
  {"ssz_hash_tree_root", py_ssz_hash_tree_root, METH_VARARGS, DOC_ssz_hash_tree_root},
  {"rlpx_ecies_encrypt", py_rlpx_ecies_encrypt, METH_VARARGS, DOC_rlpx_ecies_encrypt},
  {"rlpx_ecies_decrypt", py_rlpx_ecies_decrypt, METH_VARARGS, DOC_rlpx_ecies_decrypt},
  {"devp2p_decode_message", py_devp2p_decode_message, METH_VARARGS, DOC_devp2p_decode_message},
  {"devp2p_encode_message", py_devp2p_encode_message, METH_VARARGS, DOC_devp2p_encode_message},
  {"discv4_decode", py_discv4_decode, METH_VARARGS, DOC_discv4_decode},
  {"discv4_encode", py_discv4_encode, METH_VARARGS, DOC_discv4_encode},
  {"discv4_record_signed_by", py_discv4_record_signed_by, METH_VARARGS, DOC_discv4_record_signed_by},
  {"snappy_decompress", py_snappy_decompress, METH_VARARGS, DOC_snappy_decompress},
  {"snappy_compress_literal", py_snappy_compress_literal, METH_VARARGS, DOC_snappy_compress_literal},
  {"snappy_decode_frames", py_snappy_decode_frames, METH_VARARGS, DOC_snappy_decode_frames},
  {"snappy_encode_frames_literal", py_snappy_encode_frames_literal, METH_VARARGS, DOC_snappy_encode_frames_literal},
  {"snappy_masked_crc", py_snappy_masked_crc, METH_VARARGS, DOC_snappy_masked_crc},
  {"varint_encode", py_varint_encode, METH_VARARGS, DOC_varint_encode},
  {"varint_decode", py_varint_decode, METH_VARARGS, DOC_varint_decode},
  {"gossip_message_id_phase0", py_gossip_message_id_phase0, METH_VARARGS, DOC_gossip_message_id_phase0},
  {"gossip_message_id_altair", py_gossip_message_id_altair, METH_VARARGS, DOC_gossip_message_id_altair},
  {"receipt_reencode", py_receipt_reencode, METH_VARARGS, DOC_receipt_reencode},
  {"receipt_logs_bloom", py_receipt_logs_bloom, METH_VARARGS, DOC_receipt_logs_bloom},
  {"tx_type", py_tx_type, METH_VARARGS, DOC_tx_type},
  {"tx_hash", py_tx_hash, METH_VARARGS, DOC_tx_hash},
  {"tx_recover_sender", py_tx_recover_sender, METH_VARARGS, DOC_tx_recover_sender},
  {"tx_intrinsic_gas", py_tx_intrinsic_gas, METH_VARARGS, DOC_tx_intrinsic_gas},
  {"tx_check", py_tx_check, METH_VARARGS, DOC_tx_check},
  {"rlpx_make_auth", py_rlpx_make_auth, METH_VARARGS, DOC_rlpx_make_auth},
  {"rlpx_respond", py_rlpx_respond, METH_VARARGS, DOC_rlpx_respond},
  {"rlpx_recipient_secrets", py_rlpx_recipient_secrets, METH_VARARGS, DOC_rlpx_recipient_secrets},
  {"rlpx_finish", py_rlpx_finish, METH_VARARGS, DOC_rlpx_finish},
  {"block_validate_header", py_block_validate_header, METH_VARARGS, DOC_block_validate_header},
  {"precompile_run", py_precompile_run, METH_VARARGS, DOC_precompile_run},
  {"state_root", py_state_root, METH_VARARGS, DOC_state_root},
  {"state_withdrawals_root", py_state_withdrawals_root, METH_VARARGS, DOC_state_withdrawals_root},
  {"mainnet_active_fork", py_mainnet_active_fork, METH_VARARGS, DOC_mainnet_active_fork},
  {NULL, NULL, 0, NULL},
};

static struct PyModuleDef moduledef = {
  PyModuleDef_HEAD_INIT,
  "_native", /* m_name */
  NULL, /* m_doc */
  -1, /* m_size — global state */
  methods,
  NULL, NULL, NULL, NULL,
};

PyMODINIT_FUNC
PyInit__native(void) {
  /* Boot the Lean runtime exactly once when the extension loads. */
  static int initialized = 0;
  if (!initialized) {
    /* The exception classes are plain Python, in `ethlib.errors`.
     * They are looked up before the Lean runtime boots, so a failed import boots nothing.
     * That module imports nothing from this extension, so the import cannot loop. */
    PyObject* errors = PyImport_ImportModule("ethlib.errors");
    if (!errors) return NULL;
    KZG_ERROR = PyObject_GetAttrString(errors, "KzgError");
    BLS_ERROR = PyObject_GetAttrString(errors, "BlsError");
    XMSS_ERROR = PyObject_GetAttrString(errors, "XmssError");
    SPHINCS_ERROR = PyObject_GetAttrString(errors, "SphincsError");
    SECP256K1_ERROR = PyObject_GetAttrString(errors, "Secp256k1Error");
    SECP256R1_ERROR = PyObject_GetAttrString(errors, "Secp256r1Error");
    ENR_ERROR = PyObject_GetAttrString(errors, "EnrError");
    ECRECOVER_ERROR = PyObject_GetAttrString(errors, "EcrecoverError");
    MODEXP_ERROR = PyObject_GetAttrString(errors, "ModexpError");
    SHA256_PRECOMPILE_ERROR = PyObject_GetAttrString(errors, "Sha256PrecompileError");
    PRECOMPILE_ERROR = PyObject_GetAttrString(errors, "PrecompileError");
    STATE_ERROR = PyObject_GetAttrString(errors, "StateError");
    KECCAK_ERROR = PyObject_GetAttrString(errors, "KeccakError");
    REQRESP_ERROR = PyObject_GetAttrString(errors, "ReqRespError");
    CONSENSUS_ERROR = PyObject_GetAttrString(errors, "ConsensusError");
    HKDF_ERROR = PyObject_GetAttrString(errors, "HkdfError");
    AES_ERROR = PyObject_GetAttrString(errors, "AesError");
    CONCAT_KDF_ERROR = PyObject_GetAttrString(errors, "ConcatKdfError");
    BLOCK_ERROR = PyObject_GetAttrString(errors, "BlockError");
    RLP_ERROR = PyObject_GetAttrString(errors, "RlpError");
    SSZ_ERROR = PyObject_GetAttrString(errors, "SszError");
    SNAPPY_ERROR = PyObject_GetAttrString(errors, "SnappyError");
    VARINT_ERROR = PyObject_GetAttrString(errors, "VarintError");
    DISCV5_ERROR = PyObject_GetAttrString(errors, "Discv5Error");
    RLPX_ERROR = PyObject_GetAttrString(errors, "RlpxError");
    DEVP2P_ERROR = PyObject_GetAttrString(errors, "Devp2pError");
    DISCV4_ERROR = PyObject_GetAttrString(errors, "Discv4Error");
    TRANSACTION_ERROR = PyObject_GetAttrString(errors, "TransactionError");
    VRF_ERROR = PyObject_GetAttrString(errors, "VrfError");
    TRIE_ERROR = PyObject_GetAttrString(errors, "TrieError");
    EVM_ERROR = PyObject_GetAttrString(errors, "EvmError");
    FEES_ERROR = PyObject_GetAttrString(errors, "FeesError");
    Py_DECREF(errors);
    if (PyErr_Occurred()) return NULL;

    lean_initialize_runtime_module();
    lean_object* res = initialize_EthLib_EthLib_Cryptography_Exports(1);
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
      res = initialize_EthLib_EthLib_Networking_Exports(1);
    }
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
      res = initialize_EthLib_EthLib_Execution_Exports(1);
    }
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
      res = initialize_EthLib_EthLib_Consensus_Exports(1);
    }
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
      res = initialize_EthLib_EthLib_Serialization_Exports(1);
    }
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
      res = initialize_EthLib_EthLib_Base_Exports_ChainConfig(1);
    }
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
    } else {
      lean_io_result_show_error(res);
      lean_dec(res);
      PyErr_SetString(PyExc_RuntimeError,
                      "failed to initialize Lean runtime");
      return NULL;
    }
    lean_io_mark_end_initialization();

    /* Start the worker threads that run Lean tasks.
     * Without them, a task runs on the calling thread, and independent work runs in sequence. */
    lean_init_task_manager();

    /* Pull the spec-preset sizes out of the linked Lean static archive */
    BYTES_PER_PUBKEY        = (size_t) eth_bls_const_bytes_per_pubkey(lean_box(0));
    BYTES_PER_SIGNATURE     = (size_t) eth_bls_const_bytes_per_signature(lean_box(0));
    BYTES_PER_FIELD_ELEMENT = (size_t) eth_kzg_const_bytes_per_field_element(lean_box(0));
    BYTES_PER_COMMITMENT    = (size_t) eth_kzg_const_bytes_per_commitment(lean_box(0));
    BYTES_PER_PROOF         = (size_t) eth_kzg_const_bytes_per_proof(lean_box(0));
    FIELD_ELEMENTS_PER_BLOB = (size_t) eth_kzg_const_field_elements_per_blob(lean_box(0));
    BYTES_PER_BLOB          = (size_t) eth_kzg_const_bytes_per_blob(lean_box(0));
    FIELD_ELEMENTS_PER_CELL = (size_t) eth_kzg_const_field_elements_per_cell(lean_box(0));
    BYTES_PER_CELL          = (size_t) eth_kzg_const_bytes_per_cell(lean_box(0));
    CELLS_PER_EXT_BLOB      = (size_t) eth_kzg_const_cells_per_ext_blob(lean_box(0));
    XMSS_MESSAGE_LEN  = (size_t) eth_xmss_const_message_len(lean_box(0));
    XMSS_SEED_LEN     = (size_t) eth_xmss_const_seed_len(lean_box(0));
    XMSS_PUB_KEY_SIZE = (size_t) eth_xmss_const_pub_key_size(lean_box(0));
    XMSS_SIG_SIZE     = (size_t) eth_xmss_const_sig_size(lean_box(0));
    SPHINCS_MESSAGE_LEN  = (size_t) eth_sphincs_const_message_len(lean_box(0));
    SPHINCS_SEED_LEN     = (size_t) eth_sphincs_const_seed_len(lean_box(0));
    SPHINCS_PUB_KEY_SIZE = (size_t) eth_sphincs_const_pub_key_size(lean_box(0));
    SPHINCS_SIG_SIZE     = (size_t) eth_sphincs_const_sig_size(lean_box(0));

    MODEXP_LENGTH_HEADER_BYTES = (size_t) eth_modexp_const_length_header_bytes(lean_box(0));
    MODEXP_MAX_LENGTH_BYTES    = (size_t) eth_modexp_const_max_length_bytes(lean_box(0));
    SECP256K1_HASH_LEN      = (size_t) eth_secp256k1_const_hash_len(lean_box(0));
    SECP256K1_SIGNATURE_LEN = (size_t) eth_secp256k1_const_signature_len(lean_box(0));
    SECP256R1_PUBLIC_KEY_LEN = (size_t) eth_secp256r1_const_public_key_len(lean_box(0));
    SECP256R1_HASH_LEN       = (size_t) eth_secp256r1_const_hash_len(lean_box(0));
    SECP256R1_SIGNATURE_LEN  = (size_t) eth_secp256r1_const_signature_len(lean_box(0));
    ECRECOVER_GAS           = (size_t) eth_ecrecover_const_gas(lean_box(0));
    ENR_MAX_RECORD_SIZE     = (size_t) eth_enr_const_max_record_size(lean_box(0));
    REQRESP_MAX_PAYLOAD_SIZE = (size_t) eth_reqresp_const_max_payload_size(lean_box(0));
    REQRESP_MAX_ERROR_MESSAGE_SIZE = (size_t) eth_reqresp_const_max_error_message_size(lean_box(0));

    RIPEMD160_OUTPUT_BYTES = (size_t) eth_ripemd160_const_output_bytes(lean_box(0));
    SHA256_PRECOMPILE_OUTPUT_BYTES = (size_t) eth_sha256_precompile_const_output_bytes(lean_box(0));

    initialized = 1;
  }

  PyObject* m = PyModule_Create(&moduledef);
  if (!m) return NULL;

  /* Expose the spec presets as module-level constants. */
  PyModule_AddIntConstant(m, "BYTES_PER_PUBKEY", BYTES_PER_PUBKEY);
  PyModule_AddIntConstant(m, "BYTES_PER_SIGNATURE", BYTES_PER_SIGNATURE);
  PyModule_AddIntConstant(m, "BYTES_PER_BLOB", BYTES_PER_BLOB);
  PyModule_AddIntConstant(m, "BYTES_PER_FIELD_ELEMENT", BYTES_PER_FIELD_ELEMENT);
  PyModule_AddIntConstant(m, "BYTES_PER_COMMITMENT", BYTES_PER_COMMITMENT);
  PyModule_AddIntConstant(m, "BYTES_PER_PROOF", BYTES_PER_PROOF);
  PyModule_AddIntConstant(m, "FIELD_ELEMENTS_PER_BLOB", FIELD_ELEMENTS_PER_BLOB);
  PyModule_AddIntConstant(m, "FIELD_ELEMENTS_PER_CELL", FIELD_ELEMENTS_PER_CELL);
  PyModule_AddIntConstant(m, "BYTES_PER_CELL", BYTES_PER_CELL);
  PyModule_AddIntConstant(m, "CELLS_PER_EXT_BLOB", CELLS_PER_EXT_BLOB);
  PyModule_AddIntConstant(m, "XMSS_MESSAGE_LEN", XMSS_MESSAGE_LEN);
  PyModule_AddIntConstant(m, "XMSS_SEED_LEN", XMSS_SEED_LEN);
  PyModule_AddIntConstant(m, "XMSS_PUB_KEY_SIZE", XMSS_PUB_KEY_SIZE);
  PyModule_AddIntConstant(m, "XMSS_SIG_SIZE", XMSS_SIG_SIZE);
  PyModule_AddIntConstant(m, "SPHINCS_MESSAGE_LEN", SPHINCS_MESSAGE_LEN);
  PyModule_AddIntConstant(m, "SPHINCS_SEED_LEN", SPHINCS_SEED_LEN);
  PyModule_AddIntConstant(m, "SPHINCS_PUB_KEY_SIZE", SPHINCS_PUB_KEY_SIZE);
  PyModule_AddIntConstant(m, "SPHINCS_SIG_SIZE", SPHINCS_SIG_SIZE);
  PyModule_AddIntConstant(m, "MODEXP_LENGTH_HEADER_BYTES", MODEXP_LENGTH_HEADER_BYTES);
  PyModule_AddIntConstant(m, "MODEXP_MAX_LENGTH_BYTES", MODEXP_MAX_LENGTH_BYTES);
  PyModule_AddIntConstant(m, "RIPEMD160_OUTPUT_BYTES", RIPEMD160_OUTPUT_BYTES);
  PyModule_AddIntConstant(m, "SHA256_PRECOMPILE_OUTPUT_BYTES", SHA256_PRECOMPILE_OUTPUT_BYTES);
  PyModule_AddIntConstant(m, "SECP256K1_HASH_LEN", SECP256K1_HASH_LEN);
  PyModule_AddIntConstant(m, "SECP256K1_SIGNATURE_LEN", SECP256K1_SIGNATURE_LEN);
  PyModule_AddIntConstant(m, "SECP256R1_PUBLIC_KEY_LEN", SECP256R1_PUBLIC_KEY_LEN);
  PyModule_AddIntConstant(m, "SECP256R1_HASH_LEN", SECP256R1_HASH_LEN);
  PyModule_AddIntConstant(m, "SECP256R1_SIGNATURE_LEN", SECP256R1_SIGNATURE_LEN);
  PyModule_AddIntConstant(m, "ECRECOVER_GAS", ECRECOVER_GAS);
  PyModule_AddIntConstant(m, "ENR_MAX_RECORD_SIZE", ENR_MAX_RECORD_SIZE);
  PyModule_AddIntConstant(m, "REQRESP_MAX_PAYLOAD_SIZE", REQRESP_MAX_PAYLOAD_SIZE);
  PyModule_AddIntConstant(m, "REQRESP_MAX_ERROR_MESSAGE_SIZE", REQRESP_MAX_ERROR_MESSAGE_SIZE);
  return m;
}

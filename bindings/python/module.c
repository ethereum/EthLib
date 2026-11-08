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
size_t XMSS_DIGEST_LEN;
size_t XMSS_PUBLIC_PARAM_LEN;
size_t XMSS_RANDOMIZER_LEN;
size_t XMSS_CHAINS;
size_t XMSS_LAYER_HEIGHT;
size_t XMSS_LEAF_INDEX_SIZE;

size_t SPHINCS_MESSAGE_LEN;
size_t SPHINCS_SEED_LEN;
size_t SPHINCS_PUB_KEY_SIZE;
size_t SPHINCS_SIG_SIZE;
size_t SPHINCS_N;
size_t SPHINCS_PUBLIC_PARAM_LEN;
size_t SPHINCS_RANDOMIZER_LEN;
size_t SPHINCS_CHAINS;
size_t SPHINCS_COUNTER_LEN;
size_t SPHINCS_TOP_HEIGHT;
size_t SPHINCS_LOWER_HEIGHT;
size_t SPHINCS_FORS_TREES;
size_t SPHINCS_FORS_HEIGHT;


size_t ENR_MAX_RECORD_SIZE;
size_t REQRESP_MAX_PAYLOAD_SIZE;
size_t REQRESP_MAX_ERROR_MESSAGE_SIZE;
size_t SECP256K1_HASH_LEN;
size_t SECP256K1_SIGNATURE_LEN;

size_t SECP256R1_PUBLIC_KEY_LEN;
size_t SECP256R1_HASH_LEN;
size_t SECP256R1_SIGNATURE_LEN;


/* ---- Exception classes (looked up in `PyInit__native`) --------------- */

PyObject* KZG_ERROR;
PyObject* BLS_ERROR;
PyObject* XMSS_ERROR;
PyObject* SPHINCS_ERROR;
PyObject* SECP256K1_ERROR;
PyObject* SECP256R1_ERROR;
PyObject* ENR_ERROR;
PyObject* PRECOMPILE_ERROR;
PyObject* STATE_ERROR;
PyObject* KECCAK_ERROR;
PyObject* ETHASH_ERROR;
PyObject* REQRESP_ERROR;
PyObject* CONSENSUS_ERROR;
PyObject* HKDF_ERROR;
PyObject* AES_ERROR;
PyObject* CONCAT_KDF_ERROR;
PyObject* BLOCK_ERROR;
PyObject* ENGINE_ERROR;
PyObject* CHAIN_ERROR;
PyObject* RLP_ERROR;
PyObject* SSZ_ERROR;
PyObject* SNAPPY_ERROR;
PyObject* VARINT_ERROR;
PyObject* GOSSIP_ERROR;
PyObject* DISCV5_ERROR;
PyObject* RLPX_ERROR;
PyObject* DEVP2P_ERROR;
PyObject* DISCV4_ERROR;
PyObject* FORK_ID_ERROR;
PyObject* ETH_WIRE_ERROR;
PyObject* SNAP_ERROR;
PyObject* TRANSACTION_ERROR;
PyObject* VRF_ERROR;
PyObject* TRIE_ERROR;
PyObject* EVM_ERROR;
PyObject* FEES_ERROR;
PyObject* TRANSITION_ERROR;
PyObject* LIGHT_CLIENT_ERROR;
PyObject* FORK_CHOICE_ERROR;
PyObject* WEAK_SUBJECTIVITY_ERROR;
PyObject* VALIDATOR_DUTY_ERROR;
PyObject* PROPOSER_ERROR;
PyObject* SLASHING_PROTECTION_ERROR;
PyObject* BINDING_ERROR;

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
eth_xmss_const_digest_len(
  lean_object* unit
);

extern uint64_t
eth_xmss_const_public_param_len(
  lean_object* unit
);

extern uint64_t
eth_xmss_const_randomizer_len(
  lean_object* unit
);

extern uint64_t
eth_xmss_const_chains(
  lean_object* unit
);

extern uint64_t
eth_xmss_const_layer_height(
  lean_object* unit
);

extern uint64_t
eth_xmss_const_leaf_index_size(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_n(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_public_param_len(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_randomizer_len(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_chains(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_counter_len(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_top_height(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_lower_height(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_fors_trees(
  lean_object* unit
);

extern uint64_t
eth_sphincs_const_fors_height(
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

extern lean_object*
initialize_EthLib_EthLib_Engine_Exports(
  uint8_t builtin
);

extern lean_object*
initialize_EthLib_EthLib_Base_Exports_Echo(
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
except_into_pybytes_list(
  lean_object* result,
  PyObject* error_class
) {
  if (is_error(result)) {
    raise_lean_error(result, error_class);
    return NULL;
  }
  lean_object* items = lean_ctor_get(result, 0);
  size_t n = lean_array_size(items);
  PyObject* out = PyList_New((Py_ssize_t) n);
  for (size_t i = 0; out && i < n; i++) {
    lean_object* ba = lean_array_get_core(items, i);
    PyObject* item = PyBytes_FromStringAndSize(
      (const char*) lean_sarray_cptr(ba), (Py_ssize_t) lean_sarray_size(ba));
    if (!item) {
      Py_CLEAR(out);
      break;
    }
    PyList_SET_ITEM(out, (Py_ssize_t) i, item);
  }
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

/* A Python `int` in [0, 2^64), or -1 with an exception set: OverflowError outside it. */
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
    PyErr_Format(PyExc_OverflowError, "%s must be in [0, 2^64)", name);
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
  {"sha256", py_sha256, METH_VARARGS, DOC_sha256},
  {"keccak256", py_keccak256, METH_VARARGS, DOC_keccak256},
  {"keccak512", py_keccak512, METH_VARARGS, DOC_keccak512},
  {"ethash_cache_size", py_ethash_cache_size, METH_VARARGS, DOC_ethash_cache_size},
  {"ethash_dataset_size", py_ethash_dataset_size, METH_VARARGS, DOC_ethash_dataset_size},
  {"ethash_seed", py_ethash_seed, METH_VARARGS, DOC_ethash_seed},
  {"ethash_cache", py_ethash_cache, METH_VARARGS, DOC_ethash_cache},
  {"ethash_dataset_item", py_ethash_dataset_item, METH_VARARGS, DOC_ethash_dataset_item},
  {"ethash_hashimoto_light", py_ethash_hashimoto_light, METH_VARARGS, DOC_ethash_hashimoto_light},
  {"keccak_f1600", py_keccak_f1600, METH_VARARGS, DOC_keccak_f1600},
  {"trie_root", py_trie_root, METH_VARARGS, DOC_trie_root},
  {"trie_verify_proof", py_trie_verify_proof, METH_VARARGS, DOC_trie_verify_proof},
  {"trie_hex_prefix", py_trie_hex_prefix, METH_VARARGS, DOC_trie_hex_prefix},
  {"trie_verify_account_proof", py_trie_verify_account_proof, METH_VARARGS, DOC_trie_verify_account_proof},
  {"vrf_verify", py_vrf_verify, METH_VARARGS, DOC_vrf_verify},
  {"vrf_secret", py_vrf_secret, METH_VARARGS, DOC_vrf_secret},
  {"vrf_evaluate", py_vrf_evaluate, METH_VARARGS, DOC_vrf_evaluate},
  {"crc32", py_crc32, METH_VARARGS, DOC_crc32},
  {"crc32_number", py_crc32_number, METH_VARARGS, DOC_crc32_number},
  {"crc32c", py_crc32c, METH_VARARGS, DOC_crc32c},
  {"crc32c_number", py_crc32c_number, METH_VARARGS, DOC_crc32c_number},
  {"aes_encrypt_block", py_aes_encrypt_block, METH_VARARGS, DOC_aes_encrypt_block},
  {"aes_decrypt_block", py_aes_decrypt_block, METH_VARARGS, DOC_aes_decrypt_block},
  {"aes_ctr", py_aes_ctr, METH_VARARGS, DOC_aes_ctr},
  {"aes_gcm_encrypt", py_aes_gcm_encrypt, METH_VARARGS, DOC_aes_gcm_encrypt},
  {"aes_gcm_decrypt", py_aes_gcm_decrypt, METH_VARARGS, DOC_aes_gcm_decrypt},
  {"hmac_sha256", py_hmac_sha256, METH_VARARGS, DOC_hmac_sha256},
  {"hkdf_sha256", py_hkdf_sha256, METH_VARARGS, DOC_hkdf_sha256},
  {"concat_kdf_sha256", py_concat_kdf_sha256, METH_VARARGS, DOC_concat_kdf_sha256},
  {"secp256k1_verify", py_secp256k1_verify, METH_VARARGS, DOC_secp256k1_verify},
  {"secp256k1_is_low_s", py_secp256k1_is_low_s, METH_VARARGS, DOC_secp256k1_is_low_s},
  {"secp256k1_recover", py_secp256k1_recover, METH_VARARGS, DOC_secp256k1_recover},
  {"secp256k1_sign", py_secp256k1_sign, METH_VARARGS, DOC_secp256k1_sign},
  {"secp256k1_ecdh", py_secp256k1_ecdh, METH_VARARGS, DOC_secp256k1_ecdh},
  {"secp256k1_address", py_secp256k1_address, METH_VARARGS, DOC_secp256k1_address},
  {"secp256r1_verify", py_secp256r1_verify, METH_VARARGS, DOC_secp256r1_verify},
  {"enr_from_text", py_enr_from_text, METH_VARARGS, DOC_enr_from_text},
  {"enr_seq", py_enr_seq, METH_VARARGS, DOC_enr_seq},
  {"enr_verify_v4", py_enr_verify_v4, METH_VARARGS, DOC_enr_verify_v4},
  {"enr_node_id", py_enr_node_id, METH_VARARGS, DOC_enr_node_id},
  {"enr_sign_v4", py_enr_sign_v4, METH_VARARGS, DOC_enr_sign_v4},
  {"enr_make_record_v4", py_enr_make_record_v4, METH_VARARGS, DOC_enr_make_record_v4},
  {"enr_consensus_entries", py_enr_consensus_entries, METH_VARARGS, DOC_enr_consensus_entries},
  {"enr_eth_fork_id", py_enr_eth_fork_id, METH_VARARGS, DOC_enr_eth_fork_id},
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
  {"discv5_make_whoareyou", py_discv5_make_whoareyou, METH_VARARGS, DOC_discv5_make_whoareyou},
  {"discv5_read_whoareyou", py_discv5_read_whoareyou, METH_VARARGS, DOC_discv5_read_whoareyou},
  {"discv5_seal_message", py_discv5_seal_message, METH_VARARGS, DOC_discv5_seal_message},
  {"discv5_open_message", py_discv5_open_message, METH_VARARGS, DOC_discv5_open_message},
  {"discv5_seal_handshake", py_discv5_seal_handshake, METH_VARARGS, DOC_discv5_seal_handshake},
  {"discv5_open_handshake", py_discv5_open_handshake, METH_VARARGS, DOC_discv5_open_handshake},
  {"consensus_preset", py_consensus_preset, METH_VARARGS, DOC_consensus_preset},
  {"consensus_config", py_consensus_config, METH_VARARGS, DOC_consensus_config},
  {"consensus_parameters", py_consensus_parameters, METH_VARARGS, DOC_consensus_parameters},
  {"consensus_get_custody_groups", py_consensus_get_custody_groups, METH_VARARGS, DOC_consensus_get_custody_groups},
  {"consensus_compute_columns_for_custody_group", py_consensus_compute_columns_for_custody_group,
   METH_VARARGS, DOC_consensus_compute_columns_for_custody_group},
  {"consensus_ssz_static", py_consensus_ssz_static, METH_VARARGS, DOC_consensus_ssz_static},
  {"consensus_merkle_proof", py_consensus_merkle_proof, METH_VARARGS, DOC_consensus_merkle_proof},
  {"consensus_verify_blob_sidecar_inclusion_proof", py_consensus_verify_blob_sidecar_inclusion_proof,
   METH_VARARGS, DOC_consensus_verify_blob_sidecar_inclusion_proof},
  {"consensus_process_operation", py_consensus_process_operation, METH_VARARGS,
   DOC_consensus_process_operation},
  {"consensus_light_client_sync", py_consensus_light_client_sync, METH_VARARGS,
   DOC_consensus_light_client_sync},
  {"consensus_is_better_update", py_consensus_is_better_update, METH_VARARGS,
   DOC_consensus_is_better_update},
  {"consensus_genesis_block", py_consensus_genesis_block, METH_VARARGS,
   DOC_consensus_genesis_block},
  {"consensus_create_light_client_bootstrap", py_consensus_create_light_client_bootstrap,
   METH_VARARGS, DOC_consensus_create_light_client_bootstrap},
  {"consensus_create_light_client_update", py_consensus_create_light_client_update,
   METH_VARARGS, DOC_consensus_create_light_client_update},
  {"consensus_block_to_light_client_header", py_consensus_block_to_light_client_header,
   METH_VARARGS, DOC_consensus_block_to_light_client_header},
  {"consensus_light_client_update_proofs", py_consensus_light_client_update_proofs,
   METH_VARARGS, DOC_consensus_light_client_update_proofs},
  {"consensus_compute_fork_digest", py_consensus_compute_fork_digest, METH_VARARGS,
   DOC_consensus_compute_fork_digest},
  {"consensus_process_epoch", py_consensus_process_epoch, METH_VARARGS,
   DOC_consensus_process_epoch},
  {"consensus_rewards_deltas", py_consensus_rewards_deltas, METH_VARARGS,
   DOC_consensus_rewards_deltas},
  {"consensus_rewards_deltas_batch", py_consensus_rewards_deltas_batch, METH_VARARGS,
   DOC_consensus_rewards_deltas_batch},
  {"consensus_upgrade_state", py_consensus_upgrade_state, METH_VARARGS,
   DOC_consensus_upgrade_state},
  {"consensus_process_slots", py_consensus_process_slots, METH_VARARGS,
   DOC_consensus_process_slots},
  {"consensus_state_transition", py_consensus_state_transition, METH_VARARGS,
   DOC_consensus_state_transition},
  {"consensus_state_transition_across", py_consensus_state_transition_across, METH_VARARGS,
   DOC_consensus_state_transition_across},
  {"consensus_state_transitions", py_consensus_state_transitions, METH_VARARGS,
   DOC_consensus_state_transitions},
  {"consensus_state_transitions_across", py_consensus_state_transitions_across, METH_VARARGS,
   DOC_consensus_state_transitions_across},
  {"consensus_fork_choice", py_consensus_fork_choice, METH_VARARGS, DOC_consensus_fork_choice},
  {"consensus_gossip_validation", py_consensus_gossip_validation, METH_VARARGS,
    DOC_consensus_gossip_validation},
  {"consensus_initialize_genesis", py_consensus_initialize_genesis, METH_VARARGS,
   DOC_consensus_initialize_genesis},
  {"consensus_is_valid_genesis_state", py_consensus_is_valid_genesis_state, METH_VARARGS,
   DOC_consensus_is_valid_genesis_state},
  {"consensus_compute_weak_subjectivity_period", py_consensus_compute_weak_subjectivity_period,
   METH_VARARGS, DOC_consensus_compute_weak_subjectivity_period},
  {"consensus_is_within_weak_subjectivity_period",
   py_consensus_is_within_weak_subjectivity_period, METH_VARARGS,
   DOC_consensus_is_within_weak_subjectivity_period},
  {"consensus_get_committee_assignment", py_consensus_get_committee_assignment, METH_VARARGS,
   DOC_consensus_get_committee_assignment},
  {"consensus_is_proposer", py_consensus_is_proposer, METH_VARARGS,
   DOC_consensus_is_proposer},
  {"consensus_is_assigned_to_sync_committee",
   py_consensus_is_assigned_to_sync_committee, METH_VARARGS,
   DOC_consensus_is_assigned_to_sync_committee},
  {"consensus_compute_subnets_for_sync_committee",
   py_consensus_compute_subnets_for_sync_committee, METH_VARARGS,
   DOC_consensus_compute_subnets_for_sync_committee},
  {"consensus_get_ptc_assignment", py_consensus_get_ptc_assignment, METH_VARARGS,
   DOC_consensus_get_ptc_assignment},
  {"consensus_get_upcoming_proposal_slots", py_consensus_get_upcoming_proposal_slots,
   METH_VARARGS, DOC_consensus_get_upcoming_proposal_slots},
  {"consensus_get_validator_signature", py_consensus_get_validator_signature, METH_VARARGS,
   DOC_consensus_get_validator_signature},
  {"consensus_get_attestation_data", py_consensus_get_attestation_data, METH_VARARGS,
   DOC_consensus_get_attestation_data},
  {"consensus_get_aggregate_signature", py_consensus_get_aggregate_signature, METH_VARARGS,
   DOC_consensus_get_aggregate_signature},
  {"consensus_construct_attestation", py_consensus_construct_attestation, METH_VARARGS,
   DOC_consensus_construct_attestation},
  {"consensus_construct_single_attestation", py_consensus_construct_single_attestation,
   METH_VARARGS, DOC_consensus_construct_single_attestation},
  {"consensus_construct_aggregate", py_consensus_construct_aggregate, METH_VARARGS,
   DOC_consensus_construct_aggregate},
  {"consensus_construct_aggregate_of_single_attestations",
   py_consensus_construct_aggregate_of_single_attestations, METH_VARARGS,
   DOC_consensus_construct_aggregate_of_single_attestations},
  {"consensus_construct_sync_committee_contribution",
   py_consensus_construct_sync_committee_contribution, METH_VARARGS,
   DOC_consensus_construct_sync_committee_contribution},
  {"consensus_process_sync_committee_contributions",
   py_consensus_process_sync_committee_contributions, METH_VARARGS,
   DOC_consensus_process_sync_committee_contributions},
  {"consensus_read_slashing_interchange", py_consensus_read_slashing_interchange, METH_VARARGS,
   DOC_consensus_read_slashing_interchange},
  {"consensus_import_slashing_interchange", py_consensus_import_slashing_interchange,
   METH_VARARGS, DOC_consensus_import_slashing_interchange},
  {"consensus_check_block_signing", py_consensus_check_block_signing, METH_VARARGS,
   DOC_consensus_check_block_signing},
  {"consensus_check_attestation_signing", py_consensus_check_attestation_signing, METH_VARARGS,
   DOC_consensus_check_attestation_signing},
  {"consensus_record_block_signing", py_consensus_record_block_signing, METH_VARARGS,
   DOC_consensus_record_block_signing},
  {"consensus_record_attestation_signing", py_consensus_record_attestation_signing,
   METH_VARARGS, DOC_consensus_record_attestation_signing},
  {"consensus_is_execution_block", py_consensus_is_execution_block, METH_VARARGS,
   DOC_consensus_is_execution_block},
  {"consensus_is_optimistic_candidate_block", py_consensus_is_optimistic_candidate_block,
   METH_VARARGS, DOC_consensus_is_optimistic_candidate_block},
  {"consensus_latest_verified_ancestor", py_consensus_latest_verified_ancestor, METH_VARARGS,
   DOC_consensus_latest_verified_ancestor},
  {"consensus_on_valid_payload", py_consensus_on_valid_payload, METH_VARARGS,
   DOC_consensus_on_valid_payload},
  {"consensus_on_invalidated_payload", py_consensus_on_invalidated_payload, METH_VARARGS,
   DOC_consensus_on_invalidated_payload},
  {"consensus_is_optimistic_restricted_domain", py_consensus_is_optimistic_restricted_domain,
   METH_VARARGS, DOC_consensus_is_optimistic_restricted_domain},
  {"consensus_get_eth1_vote", py_consensus_get_eth1_vote, METH_VARARGS,
   DOC_consensus_get_eth1_vote},
  {"consensus_get_eth1_pending_deposit_count", py_consensus_get_eth1_pending_deposit_count,
   METH_VARARGS, DOC_consensus_get_eth1_pending_deposit_count},
  {"consensus_compute_new_state_root", py_consensus_compute_new_state_root, METH_VARARGS,
   DOC_consensus_compute_new_state_root},
  {"consensus_compute_on_chain_aggregate", py_consensus_compute_on_chain_aggregate,
   METH_VARARGS, DOC_consensus_compute_on_chain_aggregate},
  {"consensus_get_execution_requests", py_consensus_get_execution_requests, METH_VARARGS,
   DOC_consensus_get_execution_requests},
  {"consensus_get_execution_payload_bid", py_consensus_get_execution_payload_bid, METH_VARARGS,
   DOC_consensus_get_execution_payload_bid},
  {"consensus_get_self_built_execution_payload_bid",
   py_consensus_get_self_built_execution_payload_bid, METH_VARARGS,
   DOC_consensus_get_self_built_execution_payload_bid},
  {"consensus_get_execution_payload_envelope", py_consensus_get_execution_payload_envelope,
   METH_VARARGS, DOC_consensus_get_execution_payload_envelope},
  {"consensus_get_validators_custody_requirement",
   py_consensus_get_validators_custody_requirement, METH_VARARGS,
   DOC_consensus_get_validators_custody_requirement},
  {"pq_keys_ssz", py_pq_keys_ssz, METH_VARARGS, DOC_pq_keys_ssz},
  {"pq_keys_possession_signing_root", py_pq_keys_possession_signing_root, METH_VARARGS,
   DOC_pq_keys_possession_signing_root},
  {"pq_keys_is_valid_possession_proof", py_pq_keys_is_valid_possession_proof, METH_VARARGS,
   DOC_pq_keys_is_valid_possession_proof},
  {"consensus_verify_data_column_sidecar", py_consensus_verify_data_column_sidecar, METH_VARARGS,
   DOC_consensus_verify_data_column_sidecar},
  {"consensus_verify_data_column_sidecar_inclusion_proof",
   py_consensus_verify_data_column_sidecar_inclusion_proof, METH_VARARGS,
   DOC_consensus_verify_data_column_sidecar_inclusion_proof},
  {"consensus_verify_data_column_sidecar_kzg_proofs",
   py_consensus_verify_data_column_sidecar_kzg_proofs, METH_VARARGS,
   DOC_consensus_verify_data_column_sidecar_kzg_proofs},
  {"consensus_verify_partial_data_column_header_inclusion_proof",
   py_consensus_verify_partial_data_column_header_inclusion_proof, METH_VARARGS,
   DOC_consensus_verify_partial_data_column_header_inclusion_proof},
  {"consensus_verify_partial_data_column_sidecar_kzg_proofs",
   py_consensus_verify_partial_data_column_sidecar_kzg_proofs, METH_VARARGS,
   DOC_consensus_verify_partial_data_column_sidecar_kzg_proofs},
  {"consensus_compute_matrix", py_consensus_compute_matrix, METH_VARARGS,
   DOC_consensus_compute_matrix},
  {"consensus_recover_matrix", py_consensus_recover_matrix, METH_VARARGS,
   DOC_consensus_recover_matrix},
  {"consensus_get_data_column_sidecars_from_block",
   py_consensus_get_data_column_sidecars_from_block, METH_VARARGS,
   DOC_consensus_get_data_column_sidecars_from_block},
  {"consensus_get_data_column_sidecars_from_column_sidecar",
   py_consensus_get_data_column_sidecars_from_column_sidecar, METH_VARARGS,
   DOC_consensus_get_data_column_sidecars_from_column_sidecar},
  {"consensus_compute_shuffled_permutation", py_consensus_compute_shuffled_permutation,
   METH_VARARGS, DOC_consensus_compute_shuffled_permutation},
  {"consensus_compute_shuffled_index", py_consensus_compute_shuffled_index, METH_VARARGS,
   DOC_consensus_compute_shuffled_index},
  {"consensus_reqresp_protocol_ids", py_consensus_reqresp_protocol_ids, METH_VARARGS,
   DOC_consensus_reqresp_protocol_ids},
  {"consensus_reqresp_parse_protocol_id", py_consensus_reqresp_parse_protocol_id, METH_VARARGS,
   DOC_consensus_reqresp_parse_protocol_id},
  {"consensus_reqresp_message", py_consensus_reqresp_message, METH_VARARGS,
   DOC_consensus_reqresp_message},
  {"consensus_compute_min_epochs_for_block_requests",
   py_consensus_compute_min_epochs_for_block_requests, METH_VARARGS,
   DOC_consensus_compute_min_epochs_for_block_requests},
  {"consensus_gossip_topics", py_consensus_gossip_topics, METH_VARARGS,
   DOC_consensus_gossip_topics},
  {"consensus_reqresp_request_bounds", py_consensus_reqresp_request_bounds, METH_VARARGS,
   DOC_consensus_reqresp_request_bounds},
  {"consensus_reqresp_response_bounds", py_consensus_reqresp_response_bounds, METH_VARARGS,
   DOC_consensus_reqresp_response_bounds},
  {"consensus_gossip_topic_bound", py_consensus_gossip_topic_bound, METH_VARARGS,
   DOC_consensus_gossip_topic_bound},
  {"consensus_compute_subnet_for_attestation", py_consensus_compute_subnet_for_attestation,
   METH_VARARGS, DOC_consensus_compute_subnet_for_attestation},
  {"consensus_compute_subnet_for_blob_sidecar", py_consensus_compute_subnet_for_blob_sidecar,
   METH_VARARGS, DOC_consensus_compute_subnet_for_blob_sidecar},
  {"consensus_compute_subnet_for_data_column_sidecar",
   py_consensus_compute_subnet_for_data_column_sidecar, METH_VARARGS,
   DOC_consensus_compute_subnet_for_data_column_sidecar},
  {"consensus_compute_subscribed_subnets", py_consensus_compute_subscribed_subnets,
   METH_VARARGS, DOC_consensus_compute_subscribed_subnets},
  {"reqresp_max_compressed_len", py_reqresp_max_compressed_len, METH_VARARGS, DOC_reqresp_max_compressed_len},
  {"reqresp_decode_payload", py_reqresp_decode_payload, METH_VARARGS, DOC_reqresp_decode_payload},
  {"reqresp_decode_response_chunk", py_reqresp_decode_response_chunk, METH_VARARGS, DOC_reqresp_decode_response_chunk},
  {"reqresp_encode_payload", py_reqresp_encode_payload, METH_VARARGS, DOC_reqresp_encode_payload},
  {"reqresp_encode_response_chunk", py_reqresp_encode_response_chunk, METH_VARARGS,
   DOC_reqresp_encode_response_chunk},
  {"block_header_hash", py_block_header_hash, METH_VARARGS, DOC_block_header_hash},
  {"block_reencode", py_block_reencode, METH_VARARGS, DOC_block_reencode},
  {"pow_block_difficulty", py_pow_block_difficulty, METH_VARARGS, DOC_pow_block_difficulty},
  {"pow_seal_hash", py_pow_seal_hash, METH_VARARGS, DOC_pow_seal_hash},
  {"pow_check", py_pow_check, METH_VARARGS, DOC_pow_check},
  {"pow_validate_ommers", py_pow_validate_ommers, METH_VARARGS, DOC_pow_validate_ommers},
  {"block_transactions_root", py_block_transactions_root, METH_VARARGS, DOC_block_transactions_root},
  {"block_withdrawals_root", py_block_withdrawals_root, METH_VARARGS, DOC_block_withdrawals_root},
  {"block_deposit_requests", py_block_deposit_requests, METH_VARARGS, DOC_block_deposit_requests},
  {"block_requests_hash", py_block_requests_hash, METH_VARARGS, DOC_block_requests_hash},
  {"block_access_list_hash", py_block_access_list_hash, METH_VARARGS, DOC_block_access_list_hash},
  {"block_access_list_check", py_block_access_list_check, METH_VARARGS, DOC_block_access_list_check},
  {"block_validate_size", py_block_validate_size, METH_VARARGS, DOC_block_validate_size},
  {"fees_base_fee_per_gas", py_fees_base_fee_per_gas, METH_VARARGS, DOC_fees_base_fee_per_gas},
  {"fees_fake_exponential", py_fees_fake_exponential, METH_VARARGS, DOC_fees_fake_exponential},
  {"fees_base_fee_per_blob_gas", py_fees_base_fee_per_blob_gas, METH_VARARGS, DOC_fees_base_fee_per_blob_gas},
  {"fees_blob_data_fee", py_fees_blob_data_fee, METH_VARARGS, DOC_fees_blob_data_fee},
  {"fees_excess_blob_gas", py_fees_excess_blob_gas, METH_VARARGS, DOC_fees_excess_blob_gas},
  {"evm_word_op", py_evm_word_op, METH_VARARGS, DOC_evm_word_op},
  {"evm_immediate_depths", py_evm_immediate_depths, METH_VARARGS, DOC_evm_immediate_depths},
  {"evm_memory_gas_cost", py_evm_memory_gas_cost, METH_VARARGS, DOC_evm_memory_gas_cost},
  {"evm_extend_memory_cost", py_evm_extend_memory_cost, METH_VARARGS, DOC_evm_extend_memory_cost},
  {"evm_extend_memory_expand_by", py_evm_extend_memory_expand_by, METH_VARARGS, DOC_evm_extend_memory_expand_by},
  {"evm_create_address", py_evm_create_address, METH_VARARGS, DOC_evm_create_address},
  {"evm_create2_address", py_evm_create2_address, METH_VARARGS, DOC_evm_create2_address},
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
  {"fork_id", py_fork_id, METH_VARARGS, DOC_fork_id},
  {"mainnet_fork_id", py_mainnet_fork_id, METH_VARARGS, DOC_mainnet_fork_id},
  {"fork_id_validate", py_fork_id_validate, METH_VARARGS, DOC_fork_id_validate},
  {"eth_message_decode", py_eth_message_decode, METH_VARARGS, DOC_eth_message_decode},
  {"eth_check_status", py_eth_check_status, METH_VARARGS, DOC_eth_check_status},
  {"eth_check_headers", py_eth_check_headers, METH_VARARGS, DOC_eth_check_headers},
  {"eth_check_pooled", py_eth_check_pooled, METH_VARARGS, DOC_eth_check_pooled},
  {"eth_wire_hash", py_eth_wire_hash, METH_VARARGS, DOC_eth_wire_hash},
  {"eth_receipts_match", py_eth_receipts_match, METH_VARARGS, DOC_eth_receipts_match},
  {"eth_access_lists_answer", py_eth_access_lists_answer, METH_VARARGS, DOC_eth_access_lists_answer},
  {"eth_check_partial_receipts", py_eth_check_partial_receipts, METH_VARARGS, DOC_eth_check_partial_receipts},
  {"snap_message_decode", py_snap_message_decode, METH_VARARGS, DOC_snap_message_decode},
  {"snap_codes_answer", py_snap_codes_answer, METH_VARARGS, DOC_snap_codes_answer},
  {"snap_access_lists_answer", py_snap_access_lists_answer, METH_VARARGS, DOC_snap_access_lists_answer},
  {"snap_full_account", py_snap_full_account, METH_VARARGS, DOC_snap_full_account},
  {"snappy_decompress", py_snappy_decompress, METH_VARARGS, DOC_snappy_decompress},
  {"snappy_compress", py_snappy_compress, METH_VARARGS, DOC_snappy_compress},
  {"snappy_decode_frames", py_snappy_decode_frames, METH_VARARGS, DOC_snappy_decode_frames},
  {"snappy_encode_frames_literal", py_snappy_encode_frames_literal, METH_VARARGS, DOC_snappy_encode_frames_literal},
  {"snappy_encode_frames", py_snappy_encode_frames, METH_VARARGS, DOC_snappy_encode_frames},
  {"snappy_masked_crc", py_snappy_masked_crc, METH_VARARGS, DOC_snappy_masked_crc},
  {"varint_encode", py_varint_encode, METH_VARARGS, DOC_varint_encode},
  {"varint_decode", py_varint_decode, METH_VARARGS, DOC_varint_decode},
  {"gossip_message_id", py_gossip_message_id, METH_VARARGS, DOC_gossip_message_id},
  {"gossip_decode_payload", py_gossip_decode_payload, METH_VARARGS, DOC_gossip_decode_payload},
  {"receipt_reencode", py_receipt_reencode, METH_VARARGS, DOC_receipt_reencode},
  {"receipt_logs_bloom", py_receipt_logs_bloom, METH_VARARGS, DOC_receipt_logs_bloom},
  {"block_make_receipts", py_block_make_receipts, METH_VARARGS, DOC_block_make_receipts},
  {"tx_type", py_tx_type, METH_VARARGS, DOC_tx_type},
  {"tx_hash", py_tx_hash, METH_VARARGS, DOC_tx_hash},
  {"tx_recover_sender", py_tx_recover_sender, METH_VARARGS, DOC_tx_recover_sender},
  {"tx_intrinsic_gas", py_tx_intrinsic_gas, METH_VARARGS, DOC_tx_intrinsic_gas},
  {"tx_check", py_tx_check, METH_VARARGS, DOC_tx_check},
  {"tx_check_in_block", py_tx_check_in_block, METH_VARARGS, DOC_tx_check_in_block},
  {"tx_run", py_tx_run, METH_VARARGS, DOC_tx_run},
  {"tx_settle", py_tx_settle, METH_VARARGS, DOC_tx_settle},
  {"tx_network_check", py_tx_network_check, METH_VARARGS, DOC_tx_network_check},
  {"rlpx_make_auth", py_rlpx_make_auth, METH_VARARGS, DOC_rlpx_make_auth},
  {"rlpx_respond", py_rlpx_respond, METH_VARARGS, DOC_rlpx_respond},
  {"rlpx_recipient_secrets", py_rlpx_recipient_secrets, METH_VARARGS, DOC_rlpx_recipient_secrets},
  {"rlpx_finish", py_rlpx_finish, METH_VARARGS, DOC_rlpx_finish},
  {"rlpx_write_frames", py_rlpx_write_frames, METH_VARARGS, DOC_rlpx_write_frames},
  {"rlpx_read_frames", py_rlpx_read_frames, METH_VARARGS, DOC_rlpx_read_frames},
  {"block_validate_header", py_block_validate_header, METH_VARARGS, DOC_block_validate_header},
  {"block_check_header", py_block_check_header, METH_VARARGS, DOC_block_check_header},
  {"block_dao_extra_data_valid", py_block_dao_extra_data_valid, METH_VARARGS,
   DOC_block_dao_extra_data_valid},
  {"state_transition", py_state_transition, METH_VARARGS, DOC_state_transition},
  {"genesis_block", py_genesis_block, METH_VARARGS, DOC_genesis_block},
  {"precompile_run", py_precompile_run, METH_VARARGS, DOC_precompile_run},
  {"precompile_price", py_precompile_price, METH_VARARGS, DOC_precompile_price},
  {"state_root", py_state_root, METH_VARARGS, DOC_state_root},
  {"state_withdrawals_root", py_state_withdrawals_root, METH_VARARGS, DOC_state_withdrawals_root},
  {"state_dao_fork_root", py_state_dao_fork_root, METH_VARARGS, DOC_state_dao_fork_root},
  {"state_rewards_root", py_state_rewards_root, METH_VARARGS, DOC_state_rewards_root},
  {"mainnet_active_fork", py_mainnet_active_fork, METH_VARARGS, DOC_mainnet_active_fork},
  {"hoodi_active_fork", py_hoodi_active_fork, METH_VARARGS, DOC_hoodi_active_fork},
  {"active_fork", py_active_fork, METH_VARARGS, DOC_active_fork},
  {"engine_new_payload", py_engine_new_payload, METH_VARARGS, DOC_engine_new_payload},
  {"engine_new_payload_on_chain", py_engine_new_payload_on_chain, METH_VARARGS,
   DOC_engine_new_payload_on_chain},
  {"engine_forkchoice_updated", py_engine_forkchoice_updated, METH_VARARGS,
   DOC_engine_forkchoice_updated},
  {"engine_prepare_execution_payload", py_engine_prepare_execution_payload, METH_VARARGS,
   DOC_engine_prepare_execution_payload},
  {"engine_prepare_execution_payload_gloas", py_engine_prepare_execution_payload_gloas,
   METH_VARARGS, DOC_engine_prepare_execution_payload_gloas},
  {"pyvalue_echo", py_pyvalue_echo, METH_VARARGS, DOC_pyvalue_echo},
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
    PRECOMPILE_ERROR = PyObject_GetAttrString(errors, "PrecompileError");
    STATE_ERROR = PyObject_GetAttrString(errors, "StateError");
    KECCAK_ERROR = PyObject_GetAttrString(errors, "KeccakError");
    ETHASH_ERROR = PyObject_GetAttrString(errors, "EthashError");
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
    GOSSIP_ERROR = PyObject_GetAttrString(errors, "GossipError");
    DISCV5_ERROR = PyObject_GetAttrString(errors, "Discv5Error");
    RLPX_ERROR = PyObject_GetAttrString(errors, "RlpxError");
    DEVP2P_ERROR = PyObject_GetAttrString(errors, "Devp2pError");
    DISCV4_ERROR = PyObject_GetAttrString(errors, "Discv4Error");
    FORK_ID_ERROR = PyObject_GetAttrString(errors, "ForkIdError");
    ETH_WIRE_ERROR = PyObject_GetAttrString(errors, "EthWireError");
    SNAP_ERROR = PyObject_GetAttrString(errors, "SnapError");
    TRANSACTION_ERROR = PyObject_GetAttrString(errors, "TransactionError");
    VRF_ERROR = PyObject_GetAttrString(errors, "VrfError");
    TRIE_ERROR = PyObject_GetAttrString(errors, "TrieError");
    EVM_ERROR = PyObject_GetAttrString(errors, "EvmError");
    FEES_ERROR = PyObject_GetAttrString(errors, "FeesError");
    ENGINE_ERROR = PyObject_GetAttrString(errors, "EngineError");
    TRANSITION_ERROR = PyObject_GetAttrString(errors, "TransitionError");
    LIGHT_CLIENT_ERROR = PyObject_GetAttrString(errors, "LightClientError");
    FORK_CHOICE_ERROR = PyObject_GetAttrString(errors, "ForkChoiceError");
    CHAIN_ERROR = PyObject_GetAttrString(errors, "ChainError");
    WEAK_SUBJECTIVITY_ERROR = PyObject_GetAttrString(errors, "WeakSubjectivityError");
    VALIDATOR_DUTY_ERROR = PyObject_GetAttrString(errors, "ValidatorDutyError");
    PROPOSER_ERROR = PyObject_GetAttrString(errors, "ProposerError");
    SLASHING_PROTECTION_ERROR = PyObject_GetAttrString(errors, "SlashingProtectionError");
    BINDING_ERROR = PyObject_GetAttrString(errors, "BindingError");
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
      res = initialize_EthLib_EthLib_Engine_Exports(1);
    }
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
      res = initialize_EthLib_EthLib_Base_Exports_Echo(1);
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
    XMSS_DIGEST_LEN = (size_t) eth_xmss_const_digest_len(lean_box(0));
    XMSS_PUBLIC_PARAM_LEN = (size_t) eth_xmss_const_public_param_len(lean_box(0));
    XMSS_RANDOMIZER_LEN = (size_t) eth_xmss_const_randomizer_len(lean_box(0));
    XMSS_CHAINS = (size_t) eth_xmss_const_chains(lean_box(0));
    XMSS_LAYER_HEIGHT = (size_t) eth_xmss_const_layer_height(lean_box(0));
    XMSS_LEAF_INDEX_SIZE = (size_t) eth_xmss_const_leaf_index_size(lean_box(0));
    SPHINCS_N = (size_t) eth_sphincs_const_n(lean_box(0));
    SPHINCS_PUBLIC_PARAM_LEN = (size_t) eth_sphincs_const_public_param_len(lean_box(0));
    SPHINCS_RANDOMIZER_LEN = (size_t) eth_sphincs_const_randomizer_len(lean_box(0));
    SPHINCS_CHAINS = (size_t) eth_sphincs_const_chains(lean_box(0));
    SPHINCS_COUNTER_LEN = (size_t) eth_sphincs_const_counter_len(lean_box(0));
    SPHINCS_TOP_HEIGHT = (size_t) eth_sphincs_const_top_height(lean_box(0));
    SPHINCS_LOWER_HEIGHT = (size_t) eth_sphincs_const_lower_height(lean_box(0));
    SPHINCS_FORS_TREES = (size_t) eth_sphincs_const_fors_trees(lean_box(0));
    SPHINCS_FORS_HEIGHT = (size_t) eth_sphincs_const_fors_height(lean_box(0));

    SECP256K1_HASH_LEN      = (size_t) eth_secp256k1_const_hash_len(lean_box(0));
    SECP256K1_SIGNATURE_LEN = (size_t) eth_secp256k1_const_signature_len(lean_box(0));
    SECP256R1_PUBLIC_KEY_LEN = (size_t) eth_secp256r1_const_public_key_len(lean_box(0));
    SECP256R1_HASH_LEN       = (size_t) eth_secp256r1_const_hash_len(lean_box(0));
    SECP256R1_SIGNATURE_LEN  = (size_t) eth_secp256r1_const_signature_len(lean_box(0));
    ENR_MAX_RECORD_SIZE     = (size_t) eth_enr_const_max_record_size(lean_box(0));
    REQRESP_MAX_PAYLOAD_SIZE = (size_t) eth_reqresp_const_max_payload_size(lean_box(0));
    REQRESP_MAX_ERROR_MESSAGE_SIZE = (size_t) eth_reqresp_const_max_error_message_size(lean_box(0));


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
  PyModule_AddIntConstant(m, "XMSS_DIGEST_LEN", XMSS_DIGEST_LEN);
  PyModule_AddIntConstant(m, "XMSS_PUBLIC_PARAM_LEN", XMSS_PUBLIC_PARAM_LEN);
  PyModule_AddIntConstant(m, "XMSS_RANDOMIZER_LEN", XMSS_RANDOMIZER_LEN);
  PyModule_AddIntConstant(m, "XMSS_CHAINS", XMSS_CHAINS);
  PyModule_AddIntConstant(m, "XMSS_LAYER_HEIGHT", XMSS_LAYER_HEIGHT);
  PyModule_AddIntConstant(m, "XMSS_LEAF_INDEX_SIZE", XMSS_LEAF_INDEX_SIZE);
  PyModule_AddIntConstant(m, "SPHINCS_N", SPHINCS_N);
  PyModule_AddIntConstant(m, "SPHINCS_PUBLIC_PARAM_LEN", SPHINCS_PUBLIC_PARAM_LEN);
  PyModule_AddIntConstant(m, "SPHINCS_RANDOMIZER_LEN", SPHINCS_RANDOMIZER_LEN);
  PyModule_AddIntConstant(m, "SPHINCS_CHAINS", SPHINCS_CHAINS);
  PyModule_AddIntConstant(m, "SPHINCS_COUNTER_LEN", SPHINCS_COUNTER_LEN);
  PyModule_AddIntConstant(m, "SPHINCS_TOP_HEIGHT", SPHINCS_TOP_HEIGHT);
  PyModule_AddIntConstant(m, "SPHINCS_LOWER_HEIGHT", SPHINCS_LOWER_HEIGHT);
  PyModule_AddIntConstant(m, "SPHINCS_FORS_TREES", SPHINCS_FORS_TREES);
  PyModule_AddIntConstant(m, "SPHINCS_FORS_HEIGHT", SPHINCS_FORS_HEIGHT);
  PyModule_AddIntConstant(m, "SECP256K1_HASH_LEN", SECP256K1_HASH_LEN);
  PyModule_AddIntConstant(m, "SECP256K1_SIGNATURE_LEN", SECP256K1_SIGNATURE_LEN);
  PyModule_AddIntConstant(m, "SECP256R1_PUBLIC_KEY_LEN", SECP256R1_PUBLIC_KEY_LEN);
  PyModule_AddIntConstant(m, "SECP256R1_HASH_LEN", SECP256R1_HASH_LEN);
  PyModule_AddIntConstant(m, "SECP256R1_SIGNATURE_LEN", SECP256R1_SIGNATURE_LEN);
  PyModule_AddIntConstant(m, "ENR_MAX_RECORD_SIZE", ENR_MAX_RECORD_SIZE);
  PyModule_AddIntConstant(m, "REQRESP_MAX_PAYLOAD_SIZE", REQRESP_MAX_PAYLOAD_SIZE);
  PyModule_AddIntConstant(m, "REQRESP_MAX_ERROR_MESSAGE_SIZE", REQRESP_MAX_ERROR_MESSAGE_SIZE);
  return m;
}

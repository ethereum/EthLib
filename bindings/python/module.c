/*
 * CPython extension entry point. Boots the Lean runtime, wires up the
 * spec-preset size constants, and assembles the method table from the
 * per-domain wrappers.
 */
#include "wrappers.h"

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
size_t REQRESP_MAX_ERROR_MESSAGE_SIZE;
size_t SECP256K1_HASH_LEN;
size_t SECP256K1_SIGNATURE_LEN;

size_t SECP256R1_PUBLIC_KEY_LEN;
size_t SECP256R1_HASH_LEN;
size_t SECP256R1_SIGNATURE_LEN;

size_t ECRECOVER_GAS;

/* ---- Lean externs: size accessors ------------------------------------ */

extern uint64_t
eth_bls_const_bytes_per_pubkey(
  uint8_t unit
);

extern uint64_t
eth_bls_const_bytes_per_signature(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_bytes_per_field_element(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_bytes_per_commitment(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_bytes_per_proof(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_field_elements_per_blob(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_bytes_per_blob(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_field_elements_per_cell(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_bytes_per_cell(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_cells_per_ext_blob(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_message_len(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_seed_len(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_pub_key_size(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_sig_size(
  uint8_t unit
);

extern uint64_t
eth_sphincs_const_message_len(
  uint8_t unit
);

extern uint64_t
eth_sphincs_const_seed_len(
  uint8_t unit
);

extern uint64_t
eth_sphincs_const_pub_key_size(
  uint8_t unit
);

extern uint64_t
eth_sphincs_const_sig_size(
  uint8_t unit
);

extern uint64_t
eth_modexp_const_length_header_bytes(
  uint8_t unit
);

extern uint64_t
eth_modexp_const_max_length_bytes(
  uint8_t unit
);

extern uint64_t
eth_ripemd160_const_output_bytes(
  uint8_t unit
);

extern uint64_t
eth_sha256_precompile_const_output_bytes(
  uint8_t unit
);

extern uint64_t
eth_secp256k1_const_hash_len(
  uint8_t unit
);

extern uint64_t
eth_secp256k1_const_signature_len(
  uint8_t unit
);

extern uint64_t
eth_secp256r1_const_public_key_len(
  uint8_t unit
);

extern uint64_t
eth_secp256r1_const_hash_len(
  uint8_t unit
);

extern uint64_t
eth_secp256r1_const_signature_len(
  uint8_t unit
);

extern uint64_t
eth_ecrecover_const_gas(
  uint8_t unit
);

extern uint64_t
eth_enr_const_max_record_size(
  uint8_t unit
);

extern uint64_t
eth_reqresp_const_max_error_message_size(
  uint8_t unit
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

/* Run an IO action and copy its inner ByteArray into `out`/`out_len`.
 * `lean_io_result_get_value` returns a *borrowed* reference; do NOT
 * `lean_dec` the inner value separately. Returns 0 on success. */
int
run_io_into_bytearray(
  lean_object* io_result,
  uint8_t* out,
  size_t out_len
) {
  if (!lean_io_result_is_ok(io_result)) {
    lean_io_result_show_error(io_result);
    lean_dec(io_result);
    return 1;
  }
  lean_object* ba = lean_io_result_get_value(io_result);
  size_t got = lean_sarray_size(ba);
  if (got != out_len) {
    lean_dec(io_result);
    return 1;
  }
  memcpy(out, lean_sarray_cptr(ba), out_len);
  lean_dec(io_result);
  return 0;
}

/* Run an IO action returning a UInt8 boolean. */
int
run_io_into_bool(
  lean_object* io_result,
  uint8_t* out_ok
) {
  if (!lean_io_result_is_ok(io_result)) {
    lean_io_result_show_error(io_result);
    lean_dec(io_result);
    return 1;
  }
  *out_ok = lean_unbox(lean_io_result_get_value(io_result));
  lean_dec(io_result);
  return 0;
}

/* `IO.Error.toString`, exported by the Lean core but absent from `lean.h`. */
extern lean_object*
lean_io_error_to_string(
  lean_object* err
);

/* Raise `ValueError` with the Lean error message of a failed IO action.
 *
 * The result is freed.
 *
 * `what` names the operation in the message. */
void
raise_io_error(
  lean_object* io_result,
  const char* what
) {
  lean_object* err = lean_io_result_get_error(io_result);
  lean_inc(err);
  lean_object* msg = lean_io_error_to_string(err);
  PyErr_Format(PyExc_ValueError, "%s: %s", what, lean_string_cstr(msg));
  lean_dec(msg);
  lean_dec(io_result);
}

/* Run an IO action and return its inner ByteArray as a Python `bytes`.
 *
 * The inner value is borrowed, so only the result is freed.
 *
 * A failed action raises `ValueError` with the Lean error message. */
PyObject*
run_io_into_pybytes(
  lean_object* io_result,
  const char* what
) {
  if (!lean_io_result_is_ok(io_result)) {
    raise_io_error(io_result, what);
    return NULL;
  }
  lean_object* ba = lean_io_result_get_value(io_result);
  PyObject* out = PyBytes_FromStringAndSize(
    (const char*) lean_sarray_cptr(ba), (Py_ssize_t) lean_sarray_size(ba));
  lean_dec(io_result);
  return out;
}

/* Run an IO action and return its inner UInt64 as a Python `int`.
 *
 * A failed action raises `ValueError` with the Lean error message. */
PyObject*
run_io_into_pyint(
  lean_object* io_result,
  const char* what
) {
  if (!lean_io_result_is_ok(io_result)) {
    raise_io_error(io_result, what);
    return NULL;
  }
  uint64_t value = lean_unbox_uint64(lean_io_result_get_value(io_result));
  lean_dec(io_result);
  return PyLong_FromUnsignedLongLong(value);
}

/* Run an IO action returning a `UInt8` boolean, as a Python `bool`.
 *
 * On failure it sets a `ValueError` with the Lean message and returns NULL. */
PyObject*
run_io_into_pybool(
  lean_object* io_result,
  const char* what
) {
  if (!lean_io_result_is_ok(io_result)) {
    raise_io_error(io_result, what);
    return NULL;
  }
  uint8_t value = lean_unbox(lean_io_result_get_value(io_result));
  lean_dec(io_result);
  if (value) Py_RETURN_TRUE; else Py_RETURN_FALSE;
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
  {"eth_aggregate_pubkeys", py_eth_aggregate_pubkeys, METH_VARARGS, NULL},
  {"eth_fast_aggregate_verify", py_eth_fast_aggregate_verify, METH_VARARGS, NULL},
  {"bls_key_gen", py_bls_key_gen, METH_VARARGS, NULL},
  {"bls_sign", py_bls_sign, METH_VARARGS, NULL},
  {"bls_verify", py_bls_verify, METH_VARARGS, NULL},
  {"bls_aggregate", py_bls_aggregate, METH_VARARGS, NULL},
  {"bls_aggregate_verify", py_bls_aggregate_verify, METH_VARARGS, NULL},
  {"bls_fast_aggregate_verify", py_bls_fast_aggregate_verify, METH_VARARGS, NULL},
  {"bls_pop_prove", py_bls_pop_prove, METH_VARARGS, NULL},
  {"bls_pop_verify", py_bls_pop_verify, METH_VARARGS, NULL},
  {"bls_expand_message_xmd", py_bls_expand_message_xmd, METH_VARARGS, NULL},
  {"bls_hash_to_g2", py_bls_hash_to_g2, METH_VARARGS, NULL},
  {"blob_to_kzg_commitment", py_blob_to_kzg_commitment, METH_VARARGS, NULL},
  {"compute_challenge", py_compute_challenge, METH_VARARGS, NULL},
  {"compute_kzg_proof", py_compute_kzg_proof, METH_VARARGS, NULL},
  {"verify_kzg_proof", py_verify_kzg_proof, METH_VARARGS, NULL},
  {"compute_blob_kzg_proof", py_compute_blob_kzg_proof, METH_VARARGS, NULL},
  {"verify_blob_kzg_proof", py_verify_blob_kzg_proof, METH_VARARGS, NULL},
  {"verify_blob_kzg_proof_batch", py_verify_blob_kzg_proof_batch, METH_VARARGS, NULL},
  {"compute_cells", py_compute_cells, METH_VARARGS, NULL},
  {"compute_cells_and_kzg_proofs", py_compute_cells_and_kzg_proofs, METH_VARARGS, NULL},
  {"compute_verify_cell_kzg_proof_batch_challenge", py_compute_verify_cell_kzg_proof_batch_challenge, METH_VARARGS, NULL},
  {"verify_cell_kzg_proof_batch", py_verify_cell_kzg_proof_batch, METH_VARARGS, NULL},
  {"recover_cells_and_kzg_proofs", py_recover_cells_and_kzg_proofs, METH_VARARGS, NULL},
  {"xmss_key_gen", py_xmss_key_gen, METH_VARARGS, NULL},
  {"xmss_sign", py_xmss_sign, METH_VARARGS, NULL},
  {"xmss_verify", py_xmss_verify, METH_VARARGS, NULL},
  {"xmss_signature_index", py_xmss_signature_index, METH_VARARGS, NULL},
  {"sphincs_key_gen", py_sphincs_key_gen, METH_VARARGS, NULL},
  {"sphincs_sign", py_sphincs_sign, METH_VARARGS, NULL},
  {"sphincs_verify", py_sphincs_verify, METH_VARARGS, NULL},
  {"modexp", py_modexp, METH_VARARGS, NULL},
  {"modexp_gas_cost", py_modexp_gas_cost, METH_VARARGS, NULL},
  {"sha256", py_sha256, METH_VARARGS, NULL},
  {"keccak256", py_keccak256, METH_VARARGS, NULL},
  {"keccak_f1600", py_keccak_f1600, METH_VARARGS, NULL},
  {"crc32c", py_crc32c, METH_VARARGS, NULL},
  {"hmac_sha256", py_hmac_sha256, METH_VARARGS, NULL},
  {"hkdf_sha256", py_hkdf_sha256, METH_VARARGS, NULL},
  {"concat_kdf_sha256", py_concat_kdf_sha256, METH_VARARGS, NULL},
  {"ripemd160", py_ripemd160, METH_VARARGS, NULL},
  {"sha256_precompile", py_sha256_precompile, METH_VARARGS, NULL},
  {"sha256_precompile_gas_cost", py_sha256_precompile_gas_cost, METH_VARARGS, NULL},
  {"secp256k1_verify", py_secp256k1_verify, METH_VARARGS, NULL},
  {"secp256k1_is_low_s", py_secp256k1_is_low_s, METH_VARARGS, NULL},
  {"secp256k1_recover", py_secp256k1_recover, METH_VARARGS, NULL},
  {"secp256k1_sign", py_secp256k1_sign, METH_VARARGS, NULL},
  {"secp256k1_ecdh", py_secp256k1_ecdh, METH_VARARGS, NULL},
  {"secp256k1_address", py_secp256k1_address, METH_VARARGS, NULL},
  {"secp256r1_verify", py_secp256r1_verify, METH_VARARGS, NULL},
  {"ecrecover", py_ecrecover, METH_VARARGS, NULL},
  {"enr_from_text", py_enr_from_text, METH_VARARGS, NULL},
  {"enr_seq", py_enr_seq, METH_VARARGS, NULL},
  {"enr_verify_v4", py_enr_verify_v4, METH_VARARGS, NULL},
  {"enr_node_id", py_enr_node_id, METH_VARARGS, NULL},
  {"enr_consensus_entries", py_enr_consensus_entries, METH_VARARGS, NULL},
  {"discv5_log_distance", py_discv5_log_distance, METH_VARARGS, NULL},
  {"discv5_ecdh", py_discv5_ecdh, METH_VARARGS, NULL},
  {"discv5_derive_keys", py_discv5_derive_keys, METH_VARARGS, NULL},
  {"discv5_id_sign", py_discv5_id_sign, METH_VARARGS, NULL},
  {"discv5_id_verify", py_discv5_id_verify, METH_VARARGS, NULL},
  {"discv5_decode_packet", py_discv5_decode_packet, METH_VARARGS, NULL},
  {"discv5_reencode_packet", py_discv5_reencode_packet, METH_VARARGS, NULL},
  {"discv5_encrypt_message", py_discv5_encrypt_message, METH_VARARGS, NULL},
  {"discv5_decrypt_message", py_discv5_decrypt_message, METH_VARARGS, NULL},
  {"consensus_preset", py_consensus_preset, METH_VARARGS, NULL},
  {"consensus_config", py_consensus_config, METH_VARARGS, NULL},
  {"consensus_parameters", py_consensus_parameters, METH_VARARGS, NULL},
  {"reqresp_max_compressed_len", py_reqresp_max_compressed_len, METH_VARARGS, NULL},
  {"reqresp_max_payload_size", py_reqresp_max_payload_size, METH_VARARGS, NULL},
  {"reqresp_decode_payload", py_reqresp_decode_payload, METH_VARARGS, NULL},
  {"reqresp_decode_response_chunk", py_reqresp_decode_response_chunk, METH_VARARGS, NULL},
  {"block_header_hash", py_block_header_hash, METH_VARARGS, NULL},
  {"block_reencode", py_block_reencode, METH_VARARGS, NULL},
  {"rlp_encode", py_rlp_encode, METH_VARARGS, NULL},
  {"rlp_decode", py_rlp_decode, METH_VARARGS, NULL},
  {"rlp_decode_as", py_rlp_decode_as, METH_VARARGS, NULL},
  {"rlpx_ecies_encrypt", py_rlpx_ecies_encrypt, METH_VARARGS, NULL},
  {"rlpx_ecies_decrypt", py_rlpx_ecies_decrypt, METH_VARARGS, NULL},
  {"snappy_decompress", py_snappy_decompress, METH_VARARGS, NULL},
  {"snappy_compress_literal", py_snappy_compress_literal, METH_VARARGS, NULL},
  {"snappy_decode_frames", py_snappy_decode_frames, METH_VARARGS, NULL},
  {"snappy_encode_frames_literal", py_snappy_encode_frames_literal, METH_VARARGS, NULL},
  {"snappy_masked_crc", py_snappy_masked_crc, METH_VARARGS, NULL},
  {"varint_encode", py_varint_encode, METH_VARARGS, NULL},
  {"varint_decode", py_varint_decode, METH_VARARGS, NULL},
  {"gossip_message_id_phase0", py_gossip_message_id_phase0, METH_VARARGS, NULL},
  {"gossip_message_id_altair", py_gossip_message_id_altair, METH_VARARGS, NULL},
  {"receipt_reencode", py_receipt_reencode, METH_VARARGS, NULL},
  {"receipt_logs_bloom", py_receipt_logs_bloom, METH_VARARGS, NULL},
  {"tx_type", py_tx_type, METH_VARARGS, NULL},
  {"tx_hash", py_tx_hash, METH_VARARGS, NULL},
  {"tx_recover_sender", py_tx_recover_sender, METH_VARARGS, NULL},
  {"tx_intrinsic_gas", py_tx_intrinsic_gas, METH_VARARGS, NULL},
  {"tx_check", py_tx_check, METH_VARARGS, NULL},
  {"precompile_run", py_precompile_run, METH_VARARGS, NULL},
  {"state_root", py_state_root, METH_VARARGS, NULL},
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
    BYTES_PER_PUBKEY        = (size_t) eth_bls_const_bytes_per_pubkey(0);
    BYTES_PER_SIGNATURE     = (size_t) eth_bls_const_bytes_per_signature(0);
    BYTES_PER_FIELD_ELEMENT = (size_t) eth_kzg_const_bytes_per_field_element(0);
    BYTES_PER_COMMITMENT    = (size_t) eth_kzg_const_bytes_per_commitment(0);
    BYTES_PER_PROOF         = (size_t) eth_kzg_const_bytes_per_proof(0);
    FIELD_ELEMENTS_PER_BLOB = (size_t) eth_kzg_const_field_elements_per_blob(0);
    BYTES_PER_BLOB          = (size_t) eth_kzg_const_bytes_per_blob(0);
    FIELD_ELEMENTS_PER_CELL = (size_t) eth_kzg_const_field_elements_per_cell(0);
    BYTES_PER_CELL          = (size_t) eth_kzg_const_bytes_per_cell(0);
    CELLS_PER_EXT_BLOB      = (size_t) eth_kzg_const_cells_per_ext_blob(0);
    XMSS_MESSAGE_LEN  = (size_t) eth_xmss_const_message_len(0);
    XMSS_SEED_LEN     = (size_t) eth_xmss_const_seed_len(0);
    XMSS_PUB_KEY_SIZE = (size_t) eth_xmss_const_pub_key_size(0);
    XMSS_SIG_SIZE     = (size_t) eth_xmss_const_sig_size(0);
    SPHINCS_MESSAGE_LEN  = (size_t) eth_sphincs_const_message_len(0);
    SPHINCS_SEED_LEN     = (size_t) eth_sphincs_const_seed_len(0);
    SPHINCS_PUB_KEY_SIZE = (size_t) eth_sphincs_const_pub_key_size(0);
    SPHINCS_SIG_SIZE     = (size_t) eth_sphincs_const_sig_size(0);

    MODEXP_LENGTH_HEADER_BYTES = (size_t) eth_modexp_const_length_header_bytes(0);
    MODEXP_MAX_LENGTH_BYTES    = (size_t) eth_modexp_const_max_length_bytes(0);
    SECP256K1_HASH_LEN      = (size_t) eth_secp256k1_const_hash_len(0);
    SECP256K1_SIGNATURE_LEN = (size_t) eth_secp256k1_const_signature_len(0);
    SECP256R1_PUBLIC_KEY_LEN = (size_t) eth_secp256r1_const_public_key_len(0);
    SECP256R1_HASH_LEN       = (size_t) eth_secp256r1_const_hash_len(0);
    SECP256R1_SIGNATURE_LEN  = (size_t) eth_secp256r1_const_signature_len(0);
    ECRECOVER_GAS           = (size_t) eth_ecrecover_const_gas(0);
    ENR_MAX_RECORD_SIZE     = (size_t) eth_enr_const_max_record_size(0);
    REQRESP_MAX_ERROR_MESSAGE_SIZE = (size_t) eth_reqresp_const_max_error_message_size(0);

    RIPEMD160_OUTPUT_BYTES = (size_t) eth_ripemd160_const_output_bytes(0);
    SHA256_PRECOMPILE_OUTPUT_BYTES = (size_t) eth_sha256_precompile_const_output_bytes(0);

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
  PyModule_AddIntConstant(m, "REQRESP_MAX_ERROR_MESSAGE_SIZE", REQRESP_MAX_ERROR_MESSAGE_SIZE);
  return m;
}

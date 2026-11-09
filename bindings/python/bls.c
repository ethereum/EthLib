/*
 * BLS handler wrappers. Each function parses Python arguments, marshals
 * them into Lean runtime objects, invokes the corresponding `@[export]`-d
 * `eth_bls_*` symbol, and unwraps the IO result back to Python.
 */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_bls_aggregate_pubkeys(
  lean_object* pubkeys
);

extern lean_object*
eth_bls_fast_aggregate_verify(
  lean_object* pubkeys,
  lean_object* msg,
  lean_object* sig
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_eth_aggregate_pubkeys(
  PyObject* self,
  PyObject* args
) {
  PyObject* pubkeys_obj;
  if (!PyArg_ParseTuple(args, "O", &pubkeys_obj)) return NULL;
  Py_ssize_t n;
  uint8_t* pks = pack_bytes_sequence(pubkeys_obj, BYTES_PER_PUBKEY, &n, "pubkey");
  if (!pks) return NULL;

  uint8_t out[BYTES_PER_PUBKEY];
  lean_object* res = eth_bls_aggregate_pubkeys(
    mk_bytearray_array(pks, n, BYTES_PER_PUBKEY));
  PyMem_Free(pks);
  if (except_into_buffer(res, BLS_ERROR, out, BYTES_PER_PUBKEY)) return NULL;
  return PyBytes_FromStringAndSize((const char*) out, BYTES_PER_PUBKEY);
}

PyObject*
py_eth_fast_aggregate_verify(
  PyObject* self,
  PyObject* args
) {
  PyObject *pubkeys_obj, *msg_obj, *sig_obj;
  if (!PyArg_ParseTuple(args, "OOO", &pubkeys_obj, &msg_obj, &sig_obj)) return NULL;
  if (!PyBytes_Check(msg_obj)) {
    PyErr_SetString(PyExc_TypeError, "message must be bytes");
    return NULL;
  }
  if (!PyBytes_Check(sig_obj)) {
    PyErr_SetString(PyExc_TypeError, "signature must be bytes");
    return NULL;
  }
  Py_ssize_t n;
  uint8_t* pks = pack_bytes_sequence(pubkeys_obj, BYTES_PER_PUBKEY, &n, "pubkey");
  /* An empty sequence gives a valid buffer with `n = 0`, so NULL always means an error. */
  if (!pks) return NULL;

  Py_ssize_t msg_len = PyBytes_GET_SIZE(msg_obj);
  Py_ssize_t sig_len = PyBytes_GET_SIZE(sig_obj);
  const uint8_t* msg = (const uint8_t*) PyBytes_AS_STRING(msg_obj);
  const uint8_t* sig = (const uint8_t*) PyBytes_AS_STRING(sig_obj);

  uint8_t ok = 0;
  lean_object* res = eth_bls_fast_aggregate_verify(
    mk_bytearray_array(pks, n, BYTES_PER_PUBKEY),
    mk_bytearray(msg, msg_len),
    mk_bytearray(sig, sig_len));
  PyMem_Free(pks);
  if (except_into_flag(res, BLS_ERROR, &ok)) return NULL;
  if (ok) Py_RETURN_TRUE; else Py_RETURN_FALSE;
}

/* ---- Draft operations ------------------------------------------------- */

extern lean_object*
eth_bls_key_gen(
  lean_object* ikm,
  lean_object* key_info
);

extern lean_object*
eth_bls_sign(
  lean_object* sk,
  lean_object* msg
);

extern lean_object*
eth_bls_verify(
  lean_object* pk,
  lean_object* msg,
  lean_object* sig
);

extern lean_object*
eth_bls_aggregate(
  lean_object* sigs
);

extern lean_object*
eth_bls_aggregate_verify(
  lean_object* pks,
  lean_object* msgs,
  lean_object* sig
);

extern lean_object*
eth_bls_fast_aggregate_verify_core(
  lean_object* pks,
  lean_object* msg,
  lean_object* sig
);

extern lean_object*
eth_bls_pop_prove(
  lean_object* sk
);

extern lean_object*
eth_bls_pop_verify(
  lean_object* pk,
  lean_object* proof
);

/* Read `bytes` of any length into a Lean `ByteArray`.
 *
 * Lean checks the length, so a wrong length gets the answer of the specification. */
static int
parse_bytes(
  PyObject* obj,
  const char* name,
  lean_object** out
) {
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s: expected bytes", name);
    return 1;
  }
  *out = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(obj), (size_t) PyBytes_GET_SIZE(obj));
  return 0;
}

/* Read a sequence of `bytes` of any lengths into a Lean `Array ByteArray`. */
int
parse_bytes_sequence(
  PyObject* seq,
  const char* name,
  lean_object** out
) {
  PyObject* fast = sequence_snapshot(seq, "expected a sequence");
  if (!fast) return 1;
  Py_ssize_t n = PySequence_Fast_GET_SIZE(fast);
  lean_object* arr = lean_alloc_array(n, n);
  for (Py_ssize_t i = 0; i < n; i++) {
    lean_object* item;
    if (parse_bytes(PySequence_Fast_GET_ITEM(fast, i), name, &item)) {
      /* Fill the unset slots, so that freeing the array is safe. */
      for (Py_ssize_t j = i; j < n; j++) lean_array_set_core(arr, j, lean_box(0));
      lean_dec(arr);
      Py_DECREF(fast);
      return 1;
    }
    lean_array_set_core(arr, i, item);
  }
  Py_DECREF(fast);
  *out = arr;
  return 0;
}

PyObject*
py_bls_key_gen(
  PyObject* self,
  PyObject* args
) {
  PyObject *ikm_obj, *info_obj;
  if (!PyArg_ParseTuple(args, "OO", &ikm_obj, &info_obj)) return NULL;
  lean_object *ikm, *info;
  if (parse_bytes(ikm_obj, "input keying material", &ikm)) return NULL;
  if (parse_bytes(info_obj, "key info", &info)) { lean_dec(ikm); return NULL; }
  return except_into_pybytes(eth_bls_key_gen(ikm, info), BLS_ERROR);
}

PyObject*
py_bls_sign(
  PyObject* self,
  PyObject* args
) {
  PyObject *sk_obj, *msg_obj;
  if (!PyArg_ParseTuple(args, "OO", &sk_obj, &msg_obj)) return NULL;
  lean_object *sk, *msg;
  if (parse_bytes(sk_obj, "secret key", &sk)) return NULL;
  if (parse_bytes(msg_obj, "message", &msg)) { lean_dec(sk); return NULL; }
  return except_into_pybytes(eth_bls_sign(sk, msg), BLS_ERROR);
}

PyObject*
py_bls_verify(
  PyObject* self,
  PyObject* args
) {
  PyObject *pk_obj, *msg_obj, *sig_obj;
  if (!PyArg_ParseTuple(args, "OOO", &pk_obj, &msg_obj, &sig_obj)) return NULL;
  lean_object *pk, *msg, *sig;
  if (parse_bytes(pk_obj, "pubkey", &pk)) return NULL;
  if (parse_bytes(msg_obj, "message", &msg)) { lean_dec(pk); return NULL; }
  if (parse_bytes(sig_obj, "signature", &sig)) { lean_dec(pk); lean_dec(msg); return NULL; }
  return except_into_pybool(eth_bls_verify(pk, msg, sig), BLS_ERROR);
}

PyObject*
py_bls_aggregate(
  PyObject* self,
  PyObject* args
) {
  PyObject* sigs_obj;
  if (!PyArg_ParseTuple(args, "O", &sigs_obj)) return NULL;
  lean_object* sigs;
  if (parse_bytes_sequence(sigs_obj, "signature", &sigs)) return NULL;
  return except_into_pybytes(eth_bls_aggregate(sigs), BLS_ERROR);
}

PyObject*
py_bls_aggregate_verify(
  PyObject* self,
  PyObject* args
) {
  PyObject *pks_obj, *msgs_obj, *sig_obj;
  if (!PyArg_ParseTuple(args, "OOO", &pks_obj, &msgs_obj, &sig_obj)) return NULL;
  lean_object *pks, *msgs, *sig;
  if (parse_bytes_sequence(pks_obj, "pubkey", &pks)) return NULL;
  if (parse_bytes_sequence(msgs_obj, "message", &msgs)) { lean_dec(pks); return NULL; }
  if (parse_bytes(sig_obj, "signature", &sig)) { lean_dec(pks); lean_dec(msgs); return NULL; }
  return except_into_pybool(eth_bls_aggregate_verify(pks, msgs, sig), BLS_ERROR);
}

PyObject*
py_bls_fast_aggregate_verify(
  PyObject* self,
  PyObject* args
) {
  PyObject *pks_obj, *msg_obj, *sig_obj;
  if (!PyArg_ParseTuple(args, "OOO", &pks_obj, &msg_obj, &sig_obj)) return NULL;
  lean_object *pks, *msg, *sig;
  if (parse_bytes_sequence(pks_obj, "pubkey", &pks)) return NULL;
  if (parse_bytes(msg_obj, "message", &msg)) { lean_dec(pks); return NULL; }
  if (parse_bytes(sig_obj, "signature", &sig)) { lean_dec(pks); lean_dec(msg); return NULL; }
  return except_into_pybool(
    eth_bls_fast_aggregate_verify_core(pks, msg, sig), BLS_ERROR);
}

PyObject*
py_bls_pop_prove(
  PyObject* self,
  PyObject* args
) {
  PyObject* sk_obj;
  if (!PyArg_ParseTuple(args, "O", &sk_obj)) return NULL;
  lean_object* sk;
  if (parse_bytes(sk_obj, "secret key", &sk)) return NULL;
  return except_into_pybytes(eth_bls_pop_prove(sk), BLS_ERROR);
}

PyObject*
py_bls_pop_verify(
  PyObject* self,
  PyObject* args
) {
  PyObject *pk_obj, *proof_obj;
  if (!PyArg_ParseTuple(args, "OO", &pk_obj, &proof_obj)) return NULL;
  lean_object *pk, *proof;
  if (parse_bytes(pk_obj, "pubkey", &pk)) return NULL;
  if (parse_bytes(proof_obj, "proof", &proof)) { lean_dec(pk); return NULL; }
  return except_into_pybool(eth_bls_pop_verify(pk, proof), BLS_ERROR);
}

/* ---- Point decoding --------------------------------------------------- */

extern lean_object*
eth_bls_decode_g1(
  lean_object* point
);

extern lean_object*
eth_bls_decode_g2(
  lean_object* point
);

PyObject*
py_bls_decode_g1(
  PyObject* self,
  PyObject* args
) {
  PyObject *point_obj;
  if (!PyArg_ParseTuple(args, "O", &point_obj)) return NULL;
  lean_object *point;
  if (parse_bytes(point_obj, "point", &point)) return NULL;
  return except_into_pybytes(eth_bls_decode_g1(point), BLS_ERROR);
}

PyObject*
py_bls_decode_g2(
  PyObject* self,
  PyObject* args
) {
  PyObject *point_obj;
  if (!PyArg_ParseTuple(args, "O", &point_obj)) return NULL;
  lean_object *point;
  if (parse_bytes(point_obj, "point", &point)) return NULL;
  return except_into_pybytes(eth_bls_decode_g2(point), BLS_ERROR);
}

/* ---- Hash to curve ---------------------------------------------------- */

extern lean_object*
eth_bls_expand_message_xmd(
  lean_object* msg,
  lean_object* dst,
  uint64_t len
);

extern lean_object*
eth_bls_hash_to_g2(
  lean_object* msg,
  lean_object* dst
);

extern lean_object*
eth_bls_pairing(
  lean_object* p,
  lean_object* q
);

PyObject*
py_bls_expand_message_xmd(
  PyObject* self,
  PyObject* args
) {
  PyObject *msg_obj, *dst_obj, *len_obj;
  if (!PyArg_ParseTuple(args, "OOO", &msg_obj, &dst_obj, &len_obj)) return NULL;
  /* A length outside [0, 2^64) raises OverflowError. */
  unsigned long long len = PyLong_AsUnsignedLongLong(len_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object *msg, *dst;
  if (parse_bytes(msg_obj, "message", &msg)) return NULL;
  if (parse_bytes(dst_obj, "dst", &dst)) { lean_dec(msg); return NULL; }
  return except_into_pybytes(
    eth_bls_expand_message_xmd(msg, dst, (uint64_t) len), BLS_ERROR);
}

PyObject*
py_bls_hash_to_g2(
  PyObject* self,
  PyObject* args
) {
  PyObject *msg_obj, *dst_obj;
  if (!PyArg_ParseTuple(args, "OO", &msg_obj, &dst_obj)) return NULL;
  lean_object *msg, *dst;
  if (parse_bytes(msg_obj, "message", &msg)) return NULL;
  if (parse_bytes(dst_obj, "dst", &dst)) { lean_dec(msg); return NULL; }
  return except_into_pybytes(eth_bls_hash_to_g2(msg, dst), BLS_ERROR);
}

PyObject*
py_bls_pairing(
  PyObject* self,
  PyObject* args
) {
  PyObject *p_obj, *q_obj;
  if (!PyArg_ParseTuple(args, "OO", &p_obj, &q_obj)) return NULL;
  lean_object *p, *q;
  if (parse_bytes(p_obj, "g1_point", &p)) return NULL;
  if (parse_bytes(q_obj, "g2_point", &q)) { lean_dec(p); return NULL; }
  return except_into_pybytes(eth_bls_pairing(p, q), BLS_ERROR);
}

/* ---- Validator key derivation ----------------------------------------- */

extern lean_object* eth_bls_derive_master_sk(lean_object* args);
extern lean_object* eth_bls_derive_child_sk(lean_object* args);
extern lean_object* eth_bls_derive_path(lean_object* args);
extern lean_object* eth_bls_withdrawal_path(lean_object* args);
extern lean_object* eth_bls_signing_path(lean_object* args);

PyObject*
py_bls_derive_master_sk(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_bls_derive_master_sk, args, 1, KEY_DERIVATION_ERROR);
}

PyObject*
py_bls_derive_child_sk(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_bls_derive_child_sk, args, 2, KEY_DERIVATION_ERROR);
}

PyObject*
py_bls_derive_path(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_bls_derive_path, args, 2, KEY_DERIVATION_ERROR);
}

PyObject*
py_bls_withdrawal_path(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_bls_withdrawal_path, args, 1, KEY_DERIVATION_ERROR);
}

PyObject*
py_bls_signing_path(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_bls_signing_path, args, 1, KEY_DERIVATION_ERROR);
}

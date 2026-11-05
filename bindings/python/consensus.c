/* Consensus-layer wrappers around the `eth_consensus_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_consensus_preset(
  lean_object* name
);

extern lean_object*
eth_consensus_config(
  lean_object* name
);

extern lean_object*
eth_consensus_parameters(
  lean_object* name,
  lean_object* fork
);

extern lean_object*
eth_consensus_get_custody_groups(
  lean_object* name,
  lean_object* node_id,
  uint64_t count
);

extern lean_object*
eth_consensus_compute_columns_for_custody_group(
  lean_object* name,
  uint64_t group
);

extern lean_object*
eth_consensus_ssz_static(
  lean_object* name,
  lean_object* fork,
  lean_object* type,
  lean_object* data
);

extern lean_object*
eth_pq_keys_ssz(
  lean_object* type,
  lean_object* data
);

extern lean_object*
eth_pq_keys_possession_signing_root(
  lean_object* name,
  lean_object* genesis_validators_root,
  lean_object* pubkey,
  lean_object* xmss_public_key
);

extern lean_object*
eth_pq_keys_is_valid_possession_proof(
  lean_object* name,
  lean_object* genesis_validators_root,
  lean_object* pubkey,
  lean_object* xmss_public_key,
  lean_object* proof
);

extern lean_object*
eth_consensus_compute_shuffled_permutation(
  lean_object* name,
  uint64_t count,
  lean_object* seed
);

extern lean_object*
eth_consensus_compute_shuffled_index(
  lean_object* name,
  uint64_t index,
  uint64_t count,
  lean_object* seed
);

extern lean_object*
eth_consensus_reqresp_protocol_ids(
  lean_object* fork
);

extern lean_object*
eth_consensus_reqresp_parse_protocol_id(
  lean_object* text
);

extern lean_object*
eth_consensus_reqresp_message(
  lean_object* name,
  lean_object* fork,
  lean_object* type,
  lean_object* data
);

extern lean_object*
eth_consensus_compute_min_epochs_for_block_requests(
  lean_object* name
);

extern lean_object*
eth_consensus_gossip_topics(
  lean_object* name,
  lean_object* fork
);

extern lean_object*
eth_consensus_compute_subnet_for_attestation(
  lean_object* name,
  uint64_t committees_per_slot,
  uint64_t slot,
  uint64_t committee_index
);

extern lean_object*
eth_consensus_compute_subnet_for_blob_sidecar(
  lean_object* name,
  lean_object* fork,
  uint64_t blob_index
);

extern lean_object*
eth_consensus_compute_subnet_for_data_column_sidecar(
  lean_object* name,
  uint64_t column_index
);

extern lean_object*
eth_consensus_compute_subscribed_subnets(
  lean_object* name,
  lean_object* node_id,
  uint64_t epoch
);

extern lean_object*
eth_consensus_merkle_proof(
  lean_object* name,
  lean_object* fork,
  lean_object* type,
  lean_object* data,
  uint64_t gindex
);

extern lean_object*
eth_consensus_verify_blob_sidecar_inclusion_proof(
  lean_object* name,
  lean_object* fork,
  lean_object* data
);

/* ---- Wrappers --------------------------------------------------------- */

/* The UTF-8 bytes of a `str` argument, or NULL with a TypeError set. */
static lean_object*
str_arg(
  PyObject* obj,
  const char* name
) {
  if (!PyUnicode_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be str", name);
    return NULL;
  }
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(obj, &len);
  if (!utf8) return NULL;
  return mk_bytearray((const uint8_t*) utf8, len);
}

PyObject*
py_consensus_preset(
  PyObject* self,
  PyObject* args
) {
  PyObject* obj;
  if (!PyArg_ParseTuple(args, "O", &obj)) return NULL;
  lean_object* name = str_arg(obj, "name");
  if (!name) return NULL;
  return except_into_pybytes(eth_consensus_preset(name), CONSENSUS_ERROR);
}

PyObject*
py_consensus_config(
  PyObject* self,
  PyObject* args
) {
  PyObject* obj;
  if (!PyArg_ParseTuple(args, "O", &obj)) return NULL;
  lean_object* name = str_arg(obj, "name");
  if (!name) return NULL;
  return except_into_pybytes(eth_consensus_config(name), CONSENSUS_ERROR);
}

PyObject*
py_consensus_parameters(
  PyObject* self,
  PyObject* args
) {
  PyObject* name_obj;
  PyObject* fork_obj;
  if (!PyArg_ParseTuple(args, "OO", &name_obj, &fork_obj)) return NULL;
  lean_object* name = str_arg(name_obj, "preset");
  if (!name) return NULL;
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    return NULL;
  }
  return except_into_pybytes(eth_consensus_parameters(name, fork), CONSENSUS_ERROR);
}

PyObject*
py_consensus_get_custody_groups(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *count_obj;
  const uint8_t* node_id;
  Py_ssize_t node_id_len;
  if (!PyArg_ParseTuple(args, "Oy#O", &name_obj, &node_id, &node_id_len, &count_obj)) return NULL;
  /* A count outside [0, 2^64) raises OverflowError. */
  unsigned long long count = PyLong_AsUnsignedLongLong(count_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  lean_object* id = mk_bytearray(node_id, node_id_len);
  return except_into_pybytes(
    eth_consensus_get_custody_groups(name, id, (uint64_t) count), CONSENSUS_ERROR);
}

PyObject*
py_consensus_compute_columns_for_custody_group(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *group_obj;
  if (!PyArg_ParseTuple(args, "OO", &name_obj, &group_obj)) return NULL;
  /* A group outside [0, 2^64) raises OverflowError. */
  unsigned long long group = PyLong_AsUnsignedLongLong(group_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  return except_into_pybytes(
    eth_consensus_compute_columns_for_custody_group(name, (uint64_t) group), CONSENSUS_ERROR);
}

PyObject*
py_consensus_ssz_static(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *type_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &name_obj, &fork_obj, &type_obj, &data_obj)) return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj) || !PyUnicode_Check(type_obj)) {
    PyErr_SetString(PyExc_TypeError, "name, fork and type must be str");
    return NULL;
  }
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  Py_ssize_t name_len, fork_len, type_len;
  const char* name_utf8 = PyUnicode_AsUTF8AndSize(name_obj, &name_len);
  if (!name_utf8) return NULL;
  const char* fork_utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &fork_len);
  if (!fork_utf8) return NULL;
  const char* type_utf8 = PyUnicode_AsUTF8AndSize(type_obj, &type_len);
  if (!type_utf8) return NULL;
  lean_object* name = mk_bytearray((const uint8_t*) name_utf8, name_len);
  lean_object* fork = mk_bytearray((const uint8_t*) fork_utf8, fork_len);
  lean_object* type = mk_bytearray((const uint8_t*) type_utf8, type_len);
  lean_object* data = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(data_obj), PyBytes_GET_SIZE(data_obj));
  return except_into_pybytes(eth_consensus_ssz_static(name, fork, type, data), SSZ_ERROR);
}

PyObject*
py_pq_keys_ssz(
  PyObject* self,
  PyObject* args
) {
  PyObject *type_obj;
  const uint8_t* data;
  Py_ssize_t data_len;
  if (!PyArg_ParseTuple(args, "Oy#", &type_obj, &data, &data_len)) return NULL;
  lean_object* type = str_arg(type_obj, "type");
  if (!type) return NULL;
  return except_into_pybytes(eth_pq_keys_ssz(type, mk_bytearray(data, data_len)), SSZ_ERROR);
}

PyObject*
py_pq_keys_possession_signing_root(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj;
  const uint8_t *root, *pubkey, *key;
  Py_ssize_t root_len, pubkey_len, key_len;
  if (!PyArg_ParseTuple(args, "Oy#y#y#", &name_obj, &root, &root_len, &pubkey, &pubkey_len,
                        &key, &key_len)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  return except_into_pybytes(
    eth_pq_keys_possession_signing_root(name, mk_bytearray(root, root_len),
      mk_bytearray(pubkey, pubkey_len), mk_bytearray(key, key_len)),
    CONSENSUS_ERROR);
}

PyObject*
py_pq_keys_is_valid_possession_proof(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj;
  const uint8_t *root, *pubkey, *key, *proof;
  Py_ssize_t root_len, pubkey_len, key_len, proof_len;
  if (!PyArg_ParseTuple(args, "Oy#y#y#y#", &name_obj, &root, &root_len, &pubkey, &pubkey_len,
                        &key, &key_len, &proof, &proof_len)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  return except_into_pybool(
    eth_pq_keys_is_valid_possession_proof(name, mk_bytearray(root, root_len),
      mk_bytearray(pubkey, pubkey_len), mk_bytearray(key, key_len),
      mk_bytearray(proof, proof_len)),
    CONSENSUS_ERROR);
}

PyObject*
py_consensus_compute_shuffled_permutation(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *count_obj;
  const uint8_t* seed;
  Py_ssize_t seed_len;
  if (!PyArg_ParseTuple(args, "OOy#", &name_obj, &count_obj, &seed, &seed_len)) return NULL;
  uint64_t count;
  if (parse_uint64(count_obj, "count", &count)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  return except_into_pybytes(
    eth_consensus_compute_shuffled_permutation(name, count, mk_bytearray(seed, seed_len)),
    CONSENSUS_ERROR);
}

PyObject*
py_consensus_compute_shuffled_index(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *index_obj, *count_obj;
  const uint8_t* seed;
  Py_ssize_t seed_len;
  if (!PyArg_ParseTuple(args, "OOOy#", &name_obj, &index_obj, &count_obj, &seed, &seed_len)) {
    return NULL;
  }
  uint64_t index, count;
  if (parse_uint64(index_obj, "index", &index)) return NULL;
  if (parse_uint64(count_obj, "count", &count)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  return except_into_pyint(
    eth_consensus_compute_shuffled_index(name, index, count, mk_bytearray(seed, seed_len)),
    CONSENSUS_ERROR);
}

PyObject*
py_consensus_gossip_topics(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj;
  if (!PyArg_ParseTuple(args, "OO", &name_obj, &fork_obj)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    return NULL;
  }
  return except_into_pybytes(eth_consensus_gossip_topics(name, fork), CONSENSUS_ERROR);
}

PyObject*
py_consensus_compute_subnet_for_attestation(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *committees_obj, *slot_obj, *index_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &name_obj, &committees_obj, &slot_obj, &index_obj)) {
    return NULL;
  }
  uint64_t committees, slot, index;
  if (parse_uint64(committees_obj, "committees_per_slot", &committees)) return NULL;
  if (parse_uint64(slot_obj, "slot", &slot)) return NULL;
  if (parse_uint64(index_obj, "committee_index", &index)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  return except_into_pyint(
    eth_consensus_compute_subnet_for_attestation(name, committees, slot, index), CONSENSUS_ERROR);
}

PyObject*
py_consensus_compute_subnet_for_blob_sidecar(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *index_obj;
  if (!PyArg_ParseTuple(args, "OOO", &name_obj, &fork_obj, &index_obj)) return NULL;
  uint64_t index;
  if (parse_uint64(index_obj, "blob_index", &index)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    return NULL;
  }
  return except_into_pyint(
    eth_consensus_compute_subnet_for_blob_sidecar(name, fork, index), CONSENSUS_ERROR);
}

PyObject*
py_consensus_compute_subnet_for_data_column_sidecar(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *index_obj;
  if (!PyArg_ParseTuple(args, "OO", &name_obj, &index_obj)) return NULL;
  uint64_t index;
  if (parse_uint64(index_obj, "column_index", &index)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  return except_into_pyint(
    eth_consensus_compute_subnet_for_data_column_sidecar(name, index), CONSENSUS_ERROR);
}

PyObject*
py_consensus_compute_subscribed_subnets(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *epoch_obj;
  const uint8_t* node_id;
  Py_ssize_t node_id_len;
  if (!PyArg_ParseTuple(args, "Oy#O", &name_obj, &node_id, &node_id_len, &epoch_obj)) return NULL;
  uint64_t epoch;
  if (parse_uint64(epoch_obj, "epoch", &epoch)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  return except_into_pybytes(
    eth_consensus_compute_subscribed_subnets(name, mk_bytearray(node_id, node_id_len), epoch),
    CONSENSUS_ERROR);
}

PyObject*
py_consensus_reqresp_protocol_ids(
  PyObject* self,
  PyObject* args
) {
  PyObject* fork_obj;
  if (!PyArg_ParseTuple(args, "O", &fork_obj)) return NULL;
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) return NULL;
  return except_into_pybytes(eth_consensus_reqresp_protocol_ids(fork), CONSENSUS_ERROR);
}

PyObject*
py_consensus_reqresp_parse_protocol_id(
  PyObject* self,
  PyObject* args
) {
  PyObject* text_obj;
  if (!PyArg_ParseTuple(args, "O", &text_obj)) return NULL;
  lean_object* text = str_arg(text_obj, "text");
  if (!text) return NULL;
  return except_into_pybytes(eth_consensus_reqresp_parse_protocol_id(text), CONSENSUS_ERROR);
}

PyObject*
py_consensus_reqresp_message(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *type_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &name_obj, &fork_obj, &type_obj, &data_obj)) return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj) || !PyUnicode_Check(type_obj)) {
    PyErr_SetString(PyExc_TypeError, "name, fork and type must be str");
    return NULL;
  }
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  Py_ssize_t name_len, fork_len, type_len;
  const char* name_utf8 = PyUnicode_AsUTF8AndSize(name_obj, &name_len);
  if (!name_utf8) return NULL;
  const char* fork_utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &fork_len);
  if (!fork_utf8) return NULL;
  const char* type_utf8 = PyUnicode_AsUTF8AndSize(type_obj, &type_len);
  if (!type_utf8) return NULL;
  lean_object* name = mk_bytearray((const uint8_t*) name_utf8, name_len);
  lean_object* fork = mk_bytearray((const uint8_t*) fork_utf8, fork_len);
  lean_object* type = mk_bytearray((const uint8_t*) type_utf8, type_len);
  lean_object* data = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(data_obj), PyBytes_GET_SIZE(data_obj));
  return except_into_pybytes(eth_consensus_reqresp_message(name, fork, type, data), SSZ_ERROR);
}

PyObject*
py_consensus_compute_min_epochs_for_block_requests(
  PyObject* self,
  PyObject* args
) {
  PyObject* name_obj;
  if (!PyArg_ParseTuple(args, "O", &name_obj)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  return except_into_pyint(
    eth_consensus_compute_min_epochs_for_block_requests(name), CONSENSUS_ERROR);
}

PyObject*
py_consensus_merkle_proof(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *type_obj, *data_obj, *gindex_obj;
  if (!PyArg_ParseTuple(args, "OOOOO", &name_obj, &fork_obj, &type_obj, &data_obj, &gindex_obj))
    return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj) || !PyUnicode_Check(type_obj)) {
    PyErr_SetString(PyExc_TypeError, "name, fork and type must be str");
    return NULL;
  }
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  /* A generalized index outside [0, 2^64) raises OverflowError. */
  unsigned long long gindex = PyLong_AsUnsignedLongLong(gindex_obj);
  if (PyErr_Occurred()) return NULL;
  Py_ssize_t name_len, fork_len, type_len;
  const char* name_utf8 = PyUnicode_AsUTF8AndSize(name_obj, &name_len);
  if (!name_utf8) return NULL;
  const char* fork_utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &fork_len);
  if (!fork_utf8) return NULL;
  const char* type_utf8 = PyUnicode_AsUTF8AndSize(type_obj, &type_len);
  if (!type_utf8) return NULL;
  lean_object* name = mk_bytearray((const uint8_t*) name_utf8, name_len);
  lean_object* fork = mk_bytearray((const uint8_t*) fork_utf8, fork_len);
  lean_object* type = mk_bytearray((const uint8_t*) type_utf8, type_len);
  lean_object* data = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(data_obj), PyBytes_GET_SIZE(data_obj));
  return except_into_pybytes(
    eth_consensus_merkle_proof(name, fork, type, data, (uint64_t) gindex), SSZ_ERROR);
}

PyObject*
py_consensus_verify_blob_sidecar_inclusion_proof(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOO", &name_obj, &fork_obj, &data_obj)) return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "name and fork must be str");
    return NULL;
  }
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  Py_ssize_t name_len, fork_len;
  const char* name_utf8 = PyUnicode_AsUTF8AndSize(name_obj, &name_len);
  if (!name_utf8) return NULL;
  const char* fork_utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &fork_len);
  if (!fork_utf8) return NULL;
  lean_object* name = mk_bytearray((const uint8_t*) name_utf8, name_len);
  lean_object* fork = mk_bytearray((const uint8_t*) fork_utf8, fork_len);
  lean_object* data = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(data_obj), PyBytes_GET_SIZE(data_obj));
  return except_into_pybool(
    eth_consensus_verify_blob_sidecar_inclusion_proof(name, fork, data), SSZ_ERROR);
}

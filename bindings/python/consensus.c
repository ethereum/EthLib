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
eth_consensus_process_operation(
  lean_object* name,
  lean_object* fork,
  lean_object* handler,
  lean_object* pre,
  lean_object* operation,
  lean_object* config,
  uint8_t verify
);

extern lean_object*
eth_consensus_process_epoch(
  lean_object* name,
  lean_object* fork,
  lean_object* handler,
  lean_object* pre,
  lean_object* config
);

extern lean_object*
eth_consensus_rewards_deltas(
  lean_object* name,
  lean_object* fork,
  lean_object* component,
  lean_object* pre,
  lean_object* config
);

extern lean_object*
eth_consensus_upgrade_state(
  lean_object* name,
  lean_object* fork,
  lean_object* pre,
  lean_object* config,
  uint8_t verify
);

extern lean_object*
eth_consensus_verify_blob_sidecar_inclusion_proof(
  lean_object* name,
  lean_object* fork,
  lean_object* data
);

extern lean_object* eth_consensus_verify_data_column_sidecar(
  lean_object* name, lean_object* fork, lean_object* data, lean_object* block,
  lean_object* config);
extern lean_object* eth_consensus_verify_data_column_sidecar_inclusion_proof(
  lean_object* name, lean_object* fork, lean_object* data);
extern lean_object* eth_consensus_verify_data_column_sidecar_kzg_proofs(
  lean_object* name, lean_object* fork, lean_object* data, lean_object* block);
extern lean_object* eth_consensus_verify_partial_data_column_header_inclusion_proof(
  lean_object* name, lean_object* fork, lean_object* data);
extern lean_object* eth_consensus_verify_partial_data_column_sidecar_kzg_proofs(
  lean_object* name, lean_object* fork, lean_object* data, lean_object* commitments,
  uint64_t column_index);
extern lean_object* eth_consensus_compute_matrix(lean_object* blobs);
extern lean_object* eth_consensus_recover_matrix(lean_object* entries, uint64_t blob_count);
extern lean_object* eth_consensus_get_data_column_sidecars_from_block(
  lean_object* name, lean_object* fork, lean_object* block, lean_object* rows);
extern lean_object* eth_consensus_get_data_column_sidecars_from_column_sidecar(
  lean_object* name, lean_object* fork, lean_object* sidecar, lean_object* rows);
extern lean_object* eth_consensus_light_client_sync(
  lean_object* name, lean_object* fork, lean_object* bootstrap_fork, lean_object* config,
  lean_object* trusted, lean_object* genesis_validators_root, lean_object* bootstrap,
  lean_object* steps);
extern lean_object* eth_consensus_block_to_light_client_header(
  lean_object* name, lean_object* fork, lean_object* config, lean_object* block);
extern lean_object* eth_consensus_light_client_update_proofs(
  lean_object* name, lean_object* fork, lean_object* type, lean_object* config,
  lean_object* data);
extern lean_object* eth_consensus_is_better_update(
  lean_object* name, lean_object* fork, lean_object* new_update, lean_object* old_update);
extern lean_object* eth_consensus_compute_fork_digest(
  lean_object* name, lean_object* config, lean_object* genesis_validators_root, uint64_t epoch);

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

/* The bytes of a `bytes` argument that the caller has checked. */
static lean_object*
bytes_arg(
  PyObject* obj
) {
  return mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), PyBytes_GET_SIZE(obj));
}

/* Read a preset name, a fork name and `count` byte strings (one to three) into `data`,
   or set an error and return 0. */
static int
name_fork_bytes_args(
  PyObject* args,
  int count,
  lean_object** name,
  lean_object** fork,
  lean_object** data
) {
  PyObject *name_obj, *fork_obj, *data_obj[3] = {NULL, NULL, NULL};
  if (!PyArg_UnpackTuple(args, "args", 2 + count, 2 + count, &name_obj, &fork_obj,
                         &data_obj[0], &data_obj[1], &data_obj[2])) return 0;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "name and fork must be str");
    return 0;
  }
  for (int i = 0; i < count; i++) {
    if (!PyBytes_Check(data_obj[i])) {
      PyErr_SetString(PyExc_TypeError, "the data must be bytes");
      return 0;
    }
  }
  *name = str_arg(name_obj, "name");
  if (!*name) return 0;
  *fork = str_arg(fork_obj, "fork");
  if (!*fork) {
    lean_dec(*name);
    return 0;
  }
  for (int i = 0; i < count; i++) data[i] = bytes_arg(data_obj[i]);
  return 1;
}

PyObject*
py_consensus_verify_data_column_sidecar(
  PyObject* self,
  PyObject* args
) {
  lean_object *name, *fork, *data[3];
  if (!name_fork_bytes_args(args, 3, &name, &fork, data)) return NULL;
  return except_into_pybool(
    eth_consensus_verify_data_column_sidecar(name, fork, data[0], data[1], data[2]), SSZ_ERROR);
}

PyObject*
py_consensus_verify_data_column_sidecar_inclusion_proof(
  PyObject* self,
  PyObject* args
) {
  lean_object *name, *fork, *data;
  if (!name_fork_bytes_args(args, 1, &name, &fork, &data)) return NULL;
  return except_into_pybool(
    eth_consensus_verify_data_column_sidecar_inclusion_proof(name, fork, data), SSZ_ERROR);
}

PyObject*
py_consensus_verify_data_column_sidecar_kzg_proofs(
  PyObject* self,
  PyObject* args
) {
  lean_object *name, *fork, *data[2];
  if (!name_fork_bytes_args(args, 2, &name, &fork, data)) return NULL;
  return except_into_pybool(
    eth_consensus_verify_data_column_sidecar_kzg_proofs(name, fork, data[0], data[1]), KZG_ERROR);
}

PyObject*
py_consensus_verify_partial_data_column_header_inclusion_proof(
  PyObject* self,
  PyObject* args
) {
  lean_object *name, *fork, *data;
  if (!name_fork_bytes_args(args, 1, &name, &fork, &data)) return NULL;
  return except_into_pybool(
    eth_consensus_verify_partial_data_column_header_inclusion_proof(name, fork, data),
    SSZ_ERROR);
}

PyObject*
py_consensus_verify_partial_data_column_sidecar_kzg_proofs(
  PyObject* self,
  PyObject* args
) {
  if (!PyTuple_Check(args) || PyTuple_GET_SIZE(args) != 5) {
    PyErr_SetString(PyExc_TypeError, "function takes exactly 5 arguments");
    return NULL;
  }
  /* Read the column index before any Lean object exists. */
  uint64_t column_index;
  if (parse_uint64(PyTuple_GET_ITEM(args, 4), "column_index", &column_index) < 0) return NULL;
  PyObject* leading = PyTuple_GetSlice(args, 0, 4);
  if (!leading) return NULL;
  lean_object *name, *fork, *data[2];
  int read = name_fork_bytes_args(leading, 2, &name, &fork, data);
  Py_DECREF(leading);
  if (!read) return NULL;
  return except_into_pybool(
    eth_consensus_verify_partial_data_column_sidecar_kzg_proofs(
      name, fork, data[0], data[1], column_index),
    KZG_ERROR);
}

PyObject*
py_consensus_compute_matrix(
  PyObject* self,
  PyObject* args
) {
  PyObject* blobs_obj;
  if (!PyArg_ParseTuple(args, "O", &blobs_obj)) return NULL;
  if (!PyBytes_Check(blobs_obj)) {
    PyErr_SetString(PyExc_TypeError, "blobs must be bytes");
    return NULL;
  }
  return except_into_pybytes(eth_consensus_compute_matrix(bytes_arg(blobs_obj)), KZG_ERROR);
}

PyObject*
py_consensus_recover_matrix(
  PyObject* self,
  PyObject* args
) {
  PyObject *entries_obj, *count_obj;
  if (!PyArg_ParseTuple(args, "OO", &entries_obj, &count_obj)) return NULL;
  if (!PyBytes_Check(entries_obj)) {
    PyErr_SetString(PyExc_TypeError, "entries must be bytes");
    return NULL;
  }
  /* A count outside [0, 2^64) raises OverflowError. */
  unsigned long long count = PyLong_AsUnsignedLongLong(count_obj);
  if (PyErr_Occurred()) return NULL;
  return except_into_pybytes(
    eth_consensus_recover_matrix(bytes_arg(entries_obj), (uint64_t) count), KZG_ERROR);
}

PyObject*
py_consensus_get_data_column_sidecars_from_block(
  PyObject* self,
  PyObject* args
) {
  lean_object *name, *fork, *data[2];
  if (!name_fork_bytes_args(args, 2, &name, &fork, data)) return NULL;
  return except_into_pybytes(
    eth_consensus_get_data_column_sidecars_from_block(name, fork, data[0], data[1]), SSZ_ERROR);
}

PyObject*
py_consensus_get_data_column_sidecars_from_column_sidecar(
  PyObject* self,
  PyObject* args
) {
  lean_object *name, *fork, *data[2];
  if (!name_fork_bytes_args(args, 2, &name, &fork, data)) return NULL;
  return except_into_pybytes(
    eth_consensus_get_data_column_sidecars_from_column_sidecar(name, fork, data[0], data[1]),
    SSZ_ERROR);
}

PyObject*
py_consensus_process_operation(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *handler_obj, *pre_obj, *operation_obj, *config_obj;
  int verify;
  if (!PyArg_ParseTuple(args, "OOOOOOp", &name_obj, &fork_obj, &handler_obj, &pre_obj,
                        &operation_obj, &config_obj, &verify)) return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj) || !PyUnicode_Check(handler_obj)) {
    PyErr_SetString(PyExc_TypeError, "name, fork and handler must be str");
    return NULL;
  }
  if (!PyBytes_Check(pre_obj) || !PyBytes_Check(operation_obj) || !PyBytes_Check(config_obj)) {
    PyErr_SetString(PyExc_TypeError, "pre, operation and config must be bytes");
    return NULL;
  }
  Py_ssize_t name_len, fork_len, handler_len;
  const char* name_utf8 = PyUnicode_AsUTF8AndSize(name_obj, &name_len);
  if (!name_utf8) return NULL;
  const char* fork_utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &fork_len);
  if (!fork_utf8) return NULL;
  const char* handler_utf8 = PyUnicode_AsUTF8AndSize(handler_obj, &handler_len);
  if (!handler_utf8) return NULL;
  lean_object* name = mk_bytearray((const uint8_t*) name_utf8, name_len);
  lean_object* fork = mk_bytearray((const uint8_t*) fork_utf8, fork_len);
  lean_object* handler = mk_bytearray((const uint8_t*) handler_utf8, handler_len);
  lean_object* pre = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(pre_obj), PyBytes_GET_SIZE(pre_obj));
  lean_object* operation = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(operation_obj), PyBytes_GET_SIZE(operation_obj));
  lean_object* config = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(config_obj), PyBytes_GET_SIZE(config_obj));
  return except_into_pybytes(
    eth_consensus_process_operation(name, fork, handler, pre, operation, config,
                                    (uint8_t) verify),
    TRANSITION_ERROR);
}

/* Read `strings` str arguments, then `count` byte strings, or set an error and return 0. */
static int
strs_bytes_args(
  PyObject* args,
  int strings,
  int count,
  lean_object** out
) {
  Py_ssize_t total = PyTuple_Size(args);
  if (total != strings + count) {
    PyErr_Format(PyExc_TypeError, "expected %d arguments", strings + count);
    return 0;
  }
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  for (Py_ssize_t i = 0; i < total; i++) {
    PyObject* item = PyTuple_GET_ITEM(args, i);
    if (i < strings ? !PyUnicode_Check(item) : !PyBytes_Check(item)) {
      PyErr_SetString(PyExc_TypeError,
                      i < strings ? "the names must be str" : "the data must be bytes");
      return 0;
    }
  }
  for (Py_ssize_t i = 0; i < total; i++) {
    PyObject* item = PyTuple_GET_ITEM(args, i);
    if (i >= strings) {
      out[i] = bytes_arg(item);
    } else if (!(out[i] = str_arg(item, "name"))) {
      for (Py_ssize_t j = 0; j < i; j++) lean_dec(out[j]);
      return 0;
    }
  }
  return 1;
}

PyObject*
py_consensus_light_client_sync(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[8];
  if (!strs_bytes_args(args, 3, 5, a)) return NULL;
  return except_into_pybytes(
    eth_consensus_light_client_sync(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]),
    LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_block_to_light_client_header(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[4];
  if (!strs_bytes_args(args, 2, 2, a)) return NULL;
  return except_into_pybytes(
    eth_consensus_block_to_light_client_header(a[0], a[1], a[2], a[3]), LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_light_client_update_proofs(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[5];
  if (!strs_bytes_args(args, 3, 2, a)) return NULL;
  return except_into_pybool(
    eth_consensus_light_client_update_proofs(a[0], a[1], a[2], a[3], a[4]), LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_is_better_update(
  PyObject* self,
  PyObject* args
) {
  lean_object *name, *fork, *updates[2];
  if (!name_fork_bytes_args(args, 2, &name, &fork, updates)) return NULL;
  return except_into_pybool(
    eth_consensus_is_better_update(name, fork, updates[0], updates[1]), LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_compute_fork_digest(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *config_obj, *root_obj;
  unsigned long long epoch;
  if (!PyArg_ParseTuple(args, "OOOK", &name_obj, &config_obj, &root_obj, &epoch)) return NULL;
  if (!PyUnicode_Check(name_obj)) {
    PyErr_SetString(PyExc_TypeError, "name must be str");
    return NULL;
  }
  if (!PyBytes_Check(config_obj) || !PyBytes_Check(root_obj)) {
    PyErr_SetString(PyExc_TypeError, "the data must be bytes");
    return NULL;
  }
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  return except_into_pybytes(
    eth_consensus_compute_fork_digest(name, bytes_arg(config_obj), bytes_arg(root_obj),
                                      (uint64_t) epoch),
    SSZ_ERROR);
}

PyObject*
py_consensus_process_epoch(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *handler_obj, *pre_obj, *config_obj;
  if (!PyArg_ParseTuple(args, "OOOOO", &name_obj, &fork_obj, &handler_obj, &pre_obj,
                        &config_obj)) return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj) || !PyUnicode_Check(handler_obj)) {
    PyErr_SetString(PyExc_TypeError, "name, fork and handler must be str");
    return NULL;
  }
  if (!PyBytes_Check(pre_obj) || !PyBytes_Check(config_obj)) {
    PyErr_SetString(PyExc_TypeError, "pre and config must be bytes");
    return NULL;
  }
  Py_ssize_t name_len, fork_len, handler_len;
  const char* name_utf8 = PyUnicode_AsUTF8AndSize(name_obj, &name_len);
  if (!name_utf8) return NULL;
  const char* fork_utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &fork_len);
  if (!fork_utf8) return NULL;
  const char* handler_utf8 = PyUnicode_AsUTF8AndSize(handler_obj, &handler_len);
  if (!handler_utf8) return NULL;
  lean_object* name = mk_bytearray((const uint8_t*) name_utf8, name_len);
  lean_object* fork = mk_bytearray((const uint8_t*) fork_utf8, fork_len);
  lean_object* handler = mk_bytearray((const uint8_t*) handler_utf8, handler_len);
  lean_object* pre = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(pre_obj), PyBytes_GET_SIZE(pre_obj));
  lean_object* config = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(config_obj), PyBytes_GET_SIZE(config_obj));
  return except_into_pybytes(
    eth_consensus_process_epoch(name, fork, handler, pre, config), TRANSITION_ERROR);
}

PyObject*
py_consensus_rewards_deltas(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *component_obj, *pre_obj, *config_obj;
  if (!PyArg_ParseTuple(args, "OOOOO", &name_obj, &fork_obj, &component_obj, &pre_obj,
                        &config_obj)) return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj) ||
      !PyUnicode_Check(component_obj)) {
    PyErr_SetString(PyExc_TypeError, "name, fork and component must be str");
    return NULL;
  }
  if (!PyBytes_Check(pre_obj) || !PyBytes_Check(config_obj)) {
    PyErr_SetString(PyExc_TypeError, "pre and config must be bytes");
    return NULL;
  }
  Py_ssize_t name_len, fork_len, component_len;
  const char* name_utf8 = PyUnicode_AsUTF8AndSize(name_obj, &name_len);
  if (!name_utf8) return NULL;
  const char* fork_utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &fork_len);
  if (!fork_utf8) return NULL;
  const char* component_utf8 = PyUnicode_AsUTF8AndSize(component_obj, &component_len);
  if (!component_utf8) return NULL;
  lean_object* name = mk_bytearray((const uint8_t*) name_utf8, name_len);
  lean_object* fork = mk_bytearray((const uint8_t*) fork_utf8, fork_len);
  lean_object* component = mk_bytearray((const uint8_t*) component_utf8, component_len);
  lean_object* pre = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(pre_obj), PyBytes_GET_SIZE(pre_obj));
  lean_object* config = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(config_obj), PyBytes_GET_SIZE(config_obj));
  return except_into_pybytes(
    eth_consensus_rewards_deltas(name, fork, component, pre, config), TRANSITION_ERROR);
}

PyObject*
py_consensus_upgrade_state(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *pre_obj, *config_obj;
  int verify;
  if (!PyArg_ParseTuple(args, "OOOOp", &name_obj, &fork_obj, &pre_obj, &config_obj, &verify))
    return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "name and fork must be str");
    return NULL;
  }
  if (!PyBytes_Check(pre_obj) || !PyBytes_Check(config_obj)) {
    PyErr_SetString(PyExc_TypeError, "pre and config must be bytes");
    return NULL;
  }
  Py_ssize_t name_len, fork_len;
  const char* name_utf8 = PyUnicode_AsUTF8AndSize(name_obj, &name_len);
  if (!name_utf8) return NULL;
  const char* fork_utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &fork_len);
  if (!fork_utf8) return NULL;
  lean_object* name = mk_bytearray((const uint8_t*) name_utf8, name_len);
  lean_object* fork = mk_bytearray((const uint8_t*) fork_utf8, fork_len);
  lean_object* pre = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(pre_obj), PyBytes_GET_SIZE(pre_obj));
  lean_object* config = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(config_obj), PyBytes_GET_SIZE(config_obj));
  return except_into_pybytes(
    eth_consensus_upgrade_state(name, fork, pre, config, (uint8_t) verify), TRANSITION_ERROR);
}

/* Consensus-layer wrappers around the `eth_consensus_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_engine_prepare_execution_payload(
  lean_object* args
);

extern lean_object*
eth_engine_prepare_execution_payload_gloas(lean_object* args);

extern lean_object*
eth_consensus_get_execution_payload_bid(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* payload,
  lean_object* requests, lean_object* commitments, lean_object* fee_recipient,
  lean_object* inclusion_list_bits, uint64_t slot, uint64_t builder_index, uint64_t value);

extern lean_object*
eth_consensus_get_self_built_execution_payload_bid(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* payload,
  lean_object* requests, lean_object* commitments, lean_object* fee_recipient,
  lean_object* inclusion_list_bits);

extern lean_object*
eth_consensus_get_execution_payload_envelope(
  lean_object* name, lean_object* fork, lean_object* block, lean_object* payload,
  lean_object* requests);

extern lean_object*
eth_consensus_preset(
  lean_object* args
);

extern lean_object*
eth_consensus_config(
  lean_object* args
);

extern lean_object*
eth_consensus_parameters(
  lean_object* args
);

extern lean_object*
eth_consensus_get_custody_groups(
  lean_object* args
);

extern lean_object*
eth_consensus_compute_columns_for_custody_group(
  lean_object* args
);

extern lean_object*
eth_consensus_ssz_static(
  lean_object* args
);

extern lean_object*
eth_pq_keys_ssz(
  lean_object* args
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
  lean_object* args
);

extern lean_object*
eth_consensus_compute_shuffled_index(
  lean_object* args
);

extern lean_object*
eth_consensus_reqresp_protocol_ids(
  lean_object* args
);

extern lean_object*
eth_consensus_reqresp_parse_protocol_id(
  lean_object* args
);

extern lean_object*
eth_consensus_reqresp_message(
  lean_object* args
);

extern lean_object*
eth_consensus_compute_min_epochs_for_block_requests(
  lean_object* name
);

extern lean_object*
eth_consensus_gossip_topics(
  lean_object* args
);

extern lean_object*
eth_consensus_reqresp_request_bounds(
  lean_object* args
);

extern lean_object*
eth_consensus_reqresp_response_bounds(
  lean_object* args
);

extern lean_object*
eth_consensus_gossip_topic_bound(
  lean_object* name,
  lean_object* fork,
  lean_object* topic
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
  lean_object* args
);

extern lean_object*
eth_consensus_merkle_proof(
  lean_object* args
);

extern lean_object*
eth_consensus_process_operation(
  lean_object* args
);

extern lean_object*
eth_consensus_process_epoch(
  lean_object* args
);

extern lean_object*
eth_consensus_rewards_deltas(
  lean_object* args
);

extern lean_object*
eth_consensus_rewards_deltas_batch(
  lean_object* args
);

extern lean_object*
eth_consensus_process_slots(
  lean_object* args
);

extern lean_object*
eth_consensus_state_transition(
  lean_object* args
);

extern lean_object*
eth_consensus_initialize_genesis(
  lean_object* args
);

extern lean_object*
eth_consensus_is_valid_genesis_state(
  lean_object* args
);

extern lean_object*
eth_consensus_compute_weak_subjectivity_period(
  lean_object* args
);

extern lean_object*
eth_consensus_is_within_weak_subjectivity_period(
  lean_object* args
);

extern lean_object*
eth_consensus_get_committee_assignment(
  lean_object* args
);

extern lean_object*
eth_consensus_is_proposer(
  lean_object* args
);

extern lean_object*
eth_consensus_is_assigned_to_sync_committee(
  lean_object* args
);

extern lean_object*
eth_consensus_compute_subnets_for_sync_committee(
  lean_object* args
);

extern lean_object*
eth_consensus_get_ptc_assignment(
  lean_object* args
);

extern lean_object*
eth_consensus_get_upcoming_proposal_slots(
  lean_object* args
);

extern lean_object*
eth_consensus_get_validator_signature(
  lean_object* args
);

extern lean_object*
eth_consensus_get_eth1_vote(
  lean_object* args
);

extern lean_object*
eth_consensus_get_eth1_pending_deposit_count(
  lean_object* args
);

extern lean_object*
eth_consensus_compute_new_state_root(
  lean_object* args
);

extern lean_object*
eth_consensus_compute_on_chain_aggregate(
  lean_object* name, lean_object* fork, lean_object* aggregates);

extern lean_object*
eth_consensus_get_attestation_data(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* head_root,
  uint64_t head_slot, uint64_t committee_index, uint64_t payload_status);

extern lean_object*
eth_consensus_get_aggregate_signature(
  lean_object* name, lean_object* fork, lean_object* attestations);

extern lean_object*
eth_consensus_construct_attestation(
  lean_object* args
);

extern lean_object*
eth_consensus_construct_single_attestation(
  lean_object* args
);

extern lean_object*
eth_consensus_construct_aggregate(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* data,
  lean_object* attestations);

extern lean_object*
eth_consensus_construct_aggregate_of_single_attestations(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* data,
  uint64_t committee_index, lean_object* singles);

extern lean_object*
eth_consensus_construct_sync_committee_contribution(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* committee,
  lean_object* block_root, uint64_t subcommittee_index, lean_object* messages);

extern lean_object*
eth_consensus_process_sync_committee_contributions(
  lean_object* name, lean_object* fork, lean_object* contributions);

extern lean_object*
eth_consensus_read_slashing_interchange(lean_object* text);

extern lean_object*
eth_consensus_import_slashing_interchange(lean_object* held, lean_object* file);

extern lean_object*
eth_consensus_check_block_signing(
  lean_object* text, lean_object* pubkey, uint64_t slot, lean_object* signing_root);

extern lean_object*
eth_consensus_check_attestation_signing(
  lean_object* text, lean_object* pubkey, uint64_t source_epoch, uint64_t target_epoch,
  lean_object* signing_root);

extern lean_object*
eth_consensus_record_block_signing(
  lean_object* text, lean_object* pubkey, uint64_t slot, lean_object* signing_root);

extern lean_object*
eth_consensus_record_attestation_signing(
  lean_object* text, lean_object* pubkey, uint64_t source_epoch, uint64_t target_epoch,
  lean_object* signing_root);

extern lean_object*
eth_consensus_is_execution_block(lean_object* name, lean_object* fork, lean_object* block);

extern lean_object*
eth_consensus_is_optimistic_candidate_block(
  lean_object* name, lean_object* fork, lean_object* blocks, uint64_t current_slot,
  uint64_t safe_slots, lean_object* block);

extern lean_object*
eth_consensus_latest_verified_ancestor(
  lean_object* args
);

extern lean_object*
eth_consensus_on_valid_payload(
  lean_object* args
);

extern lean_object*
eth_consensus_on_invalidated_payload(
  lean_object* args
);

extern lean_object*
eth_consensus_is_optimistic_restricted_domain(lean_object* domain_type);

extern lean_object*
eth_consensus_get_execution_requests(
  lean_object* name, lean_object* fork, lean_object* requests);

extern lean_object*
eth_consensus_get_validators_custody_requirement(
  lean_object* args
);

extern lean_object*
eth_consensus_state_transition_across(
  lean_object* args
);

extern lean_object*
eth_consensus_state_transitions(
  lean_object* args
);

extern lean_object*
eth_consensus_state_transitions_across(
  lean_object* args
);

extern lean_object*
eth_consensus_upgrade_state(
  lean_object* args
);

extern lean_object*
eth_consensus_upgrade_operation(
  lean_object* args
);

extern lean_object*
eth_consensus_verify_blob_sidecar_inclusion_proof(
  lean_object* name,
  lean_object* fork,
  lean_object* data
);

extern lean_object* eth_consensus_verify_data_column_sidecar(lean_object* args);
extern lean_object* eth_consensus_verify_data_column_sidecar_inclusion_proof(
  lean_object* name, lean_object* fork, lean_object* data);
extern lean_object* eth_consensus_verify_data_column_sidecar_kzg_proofs(
  lean_object* name, lean_object* fork, lean_object* data, lean_object* block);
extern lean_object* eth_consensus_verify_partial_data_column_header_inclusion_proof(
  lean_object* name, lean_object* fork, lean_object* data);
extern lean_object* eth_consensus_verify_partial_data_column_sidecar_kzg_proofs(
  lean_object* name, lean_object* fork, lean_object* data, lean_object* commitments,
  uint64_t column_index);
extern lean_object* eth_consensus_compute_matrix(lean_object* args);
extern lean_object* eth_consensus_recover_matrix(lean_object* args);
extern lean_object* eth_consensus_get_data_column_sidecars_from_block(lean_object* args);
extern lean_object* eth_consensus_get_data_column_sidecars_from_column_sidecar(lean_object* args);
extern lean_object* eth_consensus_light_client_sync(lean_object* args);
extern lean_object* eth_consensus_fork_choice(lean_object* args);
extern lean_object* eth_consensus_gossip_validation(lean_object* args);
extern lean_object* eth_consensus_block_to_light_client_header(lean_object* args);
extern lean_object* eth_consensus_light_client_update_proofs(lean_object* args);
extern lean_object* eth_consensus_is_better_update(lean_object* args);
extern lean_object* eth_consensus_genesis_block(
  lean_object* name, lean_object* fork, lean_object* state);
extern lean_object* eth_consensus_create_light_client_bootstrap(lean_object* args);
extern lean_object* eth_consensus_create_light_client_update(lean_object* args);
extern lean_object* eth_consensus_compute_fork_digest(lean_object* args);

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
  return call_pyvalue_export(eth_consensus_preset, args, 1, CONSENSUS_ERROR);
}

PyObject*
py_consensus_config(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_config, args, 1, CONSENSUS_ERROR);
}

PyObject*
py_consensus_parameters(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_parameters, args, 2, CONSENSUS_ERROR);
}

PyObject*
py_consensus_get_custody_groups(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_get_custody_groups, args, 3, CONSENSUS_ERROR);
}

PyObject*
py_consensus_compute_columns_for_custody_group(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_compute_columns_for_custody_group, args, 2, CONSENSUS_ERROR);
}

PyObject*
py_consensus_ssz_static(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_ssz_static, args, 4, SSZ_ERROR);
}

PyObject*
py_consensus_upgrade_operation(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_upgrade_operation, args, 3, SSZ_ERROR);
}

PyObject*
py_pq_keys_ssz(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_pq_keys_ssz, args, 2, SSZ_ERROR);
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
  return call_pyvalue_export(eth_consensus_compute_shuffled_permutation, args, 3, CONSENSUS_ERROR);
}

PyObject*
py_consensus_compute_shuffled_index(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_compute_shuffled_index, args, 4, CONSENSUS_ERROR);
}

PyObject*
py_consensus_gossip_topics(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_gossip_topics, args, 2, CONSENSUS_ERROR);
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
  return call_pyvalue_export(eth_consensus_compute_subscribed_subnets, args, 3, CONSENSUS_ERROR);
}

PyObject*
py_consensus_reqresp_protocol_ids(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_reqresp_protocol_ids, args, 1, CONSENSUS_ERROR);
}

PyObject*
py_consensus_reqresp_parse_protocol_id(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_reqresp_parse_protocol_id, args, 1, CONSENSUS_ERROR);
}

PyObject*
py_consensus_reqresp_message(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_reqresp_message, args, 4, SSZ_ERROR);
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
  return call_pyvalue_export(eth_consensus_merkle_proof, args, 5, SSZ_ERROR);
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
  return call_pyvalue_export(eth_consensus_verify_data_column_sidecar, args, 5, SSZ_ERROR);
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
  return call_pyvalue_export(eth_consensus_compute_matrix, args, 1, KZG_ERROR);
}

PyObject*
py_consensus_recover_matrix(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_recover_matrix, args, 2, KZG_ERROR);
}

PyObject*
py_consensus_get_data_column_sidecars_from_block(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_get_data_column_sidecars_from_block, args, 4, SSZ_ERROR);
}

PyObject*
py_consensus_get_data_column_sidecars_from_column_sidecar(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_get_data_column_sidecars_from_column_sidecar, args, 4, SSZ_ERROR);
}

PyObject*
py_consensus_process_operation(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_process_operation, args, 8, TRANSITION_ERROR);
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
  return call_pyvalue_export(eth_consensus_light_client_sync, args, 8, LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_fork_choice(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_fork_choice, args, 7, FORK_CHOICE_ERROR);
}

PyObject*
py_consensus_gossip_validation(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_gossip_validation, args, 10, FORK_CHOICE_ERROR);
}

PyObject*
py_consensus_block_to_light_client_header(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_block_to_light_client_header, args, 4, LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_light_client_update_proofs(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_light_client_update_proofs, args, 5, LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_is_better_update(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_is_better_update, args, 6, LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_genesis_block(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[3];
  if (!strs_bytes_args(args, 2, 1, a)) return NULL;
  return except_into_pybytes(eth_consensus_genesis_block(a[0], a[1], a[2]), LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_create_light_client_bootstrap(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_create_light_client_bootstrap, args, 5, LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_create_light_client_update(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_create_light_client_update, args, 11, LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_compute_fork_digest(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_compute_fork_digest, args, 4, SSZ_ERROR);
}

PyObject*
py_consensus_process_epoch(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_process_epoch, args, 5, TRANSITION_ERROR);
}

PyObject*
py_consensus_rewards_deltas(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_rewards_deltas, args, 5, TRANSITION_ERROR);
}

PyObject*
py_consensus_rewards_deltas_batch(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_rewards_deltas_batch, args, 5, TRANSITION_ERROR);
}

PyObject*
py_consensus_upgrade_state(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_upgrade_state, args, 5, TRANSITION_ERROR);
}

PyObject*
py_consensus_process_slots(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_process_slots, args, 5, TRANSITION_ERROR);
}

PyObject*
py_consensus_initialize_genesis(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_initialize_genesis, args, 7, TRANSITION_ERROR);
}

PyObject*
py_consensus_is_valid_genesis_state(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_is_valid_genesis_state, args, 4, TRANSITION_ERROR);
}

PyObject*
py_consensus_get_committee_assignment(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_get_committee_assignment, args, 6, VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_is_proposer(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_is_proposer, args, 5, VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_is_assigned_to_sync_committee(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_is_assigned_to_sync_committee, args, 6, VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_compute_subnets_for_sync_committee(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_compute_subnets_for_sync_committee, args, 5, VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_get_ptc_assignment(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_get_ptc_assignment, args, 6, VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_get_upcoming_proposal_slots(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_get_upcoming_proposal_slots, args, 5, VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_get_validator_signature(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_get_validator_signature, args, 7, VALIDATOR_DUTY_ERROR);
}

/* The name, the fork and a list of a proposer export, or -1 with an exception set.
 * On success the caller owns the three Lean objects. */
static int
named_list_args(
  PyObject* name_obj, PyObject* fork_obj, PyObject* list_obj, const char* list_name,
  lean_object** out
) {
  lean_object* list;
  if (parse_bytes_sequence(list_obj, list_name, &list)) return -1;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) {
    lean_dec(list);
    return -1;
  }
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    lean_dec(list);
    return -1;
  }
  out[0] = name;
  out[1] = fork;
  out[2] = list;
  return 0;
}

PyObject*
py_consensus_get_eth1_vote(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_get_eth1_vote, args, 5, PROPOSER_ERROR);
}

PyObject*
py_consensus_get_eth1_pending_deposit_count(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_get_eth1_pending_deposit_count, args, 3, PROPOSER_ERROR);
}

PyObject*
py_consensus_compute_new_state_root(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_compute_new_state_root, args, 6, PROPOSER_ERROR);
}

PyObject*
py_consensus_compute_on_chain_aggregate(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *list_obj;
  if (!PyArg_ParseTuple(args, "OOO", &name_obj, &fork_obj, &list_obj)) return NULL;
  lean_object* a[3];
  if (named_list_args(name_obj, fork_obj, list_obj, "aggregates", a) < 0) return NULL;
  return except_into_pybytes(eth_consensus_compute_on_chain_aggregate(a[0], a[1], a[2]),
    PROPOSER_ERROR);
}

PyObject*
py_consensus_process_sync_committee_contributions(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *list_obj;
  if (!PyArg_ParseTuple(args, "OOO", &name_obj, &fork_obj, &list_obj)) return NULL;
  lean_object* a[3];
  if (named_list_args(name_obj, fork_obj, list_obj, "contributions", a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_process_sync_committee_contributions(a[0], a[1], a[2]), PROPOSER_ERROR);
}

PyObject*
py_consensus_get_attestation_data(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *slot_obj, *committee_obj, *status_obj;
  const uint8_t *state, *head_root;
  Py_ssize_t state_len, head_root_len;
  if (!PyArg_ParseTuple(args, "OOy#y#OOO", &name_obj, &fork_obj, &state, &state_len, &head_root,
                        &head_root_len, &slot_obj, &committee_obj, &status_obj))
    return NULL;
  uint64_t head_slot, committee, status;
  if (parse_uint64(slot_obj, "head_slot", &head_slot) < 0) return NULL;
  if (parse_uint64(committee_obj, "committee_index", &committee) < 0) return NULL;
  if (parse_uint64(status_obj, "payload_status", &status) < 0) return NULL;
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "name and fork must be str");
    return NULL;
  }
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    return NULL;
  }
  return except_into_pybytes(
    eth_consensus_get_attestation_data(name, fork, mk_bytearray(state, state_len),
      mk_bytearray(head_root, head_root_len), head_slot, committee, status),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_get_aggregate_signature(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *list_obj;
  if (!PyArg_ParseTuple(args, "OOO", &name_obj, &fork_obj, &list_obj)) return NULL;
  lean_object* a[3];
  if (named_list_args(name_obj, fork_obj, list_obj, "attestations", a) < 0) return NULL;
  return except_into_pybytes(eth_consensus_get_aggregate_signature(a[0], a[1], a[2]),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_construct_attestation(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_construct_attestation, args, 7, VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_construct_single_attestation(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_construct_single_attestation, args, 8, VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_construct_aggregate(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *list_obj;
  const uint8_t *state, *data;
  Py_ssize_t state_len, data_len;
  if (!PyArg_ParseTuple(args, "OOy#y#O", &name_obj, &fork_obj, &state, &state_len, &data,
                        &data_len, &list_obj))
    return NULL;
  lean_object* a[3];
  if (named_list_args(name_obj, fork_obj, list_obj, "attestations", a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_construct_aggregate(a[0], a[1], mk_bytearray(state, state_len),
      mk_bytearray(data, data_len), a[2]),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_construct_aggregate_of_single_attestations(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *committee_obj, *list_obj;
  const uint8_t *state, *data;
  Py_ssize_t state_len, data_len;
  if (!PyArg_ParseTuple(args, "OOy#y#OO", &name_obj, &fork_obj, &state, &state_len, &data,
                        &data_len, &committee_obj, &list_obj))
    return NULL;
  uint64_t committee;
  if (parse_uint64(committee_obj, "committee_index", &committee) < 0) return NULL;
  lean_object* a[3];
  if (named_list_args(name_obj, fork_obj, list_obj, "singles", a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_construct_aggregate_of_single_attestations(a[0], a[1],
      mk_bytearray(state, state_len), mk_bytearray(data, data_len), committee, a[2]),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_construct_sync_committee_contribution(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *index_obj, *list_obj;
  const uint8_t *state, *committee, *root;
  Py_ssize_t state_len, committee_len, root_len;
  if (!PyArg_ParseTuple(args, "OOy#y#y#OO", &name_obj, &fork_obj, &state, &state_len, &committee,
                        &committee_len, &root, &root_len, &index_obj, &list_obj))
    return NULL;
  uint64_t index;
  if (parse_uint64(index_obj, "subcommittee_index", &index) < 0) return NULL;
  lean_object* a[3];
  if (named_list_args(name_obj, fork_obj, list_obj, "messages", a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_construct_sync_committee_contribution(a[0], a[1],
      mk_bytearray(state, state_len), mk_bytearray(committee, committee_len),
      mk_bytearray(root, root_len), index, a[2]),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_read_slashing_interchange(
  PyObject* self,
  PyObject* args
) {
  const uint8_t* text;
  Py_ssize_t text_len;
  if (!PyArg_ParseTuple(args, "y#", &text, &text_len)) return NULL;
  return except_into_pybytes(eth_consensus_read_slashing_interchange(mk_bytearray(text, text_len)),
    SLASHING_PROTECTION_ERROR);
}

PyObject*
py_consensus_import_slashing_interchange(
  PyObject* self,
  PyObject* args
) {
  const uint8_t *held, *file;
  Py_ssize_t held_len, file_len;
  if (!PyArg_ParseTuple(args, "y#y#", &held, &held_len, &file, &file_len)) return NULL;
  return except_into_pybytes(
    eth_consensus_import_slashing_interchange(mk_bytearray(held, held_len),
      mk_bytearray(file, file_len)),
    SLASHING_PROTECTION_ERROR);
}

PyObject*
py_consensus_check_block_signing(
  PyObject* self,
  PyObject* args
) {
  PyObject* slot_obj;
  const uint8_t *text, *pubkey, *root;
  Py_ssize_t text_len, pubkey_len, root_len;
  if (!PyArg_ParseTuple(args, "y#y#Oy#", &text, &text_len, &pubkey, &pubkey_len, &slot_obj, &root,
                        &root_len))
    return NULL;
  uint64_t slot;
  if (parse_uint64(slot_obj, "slot", &slot) < 0) return NULL;
  return except_into_pybool(
    eth_consensus_check_block_signing(mk_bytearray(text, text_len),
      mk_bytearray(pubkey, pubkey_len), slot, mk_bytearray(root, root_len)),
    SLASHING_PROTECTION_ERROR);
}

PyObject*
py_consensus_check_attestation_signing(
  PyObject* self,
  PyObject* args
) {
  PyObject *source_obj, *target_obj;
  const uint8_t *text, *pubkey, *root;
  Py_ssize_t text_len, pubkey_len, root_len;
  if (!PyArg_ParseTuple(args, "y#y#OOy#", &text, &text_len, &pubkey, &pubkey_len, &source_obj,
                        &target_obj, &root, &root_len))
    return NULL;
  uint64_t source, target;
  if (parse_uint64(source_obj, "source_epoch", &source) < 0) return NULL;
  if (parse_uint64(target_obj, "target_epoch", &target) < 0) return NULL;
  return except_into_pybool(
    eth_consensus_check_attestation_signing(mk_bytearray(text, text_len),
      mk_bytearray(pubkey, pubkey_len), source, target, mk_bytearray(root, root_len)),
    SLASHING_PROTECTION_ERROR);
}

PyObject*
py_consensus_record_block_signing(
  PyObject* self,
  PyObject* args
) {
  PyObject* slot_obj;
  const uint8_t *text, *pubkey, *root;
  Py_ssize_t text_len, pubkey_len, root_len;
  if (!PyArg_ParseTuple(args, "y#y#Oy#", &text, &text_len, &pubkey, &pubkey_len, &slot_obj, &root,
                        &root_len))
    return NULL;
  uint64_t slot;
  if (parse_uint64(slot_obj, "slot", &slot) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_record_block_signing(mk_bytearray(text, text_len),
      mk_bytearray(pubkey, pubkey_len), slot, mk_bytearray(root, root_len)),
    SLASHING_PROTECTION_ERROR);
}

PyObject*
py_consensus_record_attestation_signing(
  PyObject* self,
  PyObject* args
) {
  PyObject *source_obj, *target_obj;
  const uint8_t *text, *pubkey, *root;
  Py_ssize_t text_len, pubkey_len, root_len;
  if (!PyArg_ParseTuple(args, "y#y#OOy#", &text, &text_len, &pubkey, &pubkey_len, &source_obj,
                        &target_obj, &root, &root_len))
    return NULL;
  uint64_t source, target;
  if (parse_uint64(source_obj, "source_epoch", &source) < 0) return NULL;
  if (parse_uint64(target_obj, "target_epoch", &target) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_record_attestation_signing(mk_bytearray(text, text_len),
      mk_bytearray(pubkey, pubkey_len), source, target, mk_bytearray(root, root_len)),
    SLASHING_PROTECTION_ERROR);
}

PyObject*
py_consensus_is_execution_block(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj;
  const uint8_t* block;
  Py_ssize_t block_len;
  if (!PyArg_ParseTuple(args, "OOy#", &name_obj, &fork_obj, &block, &block_len)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    return NULL;
  }
  return except_into_pybool(
    eth_consensus_is_execution_block(name, fork, mk_bytearray(block, block_len)),
    FORK_CHOICE_ERROR);
}

PyObject*
py_consensus_is_optimistic_candidate_block(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *list_obj, *current_obj, *safe_obj;
  const uint8_t* block;
  Py_ssize_t block_len;
  if (!PyArg_ParseTuple(args, "OOOOOy#", &name_obj, &fork_obj, &list_obj, &current_obj,
                        &safe_obj, &block, &block_len))
    return NULL;
  uint64_t current, safe;
  if (parse_uint64(current_obj, "current_slot", &current) < 0) return NULL;
  if (parse_uint64(safe_obj, "safe_slots", &safe) < 0) return NULL;
  lean_object* a[3];
  if (named_list_args(name_obj, fork_obj, list_obj, "blocks", a) < 0) return NULL;
  return except_into_pybool(
    eth_consensus_is_optimistic_candidate_block(a[0], a[1], a[2], current, safe,
      mk_bytearray(block, block_len)),
    FORK_CHOICE_ERROR);
}

PyObject*
py_consensus_latest_verified_ancestor(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_latest_verified_ancestor, args, 5, FORK_CHOICE_ERROR);
}

PyObject*
py_consensus_on_valid_payload(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_on_valid_payload, args, 5, FORK_CHOICE_ERROR);
}

PyObject*
py_consensus_on_invalidated_payload(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_on_invalidated_payload, args, 5, FORK_CHOICE_ERROR);
}

PyObject*
py_consensus_is_optimistic_restricted_domain(
  PyObject* self,
  PyObject* args
) {
  const uint8_t* domain;
  Py_ssize_t domain_len;
  if (!PyArg_ParseTuple(args, "y#", &domain, &domain_len)) return NULL;
  return except_into_pybool(
    eth_consensus_is_optimistic_restricted_domain(mk_bytearray(domain, domain_len)),
    FORK_CHOICE_ERROR);
}

PyObject*
py_consensus_get_execution_requests(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *list_obj;
  if (!PyArg_ParseTuple(args, "OOO", &name_obj, &fork_obj, &list_obj)) return NULL;
  lean_object* a[3];
  if (named_list_args(name_obj, fork_obj, list_obj, "requests", a) < 0) return NULL;
  return except_into_pybytes(eth_consensus_get_execution_requests(a[0], a[1], a[2]),
    PROPOSER_ERROR);
}

PyObject*
py_consensus_get_validators_custody_requirement(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_get_validators_custody_requirement, args, 5, PROPOSER_ERROR);
}

PyObject*
py_consensus_compute_weak_subjectivity_period(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_compute_weak_subjectivity_period, args, 4, WEAK_SUBJECTIVITY_ERROR);
}

PyObject*
py_consensus_is_within_weak_subjectivity_period(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(
    eth_consensus_is_within_weak_subjectivity_period, args, 7, WEAK_SUBJECTIVITY_ERROR);
}

PyObject*
py_consensus_state_transition(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_state_transition, args, 6, TRANSITION_ERROR);
}

PyObject*
py_consensus_state_transition_across(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_state_transition_across, args, 7, TRANSITION_ERROR);
}

PyObject*
py_consensus_state_transitions(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_state_transitions, args, 6, TRANSITION_ERROR);
}

PyObject*
py_consensus_state_transitions_across(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_state_transitions_across, args, 7, TRANSITION_ERROR);
}

/* Parse three `str` arguments into Lean byte arrays, or return 0 with an error set. */
static int
three_str_args(
  PyObject* args,
  const char* first,
  const char* second,
  const char* third,
  lean_object** out
) {
  PyObject *a, *b, *c;
  if (!PyArg_ParseTuple(args, "OOO", &a, &b, &c)) return 0;
  out[0] = str_arg(a, first);
  if (!out[0]) return 0;
  out[1] = str_arg(b, second);
  if (!out[1]) {
    lean_dec(out[0]);
    return 0;
  }
  out[2] = str_arg(c, third);
  if (!out[2]) {
    lean_dec(out[0]);
    lean_dec(out[1]);
    return 0;
  }
  return 1;
}

PyObject*
py_consensus_reqresp_request_bounds(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_reqresp_request_bounds, args, 3, CONSENSUS_ERROR);
}

PyObject*
py_consensus_reqresp_response_bounds(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_reqresp_response_bounds, args, 3, CONSENSUS_ERROR);
}

PyObject*
py_consensus_gossip_topic_bound(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[3];
  if (!three_str_args(args, "name", "fork", "topic", a)) return NULL;
  return except_into_pyint(eth_consensus_gossip_topic_bound(a[0], a[1], a[2]), CONSENSUS_ERROR);
}

PyObject*
py_engine_prepare_execution_payload(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_prepare_execution_payload, args, 8, PROPOSER_ERROR);
}

PyObject*
py_engine_prepare_execution_payload_gloas(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_prepare_execution_payload_gloas, args, 14, PROPOSER_ERROR);
}

PyObject*
py_consensus_get_execution_payload_bid(
  PyObject* self,
  PyObject* args
) {
  if (PyTuple_Size(args) != 11) {
    PyErr_SetString(PyExc_TypeError, "expected 11 arguments");
    return NULL;
  }
  unsigned long long slot = PyLong_AsUnsignedLongLong(PyTuple_GET_ITEM(args, 8));
  if (PyErr_Occurred()) return NULL;
  unsigned long long builder_index = PyLong_AsUnsignedLongLong(PyTuple_GET_ITEM(args, 9));
  if (PyErr_Occurred()) return NULL;
  unsigned long long value = PyLong_AsUnsignedLongLong(PyTuple_GET_ITEM(args, 10));
  if (PyErr_Occurred()) return NULL;
  PyObject* inputs = PyTuple_GetSlice(args, 0, 8);
  if (!inputs) return NULL;
  lean_object* a[8];
  int read = strs_bytes_args(inputs, 2, 6, a);
  Py_DECREF(inputs);
  if (!read) return NULL;
  return except_into_pybytes(
    eth_consensus_get_execution_payload_bid(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7],
      (uint64_t) slot, (uint64_t) builder_index, (uint64_t) value),
    SSZ_ERROR);
}

PyObject*
py_consensus_get_self_built_execution_payload_bid(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[8];
  if (!strs_bytes_args(args, 2, 6, a)) return NULL;
  return except_into_pybytes(
    eth_consensus_get_self_built_execution_payload_bid(a[0], a[1], a[2], a[3], a[4], a[5], a[6],
      a[7]),
    SSZ_ERROR);
}

PyObject*
py_consensus_get_execution_payload_envelope(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[5];
  if (!strs_bytes_args(args, 2, 3, a)) return NULL;
  return except_into_pybytes(
    eth_consensus_get_execution_payload_envelope(a[0], a[1], a[2], a[3], a[4]), SSZ_ERROR);
}

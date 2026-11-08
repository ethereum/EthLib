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
  lean_object* name,
  lean_object* fork,
  lean_object* handler,
  lean_object* pre,
  lean_object* operation,
  lean_object* config,
  uint8_t verify,
  uint8_t execution_valid
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
eth_consensus_rewards_deltas_batch(
  lean_object* name,
  lean_object* fork,
  lean_object* components,
  lean_object* pre,
  lean_object* config
);

extern lean_object*
eth_consensus_process_slots(
  lean_object* name,
  lean_object* fork,
  lean_object* pre,
  lean_object* config,
  uint64_t slots
);

extern lean_object*
eth_consensus_state_transition(
  lean_object* name,
  lean_object* fork,
  lean_object* pre,
  lean_object* block,
  lean_object* config,
  uint8_t verify
);

extern lean_object*
eth_consensus_initialize_genesis(
  lean_object* name,
  lean_object* fork,
  lean_object* eth1_block_hash,
  lean_object* deposits,
  lean_object* config,
  uint64_t eth1_timestamp,
  uint8_t verify
);

extern lean_object*
eth_consensus_is_valid_genesis_state(
  lean_object* name,
  lean_object* fork,
  lean_object* state,
  lean_object* config
);

extern lean_object*
eth_consensus_compute_weak_subjectivity_period(
  lean_object* name,
  lean_object* fork,
  lean_object* state,
  lean_object* config
);

extern lean_object*
eth_consensus_is_within_weak_subjectivity_period(
  lean_object* name,
  lean_object* fork,
  lean_object* state,
  lean_object* checkpoint,
  lean_object* config,
  uint64_t genesis_time_ms,
  uint64_t time_ms
);

extern lean_object*
eth_consensus_get_committee_assignment(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* config,
  uint64_t epoch, uint64_t validator_index);

extern lean_object*
eth_consensus_is_proposer(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* config,
  uint64_t validator_index);

extern lean_object*
eth_consensus_is_assigned_to_sync_committee(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* config,
  uint64_t epoch, uint64_t validator_index);

extern lean_object*
eth_consensus_compute_subnets_for_sync_committee(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* config,
  uint64_t validator_index);

extern lean_object*
eth_consensus_get_ptc_assignment(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* config,
  uint64_t epoch, uint64_t validator_index);

extern lean_object*
eth_consensus_get_upcoming_proposal_slots(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* config,
  uint64_t validator_index);

extern lean_object*
eth_consensus_get_validator_signature(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* config,
  lean_object* duty, lean_object* object, lean_object* secret_key);

extern lean_object*
eth_consensus_get_eth1_vote(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* config,
  lean_object* chain);

extern lean_object*
eth_consensus_get_eth1_pending_deposit_count(
  lean_object* name, lean_object* fork, lean_object* state);

extern lean_object*
eth_consensus_compute_new_state_root(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* block,
  lean_object* config, uint8_t verify);

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
  lean_object* name, lean_object* fork, lean_object* state, lean_object* config,
  lean_object* data, uint64_t validator_index, lean_object* secret_key);

extern lean_object*
eth_consensus_construct_single_attestation(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* config,
  lean_object* data, uint64_t committee_index, uint64_t validator_index, lean_object* secret_key);

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
  lean_object* name, lean_object* fork, lean_object* blocks, lean_object* optimistic_roots,
  lean_object* root);

extern lean_object*
eth_consensus_on_valid_payload(
  lean_object* name, lean_object* fork, lean_object* blocks, lean_object* optimistic_roots,
  lean_object* root);

extern lean_object*
eth_consensus_on_invalidated_payload(
  lean_object* name, lean_object* fork, lean_object* blocks, lean_object* optimistic_roots,
  lean_object* first);

extern lean_object*
eth_consensus_is_optimistic_restricted_domain(lean_object* domain_type);

extern lean_object*
eth_consensus_get_execution_requests(
  lean_object* name, lean_object* fork, lean_object* requests);

extern lean_object*
eth_consensus_get_validators_custody_requirement(
  lean_object* name, lean_object* fork, lean_object* state, lean_object* config,
  lean_object* indices);

extern lean_object*
eth_consensus_state_transition_across(
  lean_object* name,
  lean_object* fork,
  lean_object* pre,
  lean_object* block_fork,
  lean_object* block,
  lean_object* config,
  uint8_t verify
);

extern lean_object*
eth_consensus_state_transitions(
  lean_object* name,
  lean_object* fork,
  lean_object* pre,
  lean_object* blocks,
  lean_object* config,
  uint8_t verify
);

extern lean_object*
eth_consensus_state_transitions_across(
  lean_object* name,
  lean_object* fork,
  lean_object* pre,
  lean_object* block_forks,
  lean_object* blocks,
  lean_object* config,
  uint8_t verify
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
extern lean_object* eth_consensus_fork_choice(lean_object* args);
extern lean_object* eth_consensus_gossip_validation(
  lean_object* name, lean_object* fork, lean_object* anchor_state, lean_object* anchor_block,
  lean_object* blocks, lean_object* finalized, lean_object* topic, lean_object* messages,
  lean_object* config, uint8_t verify);
extern lean_object* eth_consensus_block_to_light_client_header(
  lean_object* name, lean_object* fork, lean_object* config, lean_object* block);
extern lean_object* eth_consensus_light_client_update_proofs(
  lean_object* name, lean_object* fork, lean_object* type, lean_object* config,
  lean_object* data);
extern lean_object* eth_consensus_is_better_update(
  lean_object* name, lean_object* fork, lean_object* old_fork, lean_object* config,
  lean_object* new_update, lean_object* old_update);
extern lean_object* eth_consensus_genesis_block(
  lean_object* name, lean_object* fork, lean_object* state);
extern lean_object* eth_consensus_create_light_client_bootstrap(
  lean_object* name, lean_object* fork, lean_object* config, lean_object* state,
  lean_object* block);
extern lean_object* eth_consensus_create_light_client_update(
  lean_object* name, lean_object* fork, lean_object* attested_fork, lean_object* finalized_fork,
  lean_object* type, lean_object* config, lean_object* state, lean_object* block,
  lean_object* attested_state, lean_object* attested_block, lean_object* finalized_block);
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
  return call_pyvalue_export(eth_consensus_ssz_static, args, 4, SSZ_ERROR);
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
  int verify, execution_valid;
  if (!PyArg_ParseTuple(args, "OOOOOOpp", &name_obj, &fork_obj, &handler_obj, &pre_obj,
                        &operation_obj, &config_obj, &verify, &execution_valid)) return NULL;
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
                                    (uint8_t) verify, (uint8_t) execution_valid),
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
  if (PyTuple_Size(args) != 10) {
    PyErr_SetString(PyExc_TypeError, "expected 10 arguments");
    return NULL;
  }
  int verify = PyObject_IsTrue(PyTuple_GET_ITEM(args, 9));
  if (verify < 0) return NULL;
  PyObject* inputs = PyTuple_GetSlice(args, 0, 9);
  if (!inputs) return NULL;
  lean_object* a[9];
  int read = strs_bytes_args(inputs, 2, 7, a);
  Py_DECREF(inputs);
  if (!read) return NULL;
  return except_into_pybytes(
    eth_consensus_gossip_validation(
      a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], (uint8_t) verify),
    FORK_CHOICE_ERROR);
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
  lean_object* a[6];
  if (!strs_bytes_args(args, 3, 3, a)) return NULL;
  return except_into_pybool(
    eth_consensus_is_better_update(a[0], a[1], a[2], a[3], a[4], a[5]), LIGHT_CLIENT_ERROR);
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
  lean_object* a[5];
  if (!strs_bytes_args(args, 2, 3, a)) return NULL;
  return except_into_pybytes(
    eth_consensus_create_light_client_bootstrap(a[0], a[1], a[2], a[3], a[4]),
    LIGHT_CLIENT_ERROR);
}

PyObject*
py_consensus_create_light_client_update(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[11];
  if (!strs_bytes_args(args, 5, 6, a)) return NULL;
  return except_into_pybytes(
    eth_consensus_create_light_client_update(
      a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10]),
    LIGHT_CLIENT_ERROR);
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
py_consensus_rewards_deltas_batch(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *components_obj, *pre_obj, *config_obj;
  if (!PyArg_ParseTuple(args, "OOOOO", &name_obj, &fork_obj, &components_obj, &pre_obj,
                        &config_obj)) return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "name and fork must be str");
    return NULL;
  }
  if (!PyBytes_Check(pre_obj) || !PyBytes_Check(config_obj)) {
    PyErr_SetString(PyExc_TypeError, "pre and config must be bytes");
    return NULL;
  }
  lean_object* components;
  if (parse_bytes_sequence(components_obj, "components", &components)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) {
    lean_dec(components);
    return NULL;
  }
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    lean_dec(components);
    return NULL;
  }
  lean_object* pre = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(pre_obj), PyBytes_GET_SIZE(pre_obj));
  lean_object* config = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(config_obj), PyBytes_GET_SIZE(config_obj));
  return except_into_pybytes_list(
    eth_consensus_rewards_deltas_batch(name, fork, components, pre, config), TRANSITION_ERROR);
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

PyObject*
py_consensus_process_slots(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *pre_obj, *config_obj;
  unsigned long long slots;
  if (!PyArg_ParseTuple(args, "OOOOK", &name_obj, &fork_obj, &pre_obj, &config_obj, &slots))
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
    eth_consensus_process_slots(name, fork, pre, config, (uint64_t) slots), TRANSITION_ERROR);
}

PyObject*
py_consensus_initialize_genesis(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj;
  const uint8_t *hash, *deposits, *config;
  Py_ssize_t hash_len, deposits_len, config_len;
  unsigned long long timestamp;
  int verify;
  if (!PyArg_ParseTuple(args, "OOy#y#y#Kp", &name_obj, &fork_obj, &hash, &hash_len, &deposits,
                        &deposits_len, &config, &config_len, &timestamp, &verify))
    return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
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
    eth_consensus_initialize_genesis(name, fork, mk_bytearray(hash, hash_len),
      mk_bytearray(deposits, deposits_len), mk_bytearray(config, config_len),
      (uint64_t) timestamp, (uint8_t) verify),
    TRANSITION_ERROR);
}

PyObject*
py_consensus_is_valid_genesis_state(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj;
  const uint8_t *state, *config;
  Py_ssize_t state_len, config_len;
  if (!PyArg_ParseTuple(args, "OOy#y#", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len))
    return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
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
  return except_into_pybool(
    eth_consensus_is_valid_genesis_state(name, fork, mk_bytearray(state, state_len),
      mk_bytearray(config, config_len)),
    TRANSITION_ERROR);
}

/* The name, the fork, the state and the configuration of a duty export, or NULL with an
 * exception set. On success the caller owns the four Lean objects. */
static int
duty_args(
  PyObject* name_obj, PyObject* fork_obj, const uint8_t* state, Py_ssize_t state_len,
  const uint8_t* config, Py_ssize_t config_len, lean_object** out
) {
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "name and fork must be str");
    return -1;
  }
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return -1;
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    return -1;
  }
  out[0] = name;
  out[1] = fork;
  out[2] = mk_bytearray(state, state_len);
  out[3] = mk_bytearray(config, config_len);
  return 0;
}

PyObject*
py_consensus_get_committee_assignment(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *epoch_obj, *index_obj;
  const uint8_t *state, *config;
  Py_ssize_t state_len, config_len;
  if (!PyArg_ParseTuple(args, "OOy#y#OO", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len, &epoch_obj, &index_obj))
    return NULL;
  uint64_t epoch, index;
  if (parse_uint64(epoch_obj, "epoch", &epoch) < 0) return NULL;
  if (parse_uint64(index_obj, "validator_index", &index) < 0) return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_get_committee_assignment(a[0], a[1], a[2], a[3], epoch, index),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_is_proposer(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *index_obj;
  const uint8_t *state, *config;
  Py_ssize_t state_len, config_len;
  if (!PyArg_ParseTuple(args, "OOy#y#O", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len, &index_obj))
    return NULL;
  uint64_t index;
  if (parse_uint64(index_obj, "validator_index", &index) < 0) return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) return NULL;
  return except_into_pybool(eth_consensus_is_proposer(a[0], a[1], a[2], a[3], index),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_is_assigned_to_sync_committee(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *epoch_obj, *index_obj;
  const uint8_t *state, *config;
  Py_ssize_t state_len, config_len;
  if (!PyArg_ParseTuple(args, "OOy#y#OO", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len, &epoch_obj, &index_obj))
    return NULL;
  uint64_t epoch, index;
  if (parse_uint64(epoch_obj, "epoch", &epoch) < 0) return NULL;
  if (parse_uint64(index_obj, "validator_index", &index) < 0) return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) return NULL;
  return except_into_pybool(
    eth_consensus_is_assigned_to_sync_committee(a[0], a[1], a[2], a[3], epoch, index),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_compute_subnets_for_sync_committee(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *index_obj;
  const uint8_t *state, *config;
  Py_ssize_t state_len, config_len;
  if (!PyArg_ParseTuple(args, "OOy#y#O", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len, &index_obj))
    return NULL;
  uint64_t index;
  if (parse_uint64(index_obj, "validator_index", &index) < 0) return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_compute_subnets_for_sync_committee(a[0], a[1], a[2], a[3], index),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_get_ptc_assignment(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *epoch_obj, *index_obj;
  const uint8_t *state, *config;
  Py_ssize_t state_len, config_len;
  if (!PyArg_ParseTuple(args, "OOy#y#OO", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len, &epoch_obj, &index_obj))
    return NULL;
  uint64_t epoch, index;
  if (parse_uint64(epoch_obj, "epoch", &epoch) < 0) return NULL;
  if (parse_uint64(index_obj, "validator_index", &index) < 0) return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_get_ptc_assignment(a[0], a[1], a[2], a[3], epoch, index),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_get_upcoming_proposal_slots(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *index_obj;
  const uint8_t *state, *config;
  Py_ssize_t state_len, config_len;
  if (!PyArg_ParseTuple(args, "OOy#y#O", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len, &index_obj))
    return NULL;
  uint64_t index;
  if (parse_uint64(index_obj, "validator_index", &index) < 0) return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_get_upcoming_proposal_slots(a[0], a[1], a[2], a[3], index),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_get_validator_signature(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *duty_obj;
  const uint8_t *state, *config, *object, *key;
  Py_ssize_t state_len, config_len, object_len, key_len;
  if (!PyArg_ParseTuple(args, "OOy#y#Oy#y#", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len, &duty_obj, &object, &object_len, &key, &key_len))
    return NULL;
  if (!PyUnicode_Check(duty_obj)) {
    PyErr_SetString(PyExc_TypeError, "duty must be str");
    return NULL;
  }
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) return NULL;
  lean_object* duty = str_arg(duty_obj, "duty");
  if (!duty) {
    for (int i = 0; i < 4; i++) lean_dec(a[i]);
    return NULL;
  }
  return except_into_pybytes(
    eth_consensus_get_validator_signature(a[0], a[1], a[2], a[3], duty,
      mk_bytearray(object, object_len), mk_bytearray(key, key_len)),
    VALIDATOR_DUTY_ERROR);
}

/* A sequence of `bytes` of one length as a Lean `Array ByteArray`, or NULL with an exception set.
 */
static lean_object*
fixed_bytes_list_arg(
  PyObject* seq,
  Py_ssize_t stride,
  const char* name
) {
  Py_ssize_t n;
  uint8_t* buf = pack_bytes_sequence(seq, stride, &n, name);
  if (!buf) return NULL;
  lean_object* arr = mk_bytearray_array(buf, (size_t) n, (size_t) stride);
  PyMem_Free(buf);
  return arr;
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
  PyObject *name_obj, *fork_obj, *chain_obj;
  const uint8_t *state, *config;
  Py_ssize_t state_len, config_len;
  if (!PyArg_ParseTuple(args, "OOy#y#O", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len, &chain_obj))
    return NULL;
  /* Each block is its 8-byte timestamp followed by its 72-byte Eth1 data. */
  lean_object* chain = fixed_bytes_list_arg(chain_obj, 80, "chain");
  if (!chain) return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) {
    lean_dec(chain);
    return NULL;
  }
  return except_into_pybytes(eth_consensus_get_eth1_vote(a[0], a[1], a[2], a[3], chain),
    PROPOSER_ERROR);
}

PyObject*
py_consensus_get_eth1_pending_deposit_count(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj;
  const uint8_t* state;
  Py_ssize_t state_len;
  if (!PyArg_ParseTuple(args, "OOy#", &name_obj, &fork_obj, &state, &state_len)) return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, (const uint8_t*) "", 0, a) < 0)
    return NULL;
  /* The count reads no configuration. */
  lean_dec(a[3]);
  return except_into_pyint(eth_consensus_get_eth1_pending_deposit_count(a[0], a[1], a[2]),
    PROPOSER_ERROR);
}

PyObject*
py_consensus_compute_new_state_root(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj;
  const uint8_t *state, *block, *config;
  Py_ssize_t state_len, block_len, config_len;
  int verify;
  if (!PyArg_ParseTuple(args, "OOy#y#y#p", &name_obj, &fork_obj, &state, &state_len, &block,
                        &block_len, &config, &config_len, &verify))
    return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_compute_new_state_root(a[0], a[1], a[2], mk_bytearray(block, block_len), a[3],
      (uint8_t) verify),
    PROPOSER_ERROR);
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
  PyObject *name_obj, *fork_obj, *index_obj;
  const uint8_t *state, *config, *data, *key;
  Py_ssize_t state_len, config_len, data_len, key_len;
  if (!PyArg_ParseTuple(args, "OOy#y#y#Oy#", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len, &data, &data_len, &index_obj, &key, &key_len))
    return NULL;
  uint64_t index;
  if (parse_uint64(index_obj, "validator_index", &index) < 0) return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_construct_attestation(a[0], a[1], a[2], a[3], mk_bytearray(data, data_len),
      index, mk_bytearray(key, key_len)),
    VALIDATOR_DUTY_ERROR);
}

PyObject*
py_consensus_construct_single_attestation(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *committee_obj, *index_obj;
  const uint8_t *state, *config, *data, *key;
  Py_ssize_t state_len, config_len, data_len, key_len;
  if (!PyArg_ParseTuple(args, "OOy#y#y#OOy#", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len, &data, &data_len, &committee_obj, &index_obj, &key,
                        &key_len))
    return NULL;
  uint64_t committee, index;
  if (parse_uint64(committee_obj, "committee_index", &committee) < 0) return NULL;
  if (parse_uint64(index_obj, "validator_index", &index) < 0) return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_construct_single_attestation(a[0], a[1], a[2], a[3],
      mk_bytearray(data, data_len), committee, index, mk_bytearray(key, key_len)),
    VALIDATOR_DUTY_ERROR);
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
  PyObject *name_obj, *fork_obj, *list_obj;
  const uint8_t *roots, *root;
  Py_ssize_t roots_len, root_len;
  if (!PyArg_ParseTuple(args, "OOOy#y#", &name_obj, &fork_obj, &list_obj, &roots, &roots_len,
                        &root, &root_len))
    return NULL;
  lean_object* a[3];
  if (named_list_args(name_obj, fork_obj, list_obj, "blocks", a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_latest_verified_ancestor(a[0], a[1], a[2], mk_bytearray(roots, roots_len),
      mk_bytearray(root, root_len)),
    FORK_CHOICE_ERROR);
}

PyObject*
py_consensus_on_valid_payload(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *list_obj;
  const uint8_t *roots, *root;
  Py_ssize_t roots_len, root_len;
  if (!PyArg_ParseTuple(args, "OOOy#y#", &name_obj, &fork_obj, &list_obj, &roots, &roots_len,
                        &root, &root_len))
    return NULL;
  lean_object* a[3];
  if (named_list_args(name_obj, fork_obj, list_obj, "blocks", a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_on_valid_payload(a[0], a[1], a[2], mk_bytearray(roots, roots_len),
      mk_bytearray(root, root_len)),
    FORK_CHOICE_ERROR);
}

PyObject*
py_consensus_on_invalidated_payload(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *list_obj;
  const uint8_t *roots, *root;
  Py_ssize_t roots_len, root_len;
  if (!PyArg_ParseTuple(args, "OOOy#y#", &name_obj, &fork_obj, &list_obj, &roots, &roots_len,
                        &root, &root_len))
    return NULL;
  lean_object* a[3];
  if (named_list_args(name_obj, fork_obj, list_obj, "blocks", a) < 0) return NULL;
  return except_into_pybytes(
    eth_consensus_on_invalidated_payload(a[0], a[1], a[2], mk_bytearray(roots, roots_len),
      mk_bytearray(root, root_len)),
    FORK_CHOICE_ERROR);
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
  PyObject *name_obj, *fork_obj, *indices_obj;
  const uint8_t *state, *config;
  Py_ssize_t state_len, config_len;
  if (!PyArg_ParseTuple(args, "OOy#y#O", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len, &indices_obj))
    return NULL;
  /* Each validator index is 8 bytes, little-endian. */
  lean_object* indices = fixed_bytes_list_arg(indices_obj, 8, "validator_indices");
  if (!indices) return NULL;
  lean_object* a[4];
  if (duty_args(name_obj, fork_obj, state, state_len, config, config_len, a) < 0) {
    lean_dec(indices);
    return NULL;
  }
  return except_into_pyint(
    eth_consensus_get_validators_custody_requirement(a[0], a[1], a[2], a[3], indices),
    PROPOSER_ERROR);
}

PyObject*
py_consensus_compute_weak_subjectivity_period(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj;
  const uint8_t *state, *config;
  Py_ssize_t state_len, config_len;
  if (!PyArg_ParseTuple(args, "OOy#y#", &name_obj, &fork_obj, &state, &state_len, &config,
                        &config_len))
    return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
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
  return except_into_pyint(
    eth_consensus_compute_weak_subjectivity_period(name, fork, mk_bytearray(state, state_len),
      mk_bytearray(config, config_len)),
    WEAK_SUBJECTIVITY_ERROR);
}

PyObject*
py_consensus_is_within_weak_subjectivity_period(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *genesis_obj, *time_obj;
  const uint8_t *state, *checkpoint, *config;
  Py_ssize_t state_len, checkpoint_len, config_len;
  if (!PyArg_ParseTuple(args, "OOy#y#y#OO", &name_obj, &fork_obj, &state, &state_len,
                        &checkpoint, &checkpoint_len, &config, &config_len, &genesis_obj,
                        &time_obj))
    return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "name and fork must be str");
    return NULL;
  }
  uint64_t genesis_time_ms, time_ms;
  if (parse_uint64(genesis_obj, "genesis_time_ms", &genesis_time_ms) < 0) return NULL;
  if (parse_uint64(time_obj, "time_ms", &time_ms) < 0) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    return NULL;
  }
  return except_into_pybool(
    eth_consensus_is_within_weak_subjectivity_period(name, fork, mk_bytearray(state, state_len),
      mk_bytearray(checkpoint, checkpoint_len), mk_bytearray(config, config_len),
      genesis_time_ms, time_ms),
    WEAK_SUBJECTIVITY_ERROR);
}

PyObject*
py_consensus_state_transition(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *pre_obj, *block_obj, *config_obj;
  int verify;
  if (!PyArg_ParseTuple(args, "OOOOOp", &name_obj, &fork_obj, &pre_obj, &block_obj, &config_obj,
                        &verify))
    return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "name and fork must be str");
    return NULL;
  }
  if (!PyBytes_Check(pre_obj) || !PyBytes_Check(block_obj) || !PyBytes_Check(config_obj)) {
    PyErr_SetString(PyExc_TypeError, "pre, block and config must be bytes");
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
  lean_object* block = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(block_obj), PyBytes_GET_SIZE(block_obj));
  lean_object* config = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(config_obj), PyBytes_GET_SIZE(config_obj));
  return except_into_pybytes(
    eth_consensus_state_transition(name, fork, pre, block, config, (uint8_t) verify),
    TRANSITION_ERROR);
}

PyObject*
py_consensus_state_transition_across(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *pre_obj, *block_fork_obj, *block_obj, *config_obj;
  int verify;
  if (!PyArg_ParseTuple(args, "OOOOOOp", &name_obj, &fork_obj, &pre_obj, &block_fork_obj,
                        &block_obj, &config_obj, &verify))
    return NULL;
  /* Check every argument before any Lean object exists, so a failure leaks nothing. */
  if (!PyUnicode_Check(name_obj) || !PyUnicode_Check(fork_obj)
      || !PyUnicode_Check(block_fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "name, fork and block_fork must be str");
    return NULL;
  }
  if (!PyBytes_Check(pre_obj) || !PyBytes_Check(block_obj) || !PyBytes_Check(config_obj)) {
    PyErr_SetString(PyExc_TypeError, "pre, block and config must be bytes");
    return NULL;
  }
  Py_ssize_t name_len, fork_len, block_fork_len;
  const char* name_utf8 = PyUnicode_AsUTF8AndSize(name_obj, &name_len);
  if (!name_utf8) return NULL;
  const char* fork_utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &fork_len);
  if (!fork_utf8) return NULL;
  const char* block_fork_utf8 = PyUnicode_AsUTF8AndSize(block_fork_obj, &block_fork_len);
  if (!block_fork_utf8) return NULL;
  lean_object* name = mk_bytearray((const uint8_t*) name_utf8, name_len);
  lean_object* fork = mk_bytearray((const uint8_t*) fork_utf8, fork_len);
  lean_object* block_fork = mk_bytearray((const uint8_t*) block_fork_utf8, block_fork_len);
  lean_object* pre = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(pre_obj), PyBytes_GET_SIZE(pre_obj));
  lean_object* block = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(block_obj), PyBytes_GET_SIZE(block_obj));
  lean_object* config = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(config_obj), PyBytes_GET_SIZE(config_obj));
  return except_into_pybytes(
    eth_consensus_state_transition_across(name, fork, pre, block_fork, block, config,
                                          (uint8_t) verify),
    TRANSITION_ERROR);
}

PyObject*
py_consensus_state_transitions(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *pre_obj, *blocks_obj, *config_obj;
  int verify;
  if (!PyArg_ParseTuple(args, "OOOOOp", &name_obj, &fork_obj, &pre_obj, &blocks_obj,
                        &config_obj, &verify))
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
  lean_object* blocks;
  if (parse_bytes_sequence(blocks_obj, "blocks", &blocks)) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) {
    lean_dec(blocks);
    return NULL;
  }
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    lean_dec(blocks);
    return NULL;
  }
  lean_object* pre = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(pre_obj), PyBytes_GET_SIZE(pre_obj));
  lean_object* config = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(config_obj), PyBytes_GET_SIZE(config_obj));
  return except_into_pybytes(
    eth_consensus_state_transitions(name, fork, pre, blocks, config, (uint8_t) verify),
    TRANSITION_ERROR);
}

PyObject*
py_consensus_state_transitions_across(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *fork_obj, *pre_obj, *block_forks_obj, *blocks_obj, *config_obj;
  int verify;
  if (!PyArg_ParseTuple(args, "OOOOOOp", &name_obj, &fork_obj, &pre_obj, &block_forks_obj,
                        &blocks_obj, &config_obj, &verify))
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
  lean_object* block_forks;
  if (parse_bytes_sequence(block_forks_obj, "block_forks", &block_forks)) return NULL;
  lean_object* blocks;
  if (parse_bytes_sequence(blocks_obj, "blocks", &blocks)) {
    lean_dec(block_forks);
    return NULL;
  }
  lean_object* name = str_arg(name_obj, "name");
  if (!name) {
    lean_dec(blocks);
    lean_dec(block_forks);
    return NULL;
  }
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    lean_dec(blocks);
    lean_dec(block_forks);
    return NULL;
  }
  lean_object* pre = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(pre_obj), PyBytes_GET_SIZE(pre_obj));
  lean_object* config = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(config_obj), PyBytes_GET_SIZE(config_obj));
  return except_into_pybytes(
    eth_consensus_state_transitions_across(name, fork, pre, block_forks, blocks, config,
                                           (uint8_t) verify),
    TRANSITION_ERROR);
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

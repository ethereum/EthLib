/* Typed wrappers of the deposit tree and its EIP-4881 snapshot. */
#include "wrappers.h"

extern lean_object* eth_consensus_deposit_tree_new(lean_object* args);
extern lean_object* eth_consensus_deposit_tree_push_leaf(lean_object* args);
extern lean_object* eth_consensus_deposit_tree_push_leaves(lean_object* args);
extern lean_object* eth_consensus_deposit_tree_get_root(lean_object* args);
extern lean_object* eth_consensus_deposit_tree_finalize(lean_object* args);
extern lean_object* eth_consensus_deposit_tree_get_proof(lean_object* args);
extern lean_object* eth_consensus_deposit_tree_get_snapshot(lean_object* args);
extern lean_object* eth_consensus_deposit_tree_from_snapshot(lean_object* args);
extern lean_object* eth_consensus_deposit_tree_snapshot_calculate_root(lean_object* args);

PyObject*
py_consensus_deposit_tree_new(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_deposit_tree_new, args, 0, DEPOSIT_TREE_ERROR);
}

PyObject*
py_consensus_deposit_tree_push_leaf(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_deposit_tree_push_leaf, args, 2, DEPOSIT_TREE_ERROR);
}

PyObject*
py_consensus_deposit_tree_push_leaves(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_deposit_tree_push_leaves, args, 2, DEPOSIT_TREE_ERROR);
}

PyObject*
py_consensus_deposit_tree_get_root(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_deposit_tree_get_root, args, 1, DEPOSIT_TREE_ERROR);
}

PyObject*
py_consensus_deposit_tree_finalize(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_deposit_tree_finalize, args, 3, DEPOSIT_TREE_ERROR);
}

PyObject*
py_consensus_deposit_tree_get_proof(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_deposit_tree_get_proof, args, 2, DEPOSIT_TREE_ERROR);
}

PyObject*
py_consensus_deposit_tree_get_snapshot(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_deposit_tree_get_snapshot, args, 1, DEPOSIT_TREE_ERROR);
}

PyObject*
py_consensus_deposit_tree_from_snapshot(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_deposit_tree_from_snapshot, args, 1, DEPOSIT_TREE_ERROR);
}

PyObject*
py_consensus_deposit_tree_snapshot_calculate_root(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_consensus_deposit_tree_snapshot_calculate_root, args, 1, DEPOSIT_TREE_ERROR);
}

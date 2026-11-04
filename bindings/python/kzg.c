/*
 * KZG handler wrappers. Each function parses Python arguments, marshals
 * them into Lean runtime objects, invokes the corresponding `@[export]`-d
 * `eth_kzg_*` symbol, and unwraps the IO result back to Python.
 */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_kzg_blob_to_kzg_commitment(
  lean_object* blob
);

extern lean_object*
eth_kzg_compute_challenge(
  lean_object* blob,
  lean_object* commitment
);

extern lean_object*
eth_kzg_compute_kzg_proof(
  lean_object* blob,
  lean_object* z
);

extern lean_object*
eth_kzg_verify_kzg_proof(
  lean_object* c,
  lean_object* z,
  lean_object* y,
  lean_object* p
);

extern lean_object*
eth_kzg_compute_blob_kzg_proof(
  lean_object* blob,
  lean_object* c
);

extern lean_object*
eth_kzg_verify_blob_kzg_proof(
  lean_object* blob,
  lean_object* c,
  lean_object* p
);

extern lean_object*
eth_kzg_verify_blob_kzg_proof_batch(
  lean_object* blobs,
  lean_object* cs,
  lean_object* ps
);

extern lean_object*
eth_kzg_compute_cells(
  lean_object* blob
);

extern lean_object*
eth_kzg_compute_cells_and_kzg_proofs(
  lean_object* blob
);

extern lean_object*
eth_kzg_compute_verify_cell_kzg_proof_batch_challenge(
  lean_object* commitments,
  lean_object* commitment_indices_be,
  lean_object* cell_indices_be,
  lean_object* cosets_evals,
  lean_object* proofs
);

extern lean_object*
eth_kzg_verify_cell_kzg_proof_batch(
  lean_object* cs,
  lean_object* idx,
  lean_object* cells,
  lean_object* ps
);

extern lean_object*
eth_kzg_recover_cells_and_kzg_proofs(
  lean_object* idx,
  lean_object* cells
);

/* ---- Local helpers (KZG-only) ---------------------------------------- */

static void
u64_be(
  uint8_t out[8],
  uint64_t v
) {
  for (int i = 0; i < 8; i++) out[i] = (uint8_t)(v >> ((7 - i) * 8));
}

static lean_object*
mk_indices_bytearray(
  const uint64_t* idx,
  size_t n
) {
  lean_object* arr = lean_alloc_sarray(1, n * 8, n * 8);
  uint8_t* dst = lean_sarray_cptr(arr);
  for (size_t i = 0; i < n; i++) u64_be(dst + i * 8, idx[i]);
  return arr;
}

/* Parse a Python sequence-of-ints into a malloc'd uint64_t[]. */
static uint64_t*
pack_indices(
  PyObject* seq,
  Py_ssize_t* out_len
) {
  PyObject* fast = PySequence_Fast(seq, "expected a sequence of ints");
  if (!fast) return NULL;
  Py_ssize_t n = PySequence_Fast_GET_SIZE(fast);
  uint64_t* buf = (uint64_t*) PyMem_Malloc(n * sizeof(uint64_t));
  if (!buf) { Py_DECREF(fast); PyErr_NoMemory(); return NULL; }
  for (Py_ssize_t i = 0; i < n; i++) {
    PyObject* item = PySequence_Fast_GET_ITEM(fast, i);
    unsigned long long v = PyLong_AsUnsignedLongLong(item);
    if (v == (unsigned long long)-1 && PyErr_Occurred()) {
      PyMem_Free(buf); Py_DECREF(fast); return NULL;
    }
    buf[i] = (uint64_t) v;
  }
  Py_DECREF(fast);
  *out_len = n;
  return buf;
}

/* A list of `n` byte strings of `size` bytes each, read from `buf`, or NULL with an error set. */
static PyObject*
bytes_list(
  const uint8_t* buf,
  size_t n,
  size_t size
) {
  PyObject* list = PyList_New((Py_ssize_t) n);
  if (!list) return NULL;
  for (size_t i = 0; i < n; i++) {
    PyObject* item = PyBytes_FromStringAndSize((const char*) (buf + i * size), (Py_ssize_t) size);
    if (!item) { Py_DECREF(list); return NULL; }
    PyList_SET_ITEM(list, (Py_ssize_t) i, item);
  }
  return list;
}

/* The pair (cells, proofs) of a buffer that holds every cell, then every proof. */
static PyObject*
cells_and_proofs(
  const uint8_t* buf
) {
  PyObject* cells = bytes_list(buf, CELLS_PER_EXT_BLOB, BYTES_PER_CELL);
  if (!cells) return NULL;
  PyObject* proofs = bytes_list(buf + CELLS_PER_EXT_BLOB * BYTES_PER_CELL,
                                CELLS_PER_EXT_BLOB, BYTES_PER_PROOF);
  if (!proofs) { Py_DECREF(cells); return NULL; }
  PyObject* tup = PyTuple_Pack(2, cells, proofs);
  Py_DECREF(cells); Py_DECREF(proofs);
  return tup;
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_blob_to_kzg_commitment(
  PyObject* self,
  PyObject* args
) {
  PyObject* blob_obj;
  if (!PyArg_ParseTuple(args, "O", &blob_obj)) return NULL;
  const uint8_t* blob = parse_bytes_of_size(blob_obj, BYTES_PER_BLOB, "blob");
  if (!blob) return NULL;
  uint8_t out[BYTES_PER_COMMITMENT];
  lean_object* res = eth_kzg_blob_to_kzg_commitment(
    mk_bytearray(blob, BYTES_PER_BLOB));
  if (except_into_buffer(res, KZG_ERROR, out, BYTES_PER_COMMITMENT)) return NULL;
  return PyBytes_FromStringAndSize((const char*) out, BYTES_PER_COMMITMENT);
}

PyObject*
py_compute_challenge(
  PyObject* self,
  PyObject* args
) {
  PyObject *blob_obj, *com_obj;
  if (!PyArg_ParseTuple(args, "OO", &blob_obj, &com_obj)) return NULL;
  const uint8_t* blob = parse_bytes_of_size(blob_obj, BYTES_PER_BLOB, "blob");
  if (!blob) return NULL;
  const uint8_t* com = parse_bytes_of_size(com_obj, BYTES_PER_COMMITMENT, "commitment");
  if (!com) return NULL;
  uint8_t out[BYTES_PER_FIELD_ELEMENT];
  lean_object* res = eth_kzg_compute_challenge(
    mk_bytearray(blob, BYTES_PER_BLOB),
    mk_bytearray(com, BYTES_PER_COMMITMENT));
  if (except_into_buffer(res, KZG_ERROR, out, BYTES_PER_FIELD_ELEMENT)) return NULL;
  return PyBytes_FromStringAndSize((const char*) out, BYTES_PER_FIELD_ELEMENT);
}

PyObject*
py_compute_kzg_proof(
  PyObject* self,
  PyObject* args
) {
  PyObject *blob_obj, *z_obj;
  if (!PyArg_ParseTuple(args, "OO", &blob_obj, &z_obj)) return NULL;
  const uint8_t* blob = parse_bytes_of_size(blob_obj, BYTES_PER_BLOB, "blob");
  if (!blob) return NULL;
  const uint8_t* z = parse_bytes_of_size(z_obj, BYTES_PER_FIELD_ELEMENT, "z");
  if (!z) return NULL;
  uint8_t buf[BYTES_PER_PROOF + BYTES_PER_FIELD_ELEMENT];
  lean_object* res = eth_kzg_compute_kzg_proof(
    mk_bytearray(blob, BYTES_PER_BLOB),
    mk_bytearray(z, BYTES_PER_FIELD_ELEMENT));
  if (except_into_buffer(res, KZG_ERROR, buf, sizeof(buf))) return NULL;
  PyObject* proof = PyBytes_FromStringAndSize((const char*) buf, BYTES_PER_PROOF);
  if (!proof) return NULL;
  PyObject* y = PyBytes_FromStringAndSize((const char*) (buf + BYTES_PER_PROOF),
                                              BYTES_PER_FIELD_ELEMENT);
  if (!y) { Py_DECREF(proof); return NULL; }
  PyObject* tup = PyTuple_Pack(2, proof, y);
  Py_DECREF(proof); Py_DECREF(y);
  return tup;
}

PyObject*
py_verify_kzg_proof(
  PyObject* self,
  PyObject* args
) {
  PyObject *c_obj, *z_obj, *y_obj, *p_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &c_obj, &z_obj, &y_obj, &p_obj)) return NULL;
  const uint8_t* c = parse_bytes_of_size(c_obj, BYTES_PER_COMMITMENT, "commitment");
  if (!c) return NULL;
  const uint8_t* z = parse_bytes_of_size(z_obj, BYTES_PER_FIELD_ELEMENT, "z");
  if (!z) return NULL;
  const uint8_t* y = parse_bytes_of_size(y_obj, BYTES_PER_FIELD_ELEMENT, "y");
  if (!y) return NULL;
  const uint8_t* p = parse_bytes_of_size(p_obj, BYTES_PER_PROOF, "proof");
  if (!p) return NULL;
  uint8_t ok = 0;
  lean_object* res = eth_kzg_verify_kzg_proof(
    mk_bytearray(c, BYTES_PER_COMMITMENT),
    mk_bytearray(z, BYTES_PER_FIELD_ELEMENT),
    mk_bytearray(y, BYTES_PER_FIELD_ELEMENT),
    mk_bytearray(p, BYTES_PER_PROOF));
  if (except_into_flag(res, KZG_ERROR, &ok)) return NULL;
  if (ok) Py_RETURN_TRUE; else Py_RETURN_FALSE;
}

PyObject*
py_compute_blob_kzg_proof(
  PyObject* self,
  PyObject* args
) {
  PyObject *blob_obj, *c_obj;
  if (!PyArg_ParseTuple(args, "OO", &blob_obj, &c_obj)) return NULL;
  const uint8_t* blob = parse_bytes_of_size(blob_obj, BYTES_PER_BLOB, "blob");
  if (!blob) return NULL;
  const uint8_t* c = parse_bytes_of_size(c_obj, BYTES_PER_COMMITMENT, "commitment");
  if (!c) return NULL;
  uint8_t out[BYTES_PER_PROOF];
  lean_object* res = eth_kzg_compute_blob_kzg_proof(
    mk_bytearray(blob, BYTES_PER_BLOB),
    mk_bytearray(c, BYTES_PER_COMMITMENT));
  if (except_into_buffer(res, KZG_ERROR, out, BYTES_PER_PROOF)) return NULL;
  return PyBytes_FromStringAndSize((const char*) out, BYTES_PER_PROOF);
}

PyObject*
py_verify_blob_kzg_proof(
  PyObject* self,
  PyObject* args
) {
  PyObject *blob_obj, *c_obj, *p_obj;
  if (!PyArg_ParseTuple(args, "OOO", &blob_obj, &c_obj, &p_obj)) return NULL;
  const uint8_t* blob = parse_bytes_of_size(blob_obj, BYTES_PER_BLOB, "blob");
  if (!blob) return NULL;
  const uint8_t* c = parse_bytes_of_size(c_obj, BYTES_PER_COMMITMENT, "commitment");
  if (!c) return NULL;
  const uint8_t* p = parse_bytes_of_size(p_obj, BYTES_PER_PROOF, "proof");
  if (!p) return NULL;
  uint8_t ok = 0;
  lean_object* res = eth_kzg_verify_blob_kzg_proof(
    mk_bytearray(blob, BYTES_PER_BLOB),
    mk_bytearray(c, BYTES_PER_COMMITMENT),
    mk_bytearray(p, BYTES_PER_PROOF));
  if (except_into_flag(res, KZG_ERROR, &ok)) return NULL;
  if (ok) Py_RETURN_TRUE; else Py_RETURN_FALSE;
}

PyObject*
py_verify_blob_kzg_proof_batch(
  PyObject* self,
  PyObject* args
) {
  PyObject *blobs_obj, *coms_obj, *proofs_obj;
  if (!PyArg_ParseTuple(args, "OOO", &blobs_obj, &coms_obj, &proofs_obj)) return NULL;
  Py_ssize_t nb, nc, np;
  uint8_t* blobs = pack_bytes_sequence(blobs_obj, BYTES_PER_BLOB, &nb, "blob");
  if (!blobs) return NULL;
  uint8_t* coms = pack_bytes_sequence(coms_obj, BYTES_PER_COMMITMENT, &nc, "commitment");
  if (!coms) { PyMem_Free(blobs); return NULL; }
  uint8_t* proofs = pack_bytes_sequence(proofs_obj, BYTES_PER_PROOF, &np, "proof");
  if (!proofs) { PyMem_Free(coms); PyMem_Free(blobs); return NULL; }
  if (nb != nc || nc != np) {
    PyMem_Free(blobs); PyMem_Free(coms); PyMem_Free(proofs);
    PyErr_SetString(PyExc_ValueError, "blobs/commitments/proofs must have equal length");
    return NULL;
  }
  uint8_t ok = 0;
  lean_object* res = eth_kzg_verify_blob_kzg_proof_batch(
    mk_bytearray_array(blobs, nb, BYTES_PER_BLOB),
    mk_bytearray_array(coms, nc, BYTES_PER_COMMITMENT),
    mk_bytearray_array(proofs, np, BYTES_PER_PROOF));
  PyMem_Free(blobs); PyMem_Free(coms); PyMem_Free(proofs);
  if (except_into_flag(res, KZG_ERROR, &ok)) return NULL;
  if (ok) Py_RETURN_TRUE; else Py_RETURN_FALSE;
}

PyObject*
py_compute_cells(
  PyObject* self,
  PyObject* args
) {
  PyObject* blob_obj;
  if (!PyArg_ParseTuple(args, "O", &blob_obj)) return NULL;
  const uint8_t* blob = parse_bytes_of_size(blob_obj, BYTES_PER_BLOB, "blob");
  if (!blob) return NULL;
  size_t total = CELLS_PER_EXT_BLOB * BYTES_PER_CELL;
  uint8_t* out = (uint8_t*) PyMem_Malloc(total);
  if (!out) return PyErr_NoMemory();
  lean_object* res = eth_kzg_compute_cells(
    mk_bytearray(blob, BYTES_PER_BLOB));
  if (except_into_buffer(res, KZG_ERROR, out, total)) {
    PyMem_Free(out);
    return NULL;
  }
  PyObject* list = bytes_list(out, CELLS_PER_EXT_BLOB, BYTES_PER_CELL);
  PyMem_Free(out);
  return list;
}

PyObject*
py_compute_cells_and_kzg_proofs(
  PyObject* self,
  PyObject* args
) {
  PyObject* blob_obj;
  if (!PyArg_ParseTuple(args, "O", &blob_obj)) return NULL;
  const uint8_t* blob = parse_bytes_of_size(blob_obj, BYTES_PER_BLOB, "blob");
  if (!blob) return NULL;
  size_t total = CELLS_PER_EXT_BLOB * (BYTES_PER_CELL + BYTES_PER_PROOF);
  uint8_t* buf = (uint8_t*) PyMem_Malloc(total);
  if (!buf) return PyErr_NoMemory();
  lean_object* res = eth_kzg_compute_cells_and_kzg_proofs(
    mk_bytearray(blob, BYTES_PER_BLOB));
  if (except_into_buffer(res, KZG_ERROR, buf, total)) {
    PyMem_Free(buf);
    return NULL;
  }
  PyObject* tup = cells_and_proofs(buf);
  PyMem_Free(buf);
  return tup;
}

PyObject*
py_compute_verify_cell_kzg_proof_batch_challenge(
  PyObject* self,
  PyObject* args
) {
  PyObject *coms_obj, *com_idx_obj, *cell_idx_obj, *evals_obj, *proofs_obj;
  if (!PyArg_ParseTuple(args, "OOOOO",
        &coms_obj, &com_idx_obj, &cell_idx_obj, &evals_obj, &proofs_obj))
    return NULL;

  Py_ssize_t n_coms, n_com_idx, n_cell_idx, n_proofs;
  /* Declared before any goto so the cleanup label isn't bypassed
   * (the VLA's runtime size makes goto-over-declaration illegal). */
  uint8_t out[BYTES_PER_FIELD_ELEMENT];
  uint8_t* coms = pack_bytes_sequence(coms_obj, BYTES_PER_COMMITMENT, &n_coms, "commitment");
  if (!coms) return NULL;
  uint64_t* com_idx = pack_indices(com_idx_obj, &n_com_idx);
  if (!com_idx) { PyMem_Free(coms); return NULL; }
  uint64_t* cell_idx = pack_indices(cell_idx_obj, &n_cell_idx);
  if (!cell_idx) { PyMem_Free(com_idx); PyMem_Free(coms); return NULL; }

  /* Each `cosets_evals` entry is a list of FIELD_ELEMENTS_PER_CELL field
   * elements (32 bytes each); we pack each list into a CELL-sized buffer. */
  PyObject* fast_evals = PySequence_Fast(evals_obj, "cosets_evals must be a sequence");
  if (!fast_evals) {
    PyMem_Free(cell_idx); PyMem_Free(com_idx); PyMem_Free(coms); return NULL;
  }
  Py_ssize_t n_packed = PySequence_Fast_GET_SIZE(fast_evals);
  uint8_t* packed = (uint8_t*) PyMem_Malloc(n_packed * BYTES_PER_CELL);
  if (!packed) {
    Py_DECREF(fast_evals);
    PyMem_Free(cell_idx); PyMem_Free(com_idx); PyMem_Free(coms);
    return PyErr_NoMemory();
  }
  for (Py_ssize_t i = 0; i < n_packed; i++) {
    PyObject* sub = PySequence_Fast_GET_ITEM(fast_evals, i);
    PyObject* fast_sub = PySequence_Fast(sub, "each cosets_evals[i] must be a sequence");
    if (!fast_sub) goto fail_evals;
    if (PySequence_Fast_GET_SIZE(fast_sub) != (Py_ssize_t) FIELD_ELEMENTS_PER_CELL) {
      Py_DECREF(fast_sub);
      PyErr_SetString(PyExc_ValueError, "each cosets_evals[i] must have FIELD_ELEMENTS_PER_CELL entries");
      goto fail_evals;
    }
    for (Py_ssize_t j = 0; j < (Py_ssize_t) FIELD_ELEMENTS_PER_CELL; j++) {
      PyObject* item = PySequence_Fast_GET_ITEM(fast_sub, j);
      const uint8_t* p = parse_bytes_of_size(item, BYTES_PER_FIELD_ELEMENT, "coset eval");
      if (!p) { Py_DECREF(fast_sub); goto fail_evals; }
      memcpy(packed + i * BYTES_PER_CELL + j * BYTES_PER_FIELD_ELEMENT,
             p, BYTES_PER_FIELD_ELEMENT);
    }
    Py_DECREF(fast_sub);
  }
  Py_DECREF(fast_evals);

  Py_ssize_t n_proofs_check;
  uint8_t* proofs = pack_bytes_sequence(proofs_obj, BYTES_PER_PROOF, &n_proofs_check, "proof");
  if (!proofs) {
    PyMem_Free(packed);
    PyMem_Free(cell_idx); PyMem_Free(com_idx); PyMem_Free(coms);
    return NULL;
  }
  n_proofs = n_proofs_check;

  lean_object* res = eth_kzg_compute_verify_cell_kzg_proof_batch_challenge(
    mk_bytearray_array(coms, n_coms, BYTES_PER_COMMITMENT),
    mk_indices_bytearray(com_idx, n_com_idx),
    mk_indices_bytearray(cell_idx, n_cell_idx),
    mk_bytearray_array(packed, n_packed, BYTES_PER_CELL),
    mk_bytearray_array(proofs, n_proofs, BYTES_PER_PROOF));

  PyMem_Free(proofs);
  PyMem_Free(packed);
  PyMem_Free(cell_idx); PyMem_Free(com_idx); PyMem_Free(coms);

  if (except_into_buffer(res, KZG_ERROR, out, BYTES_PER_FIELD_ELEMENT)) return NULL;
  return PyBytes_FromStringAndSize((const char*) out, BYTES_PER_FIELD_ELEMENT);

fail_evals:
  Py_DECREF(fast_evals);
  PyMem_Free(packed);
  PyMem_Free(cell_idx); PyMem_Free(com_idx); PyMem_Free(coms);
  return NULL;
}

PyObject*
py_verify_cell_kzg_proof_batch(
  PyObject* self,
  PyObject* args
) {
  PyObject *coms_obj, *cell_idx_obj, *cells_obj, *proofs_obj;
  if (!PyArg_ParseTuple(args, "OOOO",
        &coms_obj, &cell_idx_obj, &cells_obj, &proofs_obj)) return NULL;
  Py_ssize_t n_coms, n_idx, n_cells, n_proofs;
  uint8_t* coms = pack_bytes_sequence(coms_obj, BYTES_PER_COMMITMENT, &n_coms, "commitment");
  if (!coms) return NULL;
  uint64_t* idx = pack_indices(cell_idx_obj, &n_idx);
  if (!idx) { PyMem_Free(coms); return NULL; }
  uint8_t* cells = pack_bytes_sequence(cells_obj, BYTES_PER_CELL, &n_cells, "cell");
  if (!cells) { PyMem_Free(idx); PyMem_Free(coms); return NULL; }
  uint8_t* proofs = pack_bytes_sequence(proofs_obj, BYTES_PER_PROOF, &n_proofs, "proof");
  if (!proofs) { PyMem_Free(cells); PyMem_Free(idx); PyMem_Free(coms); return NULL; }

  uint8_t ok = 0;
  lean_object* res = eth_kzg_verify_cell_kzg_proof_batch(
    mk_bytearray_array(coms, n_coms, BYTES_PER_COMMITMENT),
    mk_indices_bytearray(idx, n_idx),
    mk_bytearray_array(cells, n_cells, BYTES_PER_CELL),
    mk_bytearray_array(proofs, n_proofs, BYTES_PER_PROOF));
  PyMem_Free(proofs); PyMem_Free(cells); PyMem_Free(idx); PyMem_Free(coms);
  if (except_into_flag(res, KZG_ERROR, &ok)) return NULL;
  if (ok) Py_RETURN_TRUE; else Py_RETURN_FALSE;
}

PyObject*
py_recover_cells_and_kzg_proofs(
  PyObject* self,
  PyObject* args
) {
  PyObject *cell_idx_obj, *cells_obj;
  if (!PyArg_ParseTuple(args, "OO", &cell_idx_obj, &cells_obj)) return NULL;
  Py_ssize_t n_idx, n_cells;
  uint64_t* idx = pack_indices(cell_idx_obj, &n_idx);
  if (!idx) return NULL;
  uint8_t* cells = pack_bytes_sequence(cells_obj, BYTES_PER_CELL, &n_cells, "cell");
  if (!cells) { PyMem_Free(idx); return NULL; }

  size_t total = CELLS_PER_EXT_BLOB * (BYTES_PER_CELL + BYTES_PER_PROOF);
  uint8_t* buf = (uint8_t*) PyMem_Malloc(total);
  if (!buf) { PyMem_Free(cells); PyMem_Free(idx); return PyErr_NoMemory(); }

  lean_object* res = eth_kzg_recover_cells_and_kzg_proofs(
    mk_indices_bytearray(idx, n_idx),
    mk_bytearray_array(cells, n_cells, BYTES_PER_CELL));
  PyMem_Free(cells); PyMem_Free(idx);

  if (except_into_buffer(res, KZG_ERROR, buf, total)) {
    PyMem_Free(buf);
    return NULL;
  }
  PyObject* tup = cells_and_proofs(buf);
  PyMem_Free(buf);
  return tup;
}

/* leanXMSS wrappers around the `eth_xmss_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_xmss_key_gen(
  lean_object* seed
);

extern lean_object*
eth_xmss_sign(
  lean_object* key,
  uint32_t leaf_index,
  lean_object* msg
);

extern lean_object*
eth_xmss_verify(
  lean_object* pk,
  lean_object* msg,
  lean_object* sig
);

extern lean_object*
eth_xmss_signature_index(
  lean_object* sig
);

/* ---- Local helpers (XMSS-only) --------------------------------------- */

/* Read a Python int in [0, max]; returns 0 on success. */
static int
parse_uint(
  PyObject* obj,
  unsigned long max,
  const char* name,
  unsigned long* out
) {
  if (!PyLong_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s: expected int", name);
    return 1;
  }
  unsigned long v = PyLong_AsUnsignedLong(obj);
  if (v == (unsigned long) -1 && PyErr_Occurred()) return 1;
  if (v > max) {
    PyErr_Format(PyExc_OverflowError, "%s: must be at most %lu, got %lu",
                 name, max, v);
    return 1;
  }
  *out = v;
  return 0;
}

/* ---- The cache of secret keys ---------------------------------------- */

/* Signing from the seed alone builds the top tree and a bottom tree, each costing a key generation.
 *
 * So the extension keeps, per seed, the secret key that key generation returns.
 * It holds the top tree, the last bottom trees it signed in and their top signatures.
 * Signing with it gives the bytes of signing from the seed alone, by a Lean theorem.
 * So the cache changes how long a call takes, never what it returns.
 *
 * Memory: a built tree holds 2^17 - 1 digests, about 22 MiB of Lean objects.
 * A key holds its top tree and up to 8 bottom trees, so the 2 slots hold at most 18 trees.
 * That is about 400 MiB, which no call releases but eviction.
 * A call in flight holds its own key on top of that, until it stores or frees it.
 * A signer uses one seed, so 2 slots keep it warm while a second seed is in use.
 *
 * Secrets: a slot holds the seed and its derived secrets until it is evicted or the process ends.
 * So they outlive the call that passed the seed, key generation included.
 * The caller passes the seed itself on every call, so the API exposes nothing new.
 * Freed slots and keys are not zeroed, as no Lean object is.
 *
 * The cache is not a security boundary, so seeds are compared with a plain `memcmp`.
 * Each wrapper copies the seed first, so a slot is always filed under the seed it was built from.
 *
 * Threads: the lock guards the slots only; no Lean code runs and no key is freed under it.
 * Every stored key is marked multi-threaded first, so Lean never updates it in place.
 * Two threads that sign with one seed at once each store their updated key, and the last stays.
 * The other's new tree is dropped; it costs a rebuild and changes no signature.
 * Under the lock, no thread releases the GIL or reaches a point where a free-threaded build pauses.
 * So a forked child never inherits the lock held. */
#define XMSS_KEY_CACHE_SEEDS 2

/* The longest seed and public key a slot holds.
 * The module refuses to load if the scheme's are longer. */
#define XMSS_KEY_CACHE_SEED_MAX 32
#define XMSS_KEY_CACHE_PUB_KEY_MAX 64

typedef struct {
  uint8_t seed[XMSS_KEY_CACHE_SEED_MAX];
  /* The public key of the seed, which key generation returned with the secret key. */
  uint8_t pk[XMSS_KEY_CACHE_PUB_KEY_MAX];
  /* The secret key of the seed, or NULL for an empty slot. */
  lean_object* key;
  /* The tick of the last lookup or store, to evict the least recently used slot. */
  uint64_t last_use;
} key_slot;

static key_slot key_cache[XMSS_KEY_CACHE_SEEDS];
static uint64_t key_cache_tick;
static PyThread_type_lock key_cache_lock;

int
xmss_key_cache_init(void) {
  if (XMSS_SEED_LEN > XMSS_KEY_CACHE_SEED_MAX || XMSS_PUB_KEY_SIZE > XMSS_KEY_CACHE_PUB_KEY_MAX) {
    PyErr_Format(PyExc_RuntimeError,
                 "XMSS seed of %zu bytes and public key of %zu bytes, the key cache holds at "
                 "most %d and %d", XMSS_SEED_LEN, XMSS_PUB_KEY_SIZE, XMSS_KEY_CACHE_SEED_MAX,
                 XMSS_KEY_CACHE_PUB_KEY_MAX);
    return -1;
  }
  key_cache_lock = PyThread_allocate_lock();
  if (!key_cache_lock) {
    PyErr_NoMemory();
    return -1;
  }
  return 0;
}

/* The slot of a seed, or NULL; the caller holds the lock. */
static key_slot*
key_cache_find(
  const uint8_t* seed
) {
  for (size_t i = 0; i < XMSS_KEY_CACHE_SEEDS; i++) {
    key_slot* slot = &key_cache[i];
    if (slot->key && memcmp(slot->seed, seed, XMSS_SEED_LEN) == 0) return slot;
  }
  return NULL;
}

/* The cached key of a seed, with one reference owned by the caller, or NULL.
 *
 * When `pk_out` is not NULL, it also receives the public key of the seed. */
static lean_object*
key_cache_get(
  const uint8_t* seed,
  uint8_t* pk_out
) {
  lean_object* key = NULL;
  PyThread_acquire_lock(key_cache_lock, WAIT_LOCK);
  key_slot* slot = key_cache_find(seed);
  if (slot) {
    key = slot->key;
    lean_inc(key);
    if (pk_out) memcpy(pk_out, slot->pk, XMSS_PUB_KEY_SIZE);
    slot->last_use = ++key_cache_tick;
  }
  PyThread_release_lock(key_cache_lock);
  return key;
}

/* Store the key of a seed, whose reference the cache takes, with the seed's public key.
 *
 * It fills an empty slot, or evicts the least recently used one.
 * When the seed has a slot already, it replaces its key if `replace` is set, and else drops `key`.
 * Signing replaces, since its key extends the stored one; key generation does not. */
static void
key_cache_put(
  const uint8_t* seed,
  const uint8_t* pk,
  lean_object* key,
  bool replace
) {
  /* Only the new parts are walked: the parts shared with a stored key are marked already.
   * A key that is then dropped was walked for nothing, which only a race causes. */
  lean_mark_mt(key);
  PyThread_acquire_lock(key_cache_lock, WAIT_LOCK);
  key_slot* target = key_cache_find(seed);
  if (target && !replace) {
    PyThread_release_lock(key_cache_lock);
    lean_dec(key);
    return;
  }
  for (size_t i = 0; i < XMSS_KEY_CACHE_SEEDS && !target; i++) {
    if (!key_cache[i].key) target = &key_cache[i];
  }
  if (!target) {
    target = &key_cache[0];
    for (size_t i = 1; i < XMSS_KEY_CACHE_SEEDS; i++) {
      if (key_cache[i].last_use < target->last_use) target = &key_cache[i];
    }
  }
  lean_object* old = target->key;
  memcpy(target->seed, seed, XMSS_SEED_LEN);
  memcpy(target->pk, pk, XMSS_PUB_KEY_SIZE);
  target->key = key;
  target->last_use = ++key_cache_tick;
  PyThread_release_lock(key_cache_lock);
  /* Freeing a key walks its trees, so it runs outside the lock. */
  if (old) lean_dec(old);
}

/* Generate the key pair of a seed: write its public key to `pk_out`, and return the secret key.
 *
 * Returns NULL with a Python exception set on failure. */
static lean_object*
key_gen_seed(
  const uint8_t* seed,
  uint8_t* pk_out
) {
  lean_object* res = eth_xmss_key_gen(mk_bytearray(seed, XMSS_SEED_LEN));
  /* `Except.error` is the first constructor of `Except`, so its tag is 0. */
  if (lean_obj_tag(res) == 0) {
    raise_lean_error(res, XMSS_ERROR);
    return NULL;
  }
  /* The result holds the pair of the public key's bytes and the secret key. */
  lean_object* pair = lean_ctor_get(res, 0);
  lean_object* pk = lean_ctor_get(pair, 0);
  lean_object* key = lean_ctor_get(pair, 1);
  lean_inc(key);
  size_t got = lean_sarray_size(pk);
  if (got == XMSS_PUB_KEY_SIZE) memcpy(pk_out, lean_sarray_cptr(pk), XMSS_PUB_KEY_SIZE);
  lean_dec(res);
  if (got != XMSS_PUB_KEY_SIZE) {
    lean_dec(key);
    PyErr_Format(PyExc_RuntimeError, "Lean returned %zu bytes, expected %zu",
                 got, XMSS_PUB_KEY_SIZE);
    return NULL;
  }
  return key;
}

/* The secret key of a seed, from the cache or from key generation.
 * The caller owns one reference, and `pk_out` receives the public key.
 *
 * A key from key generation is stored, so a later call finds it.
 * A key that another thread stored meanwhile may keep bottom trees, so it is not replaced.
 *
 * Returns NULL with a Python exception set on failure. */
static lean_object*
key_of_seed(
  const uint8_t* seed,
  uint8_t* pk_out
) {
  lean_object* key = key_cache_get(seed, pk_out);
  if (key) return key;
  key = key_gen_seed(seed, pk_out);
  if (!key) return NULL;
  lean_inc(key);
  key_cache_put(seed, pk_out, key, false);
  return key;
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_xmss_key_gen(
  PyObject* self,
  PyObject* args
) {
  PyObject *seed_obj;
  if (!PyArg_ParseTuple(args, "O", &seed_obj)) return NULL;
  const uint8_t* seed_bytes = parse_bytes_of_size(seed_obj, XMSS_SEED_LEN, "seed");
  if (!seed_bytes) return NULL;
  uint8_t seed[XMSS_KEY_CACHE_SEED_MAX];
  memcpy(seed, seed_bytes, XMSS_SEED_LEN);

  uint8_t out[XMSS_KEY_CACHE_PUB_KEY_MAX];
  /* A first signature with this seed then reuses the top tree. */
  lean_object* key = key_of_seed(seed, out);
  if (!key) return NULL;
  lean_dec(key);
  return PyBytes_FromStringAndSize((const char*) out, XMSS_PUB_KEY_SIZE);
}

PyObject*
py_xmss_sign(
  PyObject* self,
  PyObject* args
) {
  PyObject *seed_obj, *index_obj, *msg_obj;
  if (!PyArg_ParseTuple(args, "OOO", &seed_obj, &index_obj, &msg_obj)) return NULL;
  const uint8_t* seed_bytes = parse_bytes_of_size(seed_obj, XMSS_SEED_LEN, "seed");
  if (!seed_bytes) return NULL;
  unsigned long leaf_index;
  if (parse_uint(index_obj, UINT32_MAX, "leaf_index", &leaf_index)) return NULL;
  const uint8_t* msg = parse_bytes_of_size(msg_obj, XMSS_MESSAGE_LEN, "message");
  if (!msg) return NULL;
  uint8_t seed[XMSS_KEY_CACHE_SEED_MAX];
  memcpy(seed, seed_bytes, XMSS_SEED_LEN);

  uint8_t pk[XMSS_KEY_CACHE_PUB_KEY_MAX];
  lean_object* key = key_of_seed(seed, pk);
  if (!key) return NULL;
  /* The export consumes the key, so the caller's reference passes to it. */
  lean_object* pair = eth_xmss_sign(
    key,
    (uint32_t) leaf_index,
    mk_bytearray(msg, XMSS_MESSAGE_LEN));
  /* The pair holds the updated key, kept even when signing fails, and the result. */
  lean_object* updated = lean_ctor_get(pair, 0);
  lean_object* res = lean_ctor_get(pair, 1);
  lean_inc(updated);
  lean_inc(res);
  lean_dec(pair);
  key_cache_put(seed, pk, updated, true);
  uint8_t out[XMSS_SIG_SIZE];
  if (except_into_buffer(res, XMSS_ERROR, out, XMSS_SIG_SIZE)) return NULL;
  return PyBytes_FromStringAndSize((const char*) out, XMSS_SIG_SIZE);
}

PyObject*
py_xmss_verify(
  PyObject* self,
  PyObject* args
) {
  PyObject *pk_obj, *msg_obj, *sig_obj;
  if (!PyArg_ParseTuple(args, "OOO", &pk_obj, &msg_obj, &sig_obj)) return NULL;
  const uint8_t* pk = parse_bytes_of_size(pk_obj, XMSS_PUB_KEY_SIZE, "public key");
  if (!pk) return NULL;
  const uint8_t* msg = parse_bytes_of_size(msg_obj, XMSS_MESSAGE_LEN, "message");
  if (!msg) return NULL;
  const uint8_t* sig = parse_bytes_of_size(sig_obj, XMSS_SIG_SIZE, "signature");
  if (!sig) return NULL;

  uint8_t ok = 0;
  lean_object* res = eth_xmss_verify(
    mk_bytearray(pk, XMSS_PUB_KEY_SIZE),
    mk_bytearray(msg, XMSS_MESSAGE_LEN),
    mk_bytearray(sig, XMSS_SIG_SIZE));
  if (except_into_flag(res, XMSS_ERROR, &ok)) return NULL;
  if (ok) Py_RETURN_TRUE; else Py_RETURN_FALSE;
}

PyObject*
py_xmss_signature_index(
  PyObject* self,
  PyObject* args
) {
  PyObject *sig_obj;
  if (!PyArg_ParseTuple(args, "O", &sig_obj)) return NULL;
  const uint8_t* sig = parse_bytes_of_size(sig_obj, XMSS_SIG_SIZE, "signature");
  if (!sig) return NULL;

  /* The index is below 2^32, so it fits the `UInt64` the export returns. */
  lean_object* res = eth_xmss_signature_index(mk_bytearray(sig, XMSS_SIG_SIZE));
  return except_into_pyint(res, XMSS_ERROR);
}

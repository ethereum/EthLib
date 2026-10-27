/*
 * Out-of-line copies of the `lean.h` helpers the Rust side needs.
 *
 * Most of `lean.h` is `static inline`, so it has no symbol Rust can link to.
 * Each function here wraps one of those helpers and keeps its ownership rule:
 *
 *     lean_obj_arg   : the callee consumes one reference
 *     b_lean_obj_arg : the callee borrows, and the caller keeps its reference
 */
#include <lean/lean.h>
#include <string.h>

/* Module initializers of the umbrella modules this crate exports.
 *
 * Each one runs the initializers of everything it imports, once. */
lean_object* initialize_EthLib_EthLib_Cryptography_Bls(uint8_t builtin);
lean_object* initialize_EthLib_EthLib_Cryptography_Kzg(uint8_t builtin);

/* Defined in the Lean runtime, which ships no header for them. */
void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);
lean_object* lean_io_error_to_string(lean_obj_arg err);

/* Boot the runtime and the exported EthLib modules.
 *
 * Returns the IO result of the first initializer that fails, or of the last one. */
lean_object* ethlib_initialize(void) {
  lean_initialize_runtime_module();

  /* Stop at the first failure: later modules may depend on it. */
  lean_object* res = initialize_EthLib_EthLib_Cryptography_Bls(1);
  if (!lean_io_result_is_ok(res)) return res;
  lean_dec_ref(res);
  res = initialize_EthLib_EthLib_Cryptography_Kzg(1);
  if (!lean_io_result_is_ok(res)) return res;

  /* Objects built so far become persistent: any thread may read them. */
  lean_io_mark_end_initialization();

  /* Start the worker threads that run Lean tasks.
   * Without them, a task runs on the calling thread, and independent work runs in sequence. */
  lean_init_task_manager();
  return res;
}

void ethlib_initialize_thread(void) {
  lean_initialize_thread();
}

void ethlib_finalize_thread(void) {
  lean_finalize_thread();
}

/* The unit value, passed to the size accessors. */
lean_object* ethlib_unit(void) {
  return lean_box(0);
}

void ethlib_dec(lean_obj_arg o) {
  lean_dec(o);
}

/* A new `ByteArray` holding a copy of `len` bytes at `data`. */
lean_object* ethlib_byte_array(const uint8_t* data, size_t len) {
  lean_object* arr = lean_alloc_sarray(1, len, len);
  /* `memcpy` with a null source is undefined even for zero bytes. */
  if (len != 0) memcpy(lean_sarray_cptr(arr), data, len);
  return arr;
}

/* A new, empty `Array` with room for `capacity` elements. */
lean_object* ethlib_array(size_t capacity) {
  return lean_alloc_array(0, capacity);
}

/* Append `item` to `arr`; both references move into the result. */
lean_object* ethlib_array_push(lean_obj_arg arr, lean_obj_arg item) {
  return lean_array_push(arr, item);
}

uint8_t ethlib_io_is_ok(b_lean_obj_arg res) {
  return lean_io_result_is_ok(res);
}

/* The value of a successful IO result, as a new reference. */
lean_object* ethlib_io_take_value(lean_obj_arg res) {
  lean_object* value = lean_io_result_get_value(res);
  /* The value is borrowed from `res`: keep it alive past `res`. */
  lean_inc(value);
  lean_dec(res);
  return value;
}

/* The message of a failed IO result, as a new `String`. */
lean_object* ethlib_io_take_error(lean_obj_arg res) {
  lean_object* err = lean_io_result_get_error(res);
  /* The error is borrowed from `res`, and the conversion consumes one reference. */
  lean_inc(err);
  lean_dec(res);
  return lean_io_error_to_string(err);
}

uint8_t ethlib_unbox_u8(b_lean_obj_arg o) {
  return (uint8_t) lean_unbox(o);
}

size_t ethlib_byte_array_size(b_lean_obj_arg o) {
  return lean_sarray_size(o);
}

const uint8_t* ethlib_byte_array_data(b_lean_obj_arg o) {
  return lean_sarray_cptr(o);
}

/* The bytes of a `String`, without the terminating zero. */
const char* ethlib_string_data(b_lean_obj_arg o) {
  return lean_string_cstr(o);
}

size_t ethlib_string_size(b_lean_obj_arg o) {
  /* Lean counts the terminating zero in the byte size. */
  return lean_string_size(o) - 1;
}

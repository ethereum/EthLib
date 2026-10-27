//! Owned Lean objects, and the runtime they live in.
//!
//! Every Lean object carries a reference count.
//! An exported Lean function consumes one reference to each argument and returns one new reference.
//!
//! ```text
//!     Rust                          Lean export
//!     Object::byte_array(..)  ──►   argument (consumed)
//!     Object (dropped here)   ◄──   IO result (owned)
//! ```

use std::cell::Cell;
use std::ptr::NonNull;
use std::slice;
use std::sync::OnceLock;

use crate::Error;

/// The opaque C type `lean_object`.
#[repr(C)]
pub(crate) struct LeanObject {
    _opaque: [u8; 0],
}

// The out-of-line `lean.h` helpers, compiled from `src/shim.c`.
unsafe extern "C" {
    fn ethlib_initialize() -> *mut LeanObject;
    fn ethlib_initialize_thread();
    fn ethlib_finalize_thread();
    fn ethlib_unit() -> *mut LeanObject;
    fn ethlib_dec(o: *mut LeanObject);
    fn ethlib_byte_array(data: *const u8, len: usize) -> *mut LeanObject;
    fn ethlib_array(capacity: usize) -> *mut LeanObject;
    fn ethlib_array_push(arr: *mut LeanObject, item: *mut LeanObject) -> *mut LeanObject;
    fn ethlib_io_is_ok(res: *const LeanObject) -> u8;
    fn ethlib_io_take_value(res: *mut LeanObject) -> *mut LeanObject;
    fn ethlib_io_take_error(res: *mut LeanObject) -> *mut LeanObject;
    fn ethlib_unbox_u8(o: *const LeanObject) -> u8;
    fn ethlib_byte_array_size(o: *const LeanObject) -> usize;
    fn ethlib_byte_array_data(o: *const LeanObject) -> *const u8;
    fn ethlib_string_data(o: *const LeanObject) -> *const u8;
    fn ethlib_string_size(o: *const LeanObject) -> usize;
}

/// The outcome of booting the runtime, shared by every thread.
static RUNTIME: OnceLock<Result<(), String>> = OnceLock::new();

thread_local! {
    /// This thread's registration with the Lean runtime.
    static THREAD: Thread = Thread::attach();
}

/// A thread registered with the Lean runtime.
///
/// Lean keeps per-thread allocator state.
/// A thread Lean did not spawn must register before it allocates, and release that state on exit.
struct Thread {
    /// Whether this thread registered itself, and so must release on exit.
    ///
    /// The thread that boots the runtime is registered by the boot itself.
    registered: Cell<bool>,
}

impl Thread {
    /// Boot the runtime if no thread has, then register the current thread.
    fn attach() -> Self {
        // The first thread to arrive boots the runtime, and is registered by that boot.
        let mut booted_here = false;
        RUNTIME.get_or_init(|| {
            booted_here = true;
            boot()
        });
        if !booted_here {
            // SAFETY: the runtime is booted, and this thread has not registered yet.
            unsafe { ethlib_initialize_thread() };
        }
        Self { registered: Cell::new(!booted_here) }
    }
}

impl Drop for Thread {
    fn drop(&mut self) {
        if self.registered.get() {
            // SAFETY: this thread registered in `attach` and makes no further Lean call.
            unsafe { ethlib_finalize_thread() };
        }
    }
}

/// Initialize the runtime and the exported modules, once per process.
fn boot() -> Result<(), String> {
    // SAFETY: `RUNTIME` runs this exactly once, before any other Lean call.
    let res = unsafe { Object::from_raw(ethlib_initialize()) };
    // SAFETY: a module initializer returns an IO result of `Unit`.
    unsafe { res.into_io() }.map(drop).map_err(|err| err.to_string())
}

/// Make the current thread ready to call Lean.
///
/// # Panics
///
/// Panics if the Lean modules failed to initialize.
/// That means a broken build, not bad input, so no caller can recover from it.
pub(crate) fn enter() {
    THREAD.with(|_| ());
    if let Some(Err(message)) = RUNTIME.get() {
        panic!("the EthLib Lean modules failed to initialize: {message}");
    }
}

/// The unit value, the only argument of the size accessors.
pub(crate) fn unit() -> *mut LeanObject {
    // SAFETY: the unit value is a tagged scalar, not an allocation.
    unsafe { ethlib_unit() }
}

/// One owned reference to a Lean object.
///
/// Dropping it releases the reference.
/// It is neither `Send` nor `Sync`: the object belongs to the thread that made it.
pub(crate) struct Object(NonNull<LeanObject>);

impl Object {
    /// Take ownership of a reference returned by Lean.
    ///
    /// # Safety
    ///
    /// `raw` is a live Lean object, and the caller owns one reference to it.
    unsafe fn from_raw(raw: *mut LeanObject) -> Self {
        Self(NonNull::new(raw).expect("Lean never returns a null object"))
    }

    /// Give up ownership, to pass the reference to a function that consumes it.
    pub(crate) fn into_raw(self) -> *mut LeanObject {
        let raw = self.0.as_ptr();
        // The consumer releases the reference now, so this handle must not.
        std::mem::forget(self);
        raw
    }

    /// A new `ByteArray` holding a copy of `bytes`.
    pub(crate) fn byte_array(bytes: &[u8]) -> Self {
        enter();
        // SAFETY: `bytes` is valid for `bytes.len()` reads, and the result is a new reference.
        unsafe { Self::from_raw(ethlib_byte_array(bytes.as_ptr(), bytes.len())) }
    }

    /// A new `Array ByteArray`, one element per byte string.
    pub(crate) fn byte_arrays<B: AsRef<[u8]>>(items: &[B]) -> Self {
        enter();
        // SAFETY: an empty array is a new reference.
        let mut arr = unsafe { Self::from_raw(ethlib_array(items.len())) };
        for item in items {
            let item = Self::byte_array(item.as_ref());
            // SAFETY: the push consumes both references and returns a new one.
            arr = unsafe { Self::from_raw(ethlib_array_push(arr.into_raw(), item.into_raw())) };
        }
        arr
    }

    /// Run the IO result this object holds.
    ///
    /// # Errors
    ///
    /// Returns the error the Lean action threw, as its message.
    ///
    /// # Safety
    ///
    /// The object is an `EIO IO.Error α` result, as every exported IO action returns.
    unsafe fn into_io(self) -> Result<Self, Error> {
        // SAFETY: the object is an IO result, which the caller guarantees.
        let ok = unsafe { ethlib_io_is_ok(self.0.as_ptr()) } != 0;
        let raw = self.into_raw();
        if ok {
            // SAFETY: both helpers consume the result and return a new reference.
            Ok(unsafe { Self::from_raw(ethlib_io_take_value(raw)) })
        } else {
            // SAFETY: as above, and the message is a `String`.
            let message = unsafe { Self::from_raw(ethlib_io_take_error(raw)) };
            // SAFETY: the object is a `String`.
            Err(Error::new(unsafe { message.string() }))
        }
    }

    /// The bytes of a `ByteArray`.
    ///
    /// # Safety
    ///
    /// The object is a `ByteArray`.
    unsafe fn bytes(&self) -> &[u8] {
        let raw = self.0.as_ptr();
        // SAFETY: a `ByteArray` holds `size` initialized bytes, alive as long as the object.
        unsafe { slice::from_raw_parts(ethlib_byte_array_data(raw), ethlib_byte_array_size(raw)) }
    }

    /// The text of a `String`.
    ///
    /// # Safety
    ///
    /// The object is a `String`.
    unsafe fn string(&self) -> String {
        let raw = self.0.as_ptr();
        // SAFETY: a `String` holds `size` bytes of UTF-8, alive as long as the object.
        let bytes = unsafe { slice::from_raw_parts(ethlib_string_data(raw), ethlib_string_size(raw)) };
        // Lean strings are UTF-8 by construction, but a lossy copy costs nothing here.
        String::from_utf8_lossy(bytes).into_owned()
    }
}

impl Drop for Object {
    fn drop(&mut self) {
        // SAFETY: this handle owns one reference, released exactly once here.
        unsafe { ethlib_dec(self.0.as_ptr()) }
    }
}

/// Run an exported action that returns `IO ByteArray`.
///
/// # Errors
///
/// Returns the error the action threw.
///
/// # Safety
///
/// `res` is the owned result of an exported action of type `IO ByteArray`.
pub(crate) unsafe fn run_bytes(res: *mut LeanObject) -> Result<Vec<u8>, Error> {
    // SAFETY: the caller passes an owned `IO ByteArray` result.
    let value = unsafe { Object::from_raw(res).into_io() }?;
    // SAFETY: the value of an `IO ByteArray` is a `ByteArray`.
    Ok(unsafe { value.bytes() }.to_vec())
}

/// Run an exported action that returns `IO UInt8`, read as a boolean.
///
/// # Errors
///
/// Returns the error the action threw.
///
/// # Safety
///
/// `res` is the owned result of an exported action of type `IO UInt8`.
pub(crate) unsafe fn run_bool(res: *mut LeanObject) -> Result<bool, Error> {
    // SAFETY: the caller passes an owned `IO UInt8` result.
    let value = unsafe { Object::from_raw(res).into_io() }?;
    // SAFETY: the value of an `IO UInt8` is a boxed `UInt8`.
    Ok(unsafe { ethlib_unbox_u8(value.0.as_ptr()) } != 0)
}

//! Lean outputs computed once and shared by every case that needs them.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, OnceLock};

/// A cache of one function's results, keyed by the bytes of its arguments.
///
/// Many cases build on the same commitment, proof or cells.
/// The first case to ask computes the value, and any case asking meanwhile waits for it.
pub(crate) struct Memo<T> {
    /// One slot per input, filled once.
    slots: Mutex<BTreeMap<Vec<u8>, Arc<OnceLock<T>>>>,
}

impl<T: Clone> Memo<T> {
    /// An empty cache.
    pub(crate) const fn new() -> Self {
        Self { slots: Mutex::new(BTreeMap::new()) }
    }

    /// The value for `arguments`, computed by `compute` on first use.
    pub(crate) fn get(&self, arguments: &[&[u8]], compute: impl FnOnce() -> T) -> T {
        // Each argument is prefixed with its length, so two splits of the same bytes differ.
        //
        //     (ab, c) → 2 a b 1 c
        //     (a, bc) → 1 a 2 b c
        let mut key = Vec::new();
        for argument in arguments {
            key.extend_from_slice(&argument.len().to_le_bytes());
            key.extend_from_slice(argument);
        }

        // Hold the map lock only to find the slot, so different keys compute in parallel.
        let slot =
            Arc::clone(self.slots.lock().expect("no case panics while holding the lock").entry(key).or_default());
        slot.get_or_init(compute).clone()
    }
}

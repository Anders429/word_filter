/// Shared utility functions used throughout the rest of the crate.

use core::hint::unreachable_unchecked;

/// Behaves like `unreachable!()` when `debug_assertions` are on, `panic!()`ing when run, but
/// behaves like `core::hint::unreachable_unchecked` otherwise.
///
/// This is useful because the code panics in development, but on release the code is simply
/// optimized away. Note that this optimization will cause undefined behavior in release if it is
/// used incorrectly.
///
/// # Safety
/// The caller must make sure this is never run.
#[inline(always)]
pub(crate) unsafe fn debug_unreachable() -> ! {
    if cfg!(debug_assertions) {
        unreachable!()
    } else {
        unreachable_unchecked()
    }
}

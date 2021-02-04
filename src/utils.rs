use core::hint::unreachable_unchecked;

#[inline(always)]
pub(crate) unsafe fn debug_unreachable() -> ! {
    if cfg!(debug_assertions) {
        unreachable!()
    } else {
        unreachable_unchecked()
    }
}

use core::hint::unreachable_unchecked;

pub(crate) unsafe fn debug_unreachable() -> ! {
    if cfg!(debug_assertions) {
        unreachable!()
    } else {
        unreachable_unchecked()
    }
}

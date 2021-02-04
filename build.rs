fn main() {
    // To enable #[track_caller] on utils::debug_unreachable()
    autocfg::new().emit_rustc_version(1, 46);
}

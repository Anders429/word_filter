#[cfg(test)]
mod tests {
    include!(concat!(env!("OUT_DIR"), "/codegen.rs"));

    #[test]
    fn word() {
        assert!(FILTER.check("foo"));
        assert_eq!(FILTER.find("foo").collect::<Vec<_>>(), vec!["foo"]);
        assert_eq!(FILTER.censor("foo"), "***");
    }

    #[test]
    fn exception() {
        assert!(!FILTER.check("foobar"));
        assert_eq!(
            FILTER.find("foobar").collect::<Vec<_>>(),
            Vec::<&str>::new()
        );
        assert_eq!(FILTER.censor("foobar"), "foobar");
    }

    #[test]
    fn separator() {
        assert!(FILTER.check("f o o"));
        assert_eq!(FILTER.find("f o o").collect::<Vec<_>>(), vec!["foo"]);
        assert_eq!(FILTER.censor(" f o o "), " ***** ");
    }

    #[test]
    fn alias() {
        assert!(FILTER.check("Foo"));
        assert_eq!(FILTER.find("Foo").collect::<Vec<_>>(), vec!["foo"]);
        assert_eq!(FILTER.censor("Foo"), "***");
    }
}

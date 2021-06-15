use integration_codegen::*;
use word_filter::censor;

#[test]
fn find() {
    assert_eq!(WORD.find("foo").collect::<Vec<_>>(), vec!["foo"]);
}

#[test]
fn check() {
    assert!(WORD.check("foo"));
    assert!(!WORD.check("bar"));
}

#[test]
fn check_only_partial() {
    assert!(!WORD.check("fo"));
}

#[test]
fn censor() {
    assert_eq!(WORD.censor("foo"), "***");
}

#[test]
fn censor_with() {
    assert_eq!(
        WORD.censor_with("foo", censor::replace_words_with!("<censored>")),
        "<censored>"
    );
}

#[test]
fn exceptions() {
    assert_eq!(
        MULTIPLE_EXCEPTIONS.find("foo").collect::<Vec<_>>(),
        vec!["foo"]
    );
    assert!(MULTIPLE_EXCEPTIONS
        .find("afoo")
        .collect::<Vec<_>>()
        .is_empty());
    assert!(MULTIPLE_EXCEPTIONS
        .find("foob")
        .collect::<Vec<_>>()
        .is_empty());
    assert!(MULTIPLE_EXCEPTIONS
        .find("cfood")
        .collect::<Vec<_>>()
        .is_empty());
}

#[test]
fn exceptions_and_matches() {
    assert_eq!(EXCEPTION.find("foobarfoo").collect::<Vec<_>>(), vec!["foo"]);
}

#[test]
fn separators() {
    assert_eq!(SEPARATOR.find("f oo").collect::<Vec<_>>(), vec!["foo"]);
}

#[test]
fn separator_between_repeated_characters() {
    assert_eq!(
        BAR_SEPARATOR.find("b a a r").collect::<Vec<_>>(),
        vec!["bar"]
    );
    assert_eq!(BAR_SEPARATOR.censor(" b a a r "), " ******* ");
}

#[test]
fn aliases() {
    assert_eq!(ALIAS.find("foo").collect::<Vec<_>>(), vec!["foo"]);
    assert_eq!(ALIAS.find("fao").collect::<Vec<_>>(), vec!["foo"]);
    assert_eq!(ALIAS.find("foa").collect::<Vec<_>>(), vec!["foo"]);
    assert_eq!(ALIAS.find("faa").collect::<Vec<_>>(), vec!["foo"]);
}

#[test]
fn aliases_on_aliases() {
    assert_eq!(ALIAS_ON_ALIAS.find("foo").collect::<Vec<_>>(), vec!["foo"]);
    assert_eq!(ALIAS_ON_ALIAS.find("fbo").collect::<Vec<_>>(), vec!["foo"]);
    assert_eq!(ALIAS_ON_ALIAS.find("fob").collect::<Vec<_>>(), vec!["foo"]);
    assert_eq!(ALIAS_ON_ALIAS.find("fbb").collect::<Vec<_>>(), vec!["foo"]);
}

#[test]
fn merged_aliases() {
    assert_eq!(MERGED_ALIASES.find("cgfr").collect::<Vec<_>>(), vec!["bar"]);
}

#[test]
fn merged_aliases_contiguous() {
    assert_eq!(
        MERGED_ALIASES_CONTIGUOUS.find("bcdefi").collect::<Vec<_>>(),
        vec!["ahj"]
    );
    assert_eq!(
        MERGED_ALIASES_CONTIGUOUS.find("bgi").collect::<Vec<_>>(),
        vec!["ahj"]
    );
}

#[test]
fn merged_aliases_over_full_match() {
    assert_eq!(
        MERGED_ALIASES_OVER_FULL_MATCH.find("w").collect::<Vec<_>>(),
        vec!["bar"]
    );
}

#[test]
fn recursive_alias_no_overflow() {
    assert_eq!(
        RECURSIVE_ALIASES.find("abr").collect::<Vec<_>>(),
        vec!["bar"]
    );
}

#[test]
fn alias_after_separator() {
    assert_eq!(
        SEPARATOR_AND_ALIAS.find("b Ar").collect::<Vec<_>>(),
        vec!["bar"]
    );
}

#[test]
fn separator_at_front_and_back_of_match() {
    assert_eq!(SEPARATOR.censor("bar foo bar"), "bar *** bar");
}

#[test]
fn censor_repeating() {
    assert_eq!(MULTIPLE_WORDS.censor("fbar"), "f***");
}

#[test]
fn censor_repeated_alias() {
    assert_eq!(MULTIPLE_WORDS_AND_ALIAS.censor("fbaAaAaAar"), "f*********");
}

#[test]
fn separator_in_match_filled_with_smaller_match() {
    assert_eq!(
        WORD_IN_WORD_WITH_SEPARATOR_AND_ALIAS
            .find("foo baz")
            .collect::<Vec<_>>(),
        vec!["foobar"]
    );
}

#[test]
fn graphemes() {
    assert_eq!(GRAPHEME.find("bãr").collect::<Vec<_>>(), vec!["bãr"]);
}

#[test]
fn repeated_graphemes() {
    assert_eq!(GRAPHEME.find("bããr").collect::<Vec<_>>(), vec!["bãr"]);
}

#[test]
fn grapheme_in_alias() {
    assert_eq!(
        GRAPHEME_IN_ALIAS.find("bãr").collect::<Vec<_>>(),
        vec!["bar"]
    );
}

#[test]
fn alias_on_grapheme() {
    assert_eq!(
        ALIAS_ON_GRAPHEME.find("bõr").collect::<Vec<_>>(),
        vec!["bãr"]
    );
}

#[test]
fn grapheme_at_root() {
    assert_eq!(
        GRAPHEME_AT_ROOT.find("ãbc").collect::<Vec<_>>(),
        vec!["ãbc"]
    );
}

#[test]
fn censor_combining_separator() {
    assert_eq!(COMBINING_SEPARATOR.censor("foõ"), "***");
}

#[test]
fn censor_combining_separator_after_repetition() {
    assert_eq!(COMBINING_SEPARATOR.censor("fooõ"), "****");
}

#[test]
fn do_not_censor_combining_separator_on_other_separator() {
    assert_eq!(COMBINING_SEPARATOR.censor("foo \u{303}"), "*** \u{303}");
}

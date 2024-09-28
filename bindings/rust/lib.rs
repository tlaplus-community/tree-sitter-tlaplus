//! This crate provides Tlaplus language support for the [tree-sitter][] parsing library.
//!
//! Typically, you will use the [language][language func] function to add this language to a
//! tree-sitter [Parser][], and then use the parser to parse some code:
//!
//! ```
//! use tree_sitter::Parser;
//!
//! let code = r#"
//! VARIABLE clock
//!
//! Init == clock \in {0, 1}
//!
//! Tick == IF clock = 0 THEN clock' = 1 ELSE clock' = 0
//!
//! Spec == Init /\ [][Tick]_<<clock>>
//! "#;
//! let mut parser = Parser::new();
//! let language = tree_sitter_tlaplus::LANGUAGE;
//! parser
//!     .set_language(&language.into())
//!     .expect("Error loading Tlaplus parser");
//! let tree = parser.parse(code, None).unwrap();
//! assert!(!tree.root_node().has_error());
//! ```
//!
//! [Language]: https://docs.rs/tree-sitter/*/tree_sitter/struct.Language.html
//! [language func]: fn.language.html
//! [Parser]: https://docs.rs/tree-sitter/*/tree_sitter/struct.Parser.html
//! [tree-sitter]: https://tree-sitter.github.io/

use tree_sitter_language::LanguageFn;

extern "C" {
    fn tree_sitter_tlaplus() -> *const ();
}

/// The tree-sitter [`LanguageFn`] for this grammar.
pub const LANGUAGE: LanguageFn = unsafe { LanguageFn::from_raw(tree_sitter_tlaplus) };

/// The content of the [`node-types.json`][] file for this grammar.
///
/// [`node-types.json`]: https://tree-sitter.github.io/tree-sitter/using-parsers#static-node-types
pub const NODE_TYPES: &'static str = include_str!("../../src/node-types.json");

/// The syntax highlighting query for this language.
pub const HIGHLIGHT_QUERY: &'static str = include_str!("../../queries/highlights.scm");

// The locals tagging query for this language.
pub const LOCALS_QUERY: &'static str = include_str!("../../queries/locals.scm");

/// The symbol tagging query for this language.
// pub const TAGS_QUERY: &'static str = include_str!("../../queries/tags.scm");

#[cfg(test)]
mod tests {
    #[test]
    fn test_can_load_grammar() {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&super::LANGUAGE.into())
            .expect("Error loading Tlaplus parser");
    }
}

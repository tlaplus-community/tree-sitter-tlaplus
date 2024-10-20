use tree_sitter::{Parser, Query, QueryCursor};
use streaming_iterator::StreamingIterator;

fn main() {
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_tlaplus::LANGUAGE.into())
        .expect("Error loading TLA+ grammar");
    let source_code = r#"
        ---- MODULE Test ----
        op ≜ ∀ n ∈ ℕ : n ≥ 0
        ===="#;
    let tree = parser.parse(source_code, None).unwrap();
    println!("{}", tree.root_node().to_sexp());

    let query = Query::new(
        &tree_sitter_tlaplus::LANGUAGE.into(),
        "(def_eq \"≜\") @capture",
    )
    .unwrap();
    let mut cursor = QueryCursor::new();
    let mut captures = cursor.matches(&query, tree.root_node(), "".as_bytes());
    while let Some(capture) = captures.next() {
        println!("{:?}", capture);
    }
}

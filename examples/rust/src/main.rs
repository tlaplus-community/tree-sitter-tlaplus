use tree_sitter::{Parser};

fn main() {
    let mut parser = Parser::new();
    parser.set_language(tree_sitter_tlaplus::language()).expect("Error loading TLA+ grammar");
    let source_code = r#"
        ---- MODULE Test ----
        f(x) == x
        ===="#;
    let tree = parser.parse(source_code, None).unwrap();
    println!("{:#?}", tree);
    tree.get_root();
}


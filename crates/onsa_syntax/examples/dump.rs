//! `cargo run -p onsa_syntax --example dump -- file.onsa`: print the AST.

fn main() {
    let path = std::env::args().nth(1).expect("usage: dump <file.onsa>");
    let text = std::fs::read_to_string(&path).expect("read file");
    let parsed = onsa_syntax::parse(onsa_diag::FileId(0), &text);
    print!("{}", onsa_syntax::dump(&parsed.ast));
    for d in &parsed.diagnostics {
        eprintln!("{} {} @{}..{}", d.code.as_str(), d.message, d.span.start, d.span.end);
    }
}

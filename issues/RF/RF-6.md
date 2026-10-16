+++
status = "OPEN"
+++
# RF-6 構文解析器の内部の重複

- 内容: `PatReader` と `parse_pattern_alt`、`parse_type` の三通り、`MoveExpr` の節を作る場所 4 つ、`dump` と `fmt` の `parens`、`operand()` が字句から読み直す W3-21/b の指摘 R2
  - RF/b（単位 1）の再確認で残った置き場所の指摘（後に回す。RF-6 と同じ回）:
    - (A) コメントの述語が一つになったのは `Lines` と `Cursor::comment()` の二か所だけで、`is_trivia`（ブロックコメントを含まない）を読む約 25 か所（`parser.rs`、`cst.rs`、`guard.rs`、`spaces.rs`、`assign.rs` など）と、局所の `matches!(… Comment | DocComment …)`（`foreign/paths.rs`、`flow.rs`、`semicolons.rs`、`edits.rs` の `move_up`、`onsa_tests/src/fix_contract.rs`）が残る。
      - `Parser::end_with` が記録する最後のトークンがブロックコメントになりうる食い違いも残る（出力の差は作れなかった）。
    - (C) 構文解析器の E0003 の候補を作る `move_up` が他言語の形の表の `foreign/edits.rs` にある（役割と置き場所が合わない）。
    - (D) `token_kinds!` のマクロの本体を rustfmt が整形しない。

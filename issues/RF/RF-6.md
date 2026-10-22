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
  - **リファクタリングの候補（9 回目）:**
    - W3-21/b の指摘 R2（`operand()` がトークンから頂点を読み直す。`reads_as_expr` の木を返して AST から `Operand` を作る）、
    - 指摘 R3（検出の入口が `FloatPattern` の行だけで、一つの検出が複数の行を選ぶことを登録簿の型に）、
    - 指摘 R4（`interpolated` が `foreign/guard.rs` にありパーサーが呼ぶ。字句の事実は字句の段へ）、
    - 指摘 R6（`Why::Differ` を理由の列挙型にし、行ごとの note を分ける。E0002 の文面が候補を作れない理由を言わない、指摘 12）。
    - W3-09/b の指摘 S1 の 6（`parse_type` の三通りを `ClockPolicy` で一つに）と 8（`foreign/flow.rs` の位置の判断、`typeish` の閉包）。
    - 報告は 9 回目の scratchpad の `w321b/report.md`・`w309b/report.md`。
  - **リファクタリングの候補（時期は別に決める）:** W3-19/b の報告 `scratchpad/w319b/report.md` の節（`foreign.rs` の型引数の塊を `foreign/type_args.rs` に、`body.rs` の E0200 の三か所、`children` の集約など）も材料にする。
    - W3-19 は見積もり 540 行に対し正味約 566 行。
    - 利用者はソースの肥大を気にしている（2026-10-09、W3-15 の報告で）。
      - 今は注意だけにし、本格的なリファクタリングは別の時期に行う。
      - W3-15 で `crates/onsa_syntax/src/foreign.rs` が約 2100 行（S-317 の部分は約 230 行）、`crates/onsa_tests/src/fix_contract.rs` の器の直しが約 300 行になった。
      - W3-15/b の報告の「リファクタリングの候補」の節（分けられる単位、`PatReader` と `parse_pattern_alt` の重複、使われない枝）を材料にする。
      - 作業の見積もりを出すときは、見積もりと実際の行数の差も記録する。
  - **リファクタリングの候補（時期は別に決める）:**
    - W3-20/b（2026-10-09、報告は 8 回目の scratchpad の `w320b/report.md`）:
      - 呼び先の判定が parser の関門・`names_a_path`・`callee_expression`・`is_postfix_chain` / `removable_parens`・`is_value_callee` に分かれる（W4-12 が 5 つ目を足す。直しの票で一部を一つの述語にした）、
      - リテラルの直後の `(` の判定が 3 か所（バイト・トークン・`Int`）、
      - `MoveExpr` の節を作る場所が 4 つ、
      - `dump.rs` と `fmt.rs` の `parens` の書き方の重複、
      - `parser.rs` の `in_type()` が `lower::class` に依存する（層の向き）。
- 判断（2026-10-19、親）: X-6 の手順 1（44 回目）: (D) の `token_kinds!` は直さない（外部の crate を足さずに、列挙と `ALL` を一つの並びから出す保証を保つ書き方が無い）。
  R2 の `operand()` は X-6 に入れない（読めない入力では字句の読みが残り判断が一つにならず、出力が変わりうる）。`PatReader` を消す案（W3-15/b）は出力が変わりうる候補として残す。
  新しい候補: `lower.rs` の `failed_kind` と `item_kind` の二通りの読み、括弧の対の判断が 4 か所（`parser.rs`・`scan.rs`・`foreign/guard.rs`・`foreign/assign.rs`）。済んだ項目と X-6 で行う項目は `issues/X/X-6/step1/A.md`

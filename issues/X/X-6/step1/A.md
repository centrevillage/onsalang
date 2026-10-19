# X-6 手順 1 の調べ: 領域 A（構文解析器と AST）の修正方針

確かめたコードは dev の ee6a2bd（2026-10-19）。行番号はその版のもの。コードは変えず、ビルドもしていない。
確かめは `rg`・`git log`・`refactor.py sizes`、`target/debug/onsa`（2026-10-19 13:08 のビルド）への小さな入力だけ。

材料の前提: 領域の票に挙げた前の回の scratchpad（`w307b`・`w309b`・`w319b`・`w306b2`・`w306b1a`）は、ディレクトリだけが残り、中のファイルは無い（`ls -la` で 0 件）。
そのため、全ての項目を RF の本文と今のコードだけで判断した（5 章）。
**追記（第 2 版）:** 親が取り戻した材料（`scratchpad/x6/materials/` の下）の該当の節を読み、項目を補った。変わった所には「〔第 2 版〕」と書いた。第 1 版は同じディレクトリの `plan.v1.md`。

分類の語: **保つ**・**変える**・**決定** は共通の票のとおり。加えて、**済み**（後の作業で直っていて、することが無い）と **他の領域**（別の領域の票が扱う）を使う。

## 1. 項目の表

見積もりは、テストを除いて変える行。移すだけの行は括弧に別に書く。

| 項目 | 今もあるか（確かめた所） | 分類 | 〔危険〕 | 触るファイル（関数） | 読むだけのファイル | 見積もり（変える行） |
|---|---|---|---|---|---|---|
| A1 RF-5 強弱の閉包 3 か所 | ほぼ済み。`parser/chain.rs:9` の `tighter` と `lower.rs:1155` の閉包は、どちらも `OpGroup::stronger` を呼んで `ast::Chain` を使う。残りは `chain.rs` の一行の包みだけ。`groups.rs:319` の `Order::tighter` は仮の強弱を足す別の役 | 保つ | なし | `parser/chain.rs`（`tighter` を消して `OpGroup::stronger` を渡す。〔第 2 版〕`parser::Chain` の名を `ast::Chain` と重ならない名に） | `ast.rs`（`Chain`、`OpGroup::stronger`） | 10 |
| A2 RF-5 `groups.rs` が `Flat::new` で平らに戻して読み直す | ある。`groups.rs:60` で全ての鎖を `Flat::new` にし、`Flat::check`（`:556`）が `Order::of_the_spec()` で読み直した木の辺で E0010 を判定する | 保つ | なし | `groups.rs`（`check`、`Flat::check` を判定と候補に分ける） | `ast.rs`、`lower.rs`（`chain`） | 60 |
| A3 RF-5 `key()`・`GROUPS`・`KEYS` が位置で対応 | ある（`groups.rs:276〜298`） | 保つ | なし | `groups.rs`（`KEYS`・`key`・`GROUPS`） | `ast.rs`（`BinOp`、`OpGroup`） | 25 |
| A4 RF-5 `children()` の 3 か所 | ある（`onsa_sema/src/flow.rs:1595`、`onsa_core/src/lower/flow.rs:559`、`onsa_driver/src/graph.rs:142`） | 他の領域（C1 の RF-8） | — | — | — | 0 |
| A5 RF-5 パーサの高さと AST の木の高さを突き合わせるテスト | 半分ある。`cst_tests.rs:400` の `levels` は CST の上でパーサの `Chain` で数え直すだけで、AST の木（`lower.rs` の `chain` が作る）とは比べていない | 保つ（テストだけ） | なし | `cst_tests.rs`（テストを足す） | `lower.rs`、`parser/chain.rs` | 0（テスト約 40） |
| A6 RF-5 `groups.rs` を判定・読みの列挙・候補・入れ子の確かめに分ける | ある。テストを除いて 745 行。入れ子の上限の確かめ（`Limit`・`nests_too_deep`・`Counting`・`TOO_DEEP_RULE`、`:458〜548`）は E0010 と無関係に `operands.rs`・`foreign/flow.rs`・`foreign.rs` が使う | 保つ | なし | `groups.rs`、新しい `nesting.rs`、使う側の `use`（`operands.rs`、`foreign.rs`、`foreign/flow.rs`、`parser.rs`）。〔第 2 版〕`foreign/flow.rs` の `clocks`（`:155〜163`）の上限の確かめの重複 | — | 40（移す約 230） |
| A7 RF-6 (A) コメントの述語 | 一部ある。`is_trivia`（`token.rs:229`、文書なし）を読む所は 27（テストを除く）。局所の `matches!` は `foreign/flow.rs:245`、`foreign/paths.rs:250`、`docs.rs:74`、`parser/items.rs:21,75`。どれも集合が違い、意図した集合に見える | 保つ | なし | `token.rs`（`is_trivia` に文書、局所の集合に名前）、上の 5 か所 | `onsa_tests/src/fix_contract.rs`（領域 D の大きいファイル） | 20 |
| A8 RF-6 (A) `Parser::end_with` の最後のトークンがブロックコメントになりうる | ある（`parser/file.rs:206` が `is_trivia` で探す） | 保つ（差は作れなかったと RF にある。`compare.py diags` で確かめる） | なし | `parser/file.rs`（`end_with`） | — | 2 |
| A9 RF-6 (C) E0003 の候補を作る `move_up` が `foreign/edits.rs` にある | ある（`foreign/edits.rs:20`、`foreign.rs:921` で再輸出し、`parser/statements.rs:32` が呼ぶ） | 保つ | なし | 新しい `edits.rs`（crate 直下）、`foreign/edits.rs`、`foreign.rs`、`parser/statements.rs`、`foreign/*.rs` の `use` | — | 20（移す約 240） |
| A10 RF-6 (D) `token_kinds!` の本体を rustfmt が整形しない | ある（`token.rs:10〜24`） | 保つ（直さない案） | なし | なし | `token.rs` | 0 |
| A11 RF-6 R2 `operand()` が字句から頂点を読み直す | ある（`foreign/assign.rs:20`。呼ぶ所は `guard.rs:290,790`、`assign.rs:65`、`flow.rs:271`） | 保つ（条件付き。読めない入力で差が出れば変える へ） | なし | `parser/expressions.rs`（`reads_as_expr` を頂点も返す形に）、`foreign/assign.rs`（`operand`） | `ast.rs`（`Operand`、`BinOp::bare`） | 80 |
| A12 RF-6 R3 検出の入口が一つの行だけ | 済み。`Matcher::many`（`foreign.rs:345`）で一つの検出が複数の行を名乗る形が型になった（`rows.rs:1064` の `guard_pattern` は 7 行） | 済み | — | — | — | 0 |
| A13 RF-6 R4 `interpolated` が `foreign/guard.rs` にある | 済み。`literal.rs:170` の `Literals::interpolated` になり、パーサは `parser/patterns.rs:85` でそれを呼ぶ | 済み | — | — | — | 0 |
| A14 RF-6 R6 `Why::Differ` | RF-7 の A23・A24 と同じ | — | — | — | — | 0 |
| A15 RF-6 S1 の 6 `parse_type` の三通り | ある。`parse_type`・`parse_bare_type`・`parse_type_ex`（`parser/types.rs:14,22,45`）と、`parser/items.rs:504` が `parse_type_ex` と `parse_clock_opt` を自分で並べる | 保つ | なし | `parser/types.rs`、`parser/items.rs`（`impl` の頭） | — | 20 |
| A16 RF-6 S1 の 8 `foreign/flow.rs` の `typeish` の閉包 | ある（`foreign/flow.rs:286`）。〔第 2 版〕位置の判断（束縛・型・入出力）は、今は `clocks` の親の種類の一つの `match`（`:146〜152`）にまとまり、済み。残りは `typeish` だけ | 保つ | なし | `cst.rs`（述語）、`foreign/flow.rs`（`in_type`） | `parser.rs`（`in_type`） | 10 |
| A17 RF-6 `PatReader` と `parse_pattern_alt` の重複 | ある（`foreign/guard.rs:104〜398` と `parser/patterns.rs:88`）。字句の集合（リテラルの葉、`Ident`・`KwSelfType` の後の `(`・`{`・`@`）が二か所 | 保つ | なし | `starts.rs`（葉の集合）、`foreign/guard.rs`（`one_at_depth`）、`parser/patterns.rs` | `scan.rs`（`pattern_alternative`） | 30 |
| A18 RF-6 W3-19/b の型引数の塊を `foreign/type_args.rs` へ | 済み。型引数の行は `foreign/paths.rs` にある（`foreign.rs` には 6 か所の参照だけ） | 済み | — | — | — | 0 |
| A19 RF-6 W3-19/b `body.rs` の E0200 の三か所、`children` の集約 | `onsa_sema` の側 | 他の領域（C1） | — | — | — | 0 |
| A20 RF-6 W3-20/b 呼び先の判定が 5 か所 | ほぼ済み。`callee.rs` の `Callee`（`by_name`・`names_a_path`）が一つの読みになった。二つの問いを一つにするかは `callee.rs:12` が W4-12・W4-13（どちらも PLAN）に残している。〔第 2 版〕W3-19/b の 2（名前の経路かの判断が 4 か所）も `Link::names_a_path` の一つになり済み | 済み（残りは W4-12・W4-13） | — | — | — | 0 |
| A21 RF-6 W3-20/b リテラルの後の判定が 3 か所 | ある。「`.` の次が成員か」が `literal.rs:313`（バイト）、`foreign/lines.rs:27`、`foreign/spaces.rs:122`（キーワードも数える）にある | 保つ | なし | `starts.rs`（述語）、`foreign/lines.rs`、`foreign/spaces.rs` | `literal.rs` | 15 |
| A22 RF-6 W3-20/b `MoveExpr` の節を作る場所が 4 つ | ある（`parser/statements.rs:136,229`、`parser/expressions.rs:349,455`） | 保つ | なし | `parser/statements.rs`、`parser/expressions.rs` | `parser.rs`（`without_node`） | 30 |
| A23 RF-6 W3-20/b `dump.rs` と `fmt.rs` の `parens` | 一部だけ残る。`fmt` は AST の `parens` を読まなくなった（`rg '\.parens\b'` で `dump.rs:410,807` と `lower.rs` だけ）。`dump.rs` の中の型とパターンの二つが同じ書き方 | 保つ | なし | `dump.rs`（`ty`、`pat`） | — | 8 |
| A24 RF-6 W3-20/b `parser.rs` の `in_type()` が `lower::class` に依存 | 済み。`Class` は `cst.rs:308` に移り、`in_type`（`parser.rs:454`）は `k.class()` を読む | 済み | — | — | — | 0 |
| A25 RF-7 (a-1) `Why::Differ` を理由の列挙型に | ある（`foreign/guard.rs:497`）。`Differ` は、骨格が違う（`:574`）、消す所にコメント（`:523,539,580`）、形が無い（`:743`）、腕の guard の最後が無い（`:789`）、来ない枝（`:583`）の 5 つの理由を一つにまとめる | 保つ | なし | `foreign/guard.rs`（`Why`、`shape`、`Arm::candidates`、`guard_pattern`） | `foreign/rows.rs` | 30 |
| A26 RF-7 (a-2) 行ごとの note を分ける（E0002 の文面が理由を言わない、W3-21/b の指摘 12） | ある（下の 2 章の例） | 変える | なし | `foreign/guard.rs`（`guard_pattern`）、`foreign/rows.rs`（行を足すか文面）、`spec/foreign-forms.toml` | — | 35（と golden）〔第 2 版〕 |
| A27 RF-7 (b) `list_fixes` の三つの分岐を表に | ある（`foreign/lists.rs:53`） | 保つ | なし | `foreign/lists.rs`（`list_fixes`） | `starts.rs`、`scan.rs` | 50 |
| A28 RF-7 (c) `Parser::ends` を閉じた節から導く | ある。`end_with` は 8 か所（`parser/statements.rs` の 5、`end_no_operand` の 3）で、どれも `complete(m, kind)` の直前 | 保つ（〔第 2 版〕前提の論点は X-3 で済み） | なし | `parser.rs`（`complete`）、`parser/file.rs`（`end_with`、`end_no_operand`）、`parser/statements.rs`、`parser/items.rs`、`foreign.rs`（`End`） | `foreign.rs`（`Cursor::end_at`） | 40 |
| A29 RF-7 (d) `many` の検出に行を足すと三か所 | ある。`Matcher::many` は 17 個（`rows.rs`） | 保つ | なし | `foreign/rows.rs`（`MATCHERS`）、`many` の検出を持つ `foreign/*.rs` | `foreign.rs`（`Matcher`） | 60 |
| A30 RF-10 P-1 `CARET_RULE`・`IF_TILDE_ELSE_RULE`・`PathInfo`・`binop` | ある（`parser.rs:224,230,239,1105`）。使うのは `parser/expressions.rs:403,688`、`parser/signatures.rs:28,50`、`binop` は `parser/statements.rs:243`・`parser/expressions.rs:56`・`parser/types.rs:232` | 保つ | なし | `parser.rs`、`parser/expressions.rs`、`parser/signatures.rs`、`parser/statements.rs`、`parser/types.rs` | — | 25 |
| A31 RF-10 P-1 `foreign.rs` の rustdoc の未解決のリンク | ある（今は 179 行目）。`pub enum Want` の `Separator` の文書の ``[`super::lists::list_fixes`]`` は、`foreign.rs` から見て `crate::lists` を指し、無い | 保つ | なし | `foreign.rs`（179 行目） | — | 2 |
| A32 RF-15 括弧を外す走査を `Ast::without_parens` に | ある。`onsa_sema/src/modes.rs:195` の `strip`（呼ぶ所は 1 つ）、`groups.rs:718`（`evaluated_once` の負のリテラル）。表に無い 3 つ目が `onsa_sema/src/flow_map.rs:145` | 保つ | modes に触れる（あり） | `onsa_sema/src/modes.rs`（`strip`、`place_of`）、`groups.rs`（`evaluated_once`） | `ast.rs`（`without_parens`、`negated_literal`） | 15 |
| A33 持ち越し: 「`&` の次が `mut`」の判定が `lines::leading` と `modes::reference` | 済み。どちらも `Cursor::ref_mut`（`foreign.rs:639`）を呼ぶ（`foreign/lines.rs:189`、`foreign/modes.rs:21`）。826fc8a で入った | 済み | — | — | — | 0 |
| A34 持ち越し: `comma_list` と `layout::starts_element` の集合の重なり | 済み。どちらも `starts.rs` の `element_starts` の表から出る（`starts.rs:77,111,119`） | 済み | — | — | — | 0 |
| A35 持ち越し: `layout.rs` と `parser.rs` の循環 | 済み。`layout.rs` は `crate::starts` と `crate::token` だけを使う（`layout.rs:10,11`）。`starts.rs` は `cst`・`token` だけ。7fd6b15（RF-3） | 済み | — | — | — | 0 |
| A36 〔第 2 版〕W3-20/b の 3: `modes.rs` の「消費する位置」の一覧が 2 か所 | ある（`onsa_sema/src/modes.rs:462` は `PlanarElem` を含み、`:632` は含まない。注釈を読むと違いは意図したもの） | 保つ | modes に触れる（あり） | `onsa_sema/src/modes.rs`（`Pos` に名前の付いた述語を二つ） | — | 10 |
| A37 〔第 2 版〕W3-19/b の 4: 型引数の AST の二重の表現（式の `TypeArgs` と struct リテラルの `type_args: Vec<(usize, TypeArgList)>`） | ある（`lower.rs:1187` の `struct_lit_path`） | 範囲の外（W4-13、PLAN が両方を扱う） | — | — | — | 0 |
| A38 〔第 2 版〕W3-09/b の S-1 の 5: 連鎖の頭の `if` の判定が 4 通り | 表の側は済み（`foreign/flow.rs:78,104` はどちらも `Cursor::branch`）。パーサ（`parse_if` の `chain`）と `lower.rs` の `Tilde` の読みが同じ事実かは確かめていない | 済み（一部は未確認） | — | — | — | 0 |
| B1 `parser.rs` を分ける | 4 章 | 保つ | なし | `parser.rs`、新しい `parser/nodes.rs`・`parser/cursor.rs`・`parser/failure.rs`・`parser/declarations.rs`、`lib.rs` | — | 40（移す約 900） |
| B2 `lower.rs` を分ける | 4 章 | 保つ | なし | `lower.rs`、新しい `lower/failed.rs`・`lower/items.rs`・`lower/exprs.rs` | — | 30（移す約 1000） |
| B3 `ast.rs` を分ける | 4 章 | 保つ | なし | `ast.rs`、新しい `ast/ops.rs` | — | 15（移す約 240） |

数（38 の項目と 3 つの大きいファイル。〔第 2 版〕）:
- 保つ: 27（A1〜A3、A5〜A11、A15〜A17、A21〜A23、A25、A27〜A32、A36、B1〜B3）
- 変える: 1（A26）
- 決定: 0
- 済み: 9（A12、A13、A18、A20、A24、A33〜A35、A38）
- 他の領域・範囲の外: 3（A4・A19 は C1、A37 は W4-13）
- A14 は A25・A26 と同じなので数えない。

見積もりの合計（〔第 2 版〕）: 変える行が約 720（A の項目が約 635、大きいファイルを分けるのが約 85）、移す行が約 2,600、テストが約 40。

## 2. 項目ごとの修正方針

**A1（保つ）.** `parser/chain.rs` の `fn tighter` を消し、`Chain::operator` に `OpGroup::stronger` をそのまま渡す。
強弱の判断は `OpGroup::stronger` の一か所になる（`lower.rs:1155` の閉包も型を合わせるだけの包み）。
`groups.rs` の `Order::tighter` は §18.1 の仮の強弱を足す読みで、役が違うので残す。
〔第 2 版〕W3-07/b は `parser::Chain` が `ast::Chain` の薄い包みで名が重なると言う。役（鎖の高さ）を表す名（例 `ChainHeight`）に改める。

**A2（保つ）.** E0010 の判定（「どの演算子の対に強弱が無いか」）を、AST の `Binary` の辺で直接行う。
`check` の中で、鎖の根ごとに `Binary` の子が `Binary` である辺を見て `op.takes(side, child)` を調べ、`parts` を作る。
`parts` の順は、今の `actual.0`（`Chain` の join の順）と同じにする必要がある。
`lower.rs` の `chain` も同じ `Chain` の join の順で `add_expr` するので、鎖の中の `Binary` を `ExprId` の昇順で回せば同じ順になる。
「`co < o`」（子の演算子が左か）は `op_span.start` の比べに置き換える。
判定で `parts` が空でない鎖だけ `Flat::new` を作り、読みの列挙（`readings`）と候補（`render`）に使う。
`Flat::check` は、判定（AST の辺）と、文面と候補を作る部分（`Flat`）に分かれる。

**A3（保つ）.** 鍵を表から出す。
`const GROUPS: [OpGroup; 6]` と `const BITWISE: [BinOp; 5]`（`BitAnd`・`BitOr`・`BitXor`・`Shl`・`Shr`）を置き、`KEYS = GROUPS.len() + BITWISE.len()`。
`key(op)` は `GROUPS` の中の位置か、`GROUPS.len()` に `BITWISE` の中の位置を足したものにする。
今の `_ => 10` は `Shr` を暗に指すので、表にすると `Shr` の名が出る。`Order::of_the_spec` は今のまま `GROUPS` を回す。

**A4（他の領域）.** 3 つの `children` は C1 の RF-8 と同じもの。読んだ範囲で分かったことだけ書く。
sema と core の二つは中身が同じ（`Error` の扱いと注釈だけ違う）で、レートの印の走査の子（`Field` の基・呼び先・`Closure` の本体・`Repeat` の長さ・`Par` の範囲・ブロックの文を含まない）。
`graph.rs` は全ての部分式（文も）で、別の判断。一つにするなら sema の側に置いて core が呼ぶ形（`onsa_core` は `onsa_sema` に依存する）。

**A5（保つ、テストだけ）.** `cst_tests.rs` に、ファイルの AST の各 `Binary` の鎖について、AST の木の高さ（`Binary` の段の数）が、`parser::Chain` で数えた鎖の高さと等しいことを確かめるテストを足す。
入力は `chain_heights_follow_the_strengths` の形と、`tests/` の全てのファイル（`cst_tests` の流儀、深い入力は `onsa_diag::stack`）。

**A6（保つ）.** `groups.rs` から入れ子の上限の確かめを `crate::nesting`（新しいモジュール）へ移す。
移すものは `Limit`、`Limit::exceeded`、`nests_too_deep`、`COUNTING`・`PARSES`・`READ`、`Counting`、`TOO_DEEP_RULE`、`parenthesized`（E0011・E0012・E0013 の候補に上限を当てる関数）。
`groups.rs` に残るのは、E0010〜E0013 の判定（`check`、`operands`、`block_like_operands`、`block_like_errors`）と E0010 の読み（`Order`・`Flat`・`Reading`・`render`）。
E0010 の読みは約 300 行あり、`groups/readings.rs` に分けてもよい（A2 の後なら判定と読みの境がはっきりする）。
〔第 2 版〕`foreign/flow.rs` の `clocks`（`:155〜163`）は、`(` の数に 1 を足して `limit.exceeded` を見て、超えれば候補を捨てて `TOO_DEEP_RULE` を付ける。`groups.rs` の `parenthesized` と同じ判断なので、`nesting.rs` に「候補に上限を当てる」関数を一つ置き、両方が呼ぶ。

**A7（保つ）.** `is_trivia` に「パーサが読み飛ばすもの: 空白・改行・行のコメント。ブロックコメントは読み飛ばさず、パーサがそこで失敗して行（E0020）が報告する」という文書を付ける。
局所の `matches!` は、集合が違うことに意味がある（`docs.rs:74` と `parser/items.rs:21,75` は文書のコメントを数えない、`foreign/flow.rs:245` は改行で止まる）。
それぞれを `TokenKind` の名前の付いた述語にするか、その場で理由を一行書く。読む所を `is_comment` に替える案は、ブロックコメントの近くの回復が変わりうるので採らない（RF/b の単位 1 の案 A で、行の継続の判定だけを替えた）。

**A8（保つ）.** `end_with` の探しを `is_trivia` から `is_code`（`token.rs:258`）の否定に替え、ブロックコメントを最後のトークンにしない。
RF の本文では出力の差を作れなかった。`compare.py diags` で 0 件でなければ、変える に移して例を出す。

**A9（保つ）.** `foreign/edits.rs` のうち、`Cursor` を使わない編集の組み立て（`move_up`、`take_out_blanks`、`Insertions`、`insert_apart`、`apart`、`Joins`、`around`、`joining`、`lexed`）を crate 直下の `edits.rs` へ移す。
`Cursor` を使うもの（`alone_on_its_line`、`move_token_up`、`move_token_up_as`、`move_token_down`）は `foreign/edits.rs` に残す。
パーサは `crate::edits::move_up` を呼び、`foreign.rs:921` の再輸出を消す。

**A10（保つ、直さない案）.** `token_kinds!` は、`TokenKind` と `TokenKind::ALL` を一つの並びから出すため（列挙の漏れを防ぐ、D-15）にある。
外部の crate を足さずに同じ保証を保つ書き方は無いので、rustfmt が本体を整形しないことは受け入れる。
親が RF-6 の (D) を「直さない」と記録する案。

**A11（保つ、条件付き）.** `reads_as_expr`（`parser/expressions.rs:715`）を、読めたかに加えて頂点（`Operand`）も返す形にする。
読めたときは、パーサの CST の頂点の節（`BinaryExpr` なら強弱の最も弱い演算子、`CastExpr`・`AtExpr` なら `Operand::AsAt`、他は `Plain`）から `Operand` を作る。
読めないとき（誤りを含む式、guard の途中）は今の `operand()` に戻すしかないので、`operand()` は「読めないときの読み」として残る。
効果は、読める式で強弱の読みがパーサと一つになること。読める式で頂点が違う入力（強弱の無い組の鎖など）があれば出力が変わるので、`compare.py diags` で差を確かめ、差があれば変える に移す。
管理の得が小さい割に手間が大きいので、優先は低い。
〔第 2 版〕W3-09/b の S-1 の 4（「`as`・`at` の式に括弧が要るか」が AST の `as_or_at_operand`・トークンの `needs_parens`・CST の種類の表の三つ）は、今は `to_value` が `operand()` を呼ぶ（`foreign/flow.rs:271`）ので CST の表は消え、残りは AST とトークンの二つで、この項目と同じもの。
W3-21/b の R-2 が挙げた「`^name` を二項の `^` と読んで括弧を足す」は、今の `operand()` が被演算子の始まりの `^` を前置として飛ばす（`foreign/assign.rs:35`）ので直っている。

**A15（保つ）.** `parse_type_ex` を `parse_type_with(clock: Clock) -> PResult<(Completed, usize)>` にし、`enum Clock { Read, None }` で時計を読むかを渡す。
`parse_type` と `parse_bare_type` はその包みとして残す（呼ぶ所が 19 と 1）。`parser/items.rs:504` は `parse_type_with(Clock::Read)` を呼ぶ。

**A16（保つ）.** `typeish`（型の類の節、`TypeArgs`、`FnTypeParams`）を `NodeKind` の述語（`cst.rs`、例 `in_type_position`）にする。
`parser.rs:454` の `in_type` は `Class::Type` だけを見るので、同じ判断かを確かめる（パーサが式を読むのは型の中の const 引数か配列の長さで、祖先に `Class::Type` の節があるので同じ結果の見込み）。
同じなら両方がその述語を呼ぶ。材料（`w309b/report.md`）が無いので、「位置の判断」の他の部分は確かめられなかった。

**A17（保つ）.** 二つの読み手は役が違う（パーサは他言語の形で失敗し、`PatReader` は失敗の後にその形を読む）ので、一つにはしない。
重なる字句の集合を `starts.rs` に置いて両方が読む: パターンの葉になるリテラル（`Int`・`Float`・`Char`・`Str`・`KwTrue`・`KwFalse`）と、名前の後の `(`・`{`・`@` の判断の条件。
`PatReader` の文書の「`Parser::parse_pattern` が読むものを読む」を、述語を指す形に改める。
〔第 2 版〕W3-21/b の R-1（`form_at` と `PatReader` が別々に判定）は、今は `form_at` が `PatReader::one` を使う（`guard.rs:628`）ので済み。R-7（束縛の名前か型の名前かの判定が 3 か所）も `naming.rs` の `is_binding_name`・`is_type_name` に寄って済み。
W3-15/b は、パーサが浮動小数のパターンを致命でなく受け、腕を閉じたときに表が CST から読む形にすれば `PatReader` と `Pat`（約 150 行）を消せる、と言う。パーサの失敗の位置と回復が変わり、E0020 の候補の作り方が CST に移る大きな直しで、出力が変わりうる。X-6 の範囲（出力を変えない）には入れず、別の項目の候補として記録する案。

**A21（保つ）.** 「`.` の次が成員」を `starts.rs` の述語 `starts_member(kind)`（`Ident`・`Int`・`LParen`）にして、`foreign/lines.rs:27` と `foreign/spaces.rs:122` が呼ぶ。
`spaces.rs` はキーワードも数えるので、`starts_member(next) || next.is_keyword()` と、違いを呼ぶ所に残す。
`literal.rs:313` はバイトの段の判断なので述語を共有できない。述語の文書から指す。

**A22（保つ）.** `move` の形を読む関数を一つにする: `fn parse_move(&mut self, node: MoveNode, rest: impl FnOnce(&mut Self, Token) -> PResult<Completed>)`。
`MoveNode::Node` は `start`/`complete` で `MoveExpr` を作り（`parse_consumed`、`match move x`）、`MoveNode::Level` は `without_node` で段だけ数える（引数、`for` の範囲）。
`no_struct_lit` の保存と戻しは呼ぶ側の `rest` の中に残す（`match` と `for` が `true`、引数が `false`）。4 か所はこの関数を呼ぶだけになる。

**A23（保つ）.** `dump.rs` の `ty` と `pat` の括弧の書き方を、`fn wrapped(&mut self, parens: u32, f: impl FnOnce(&mut Self))` の一つにする。
小さいので、B2 か他の `dump.rs` の直しと同じ回に入れる。

**A25（保つ）.** `Why` を理由ごとの列挙にする: `Skeletons`（骨格が違う）、`Comment`（消す所か穴にコメント）、`NoForm`（形が無い）、`GuardEnd`（腕の guard の最後の字句が無い）、`Bad(Form)`。
`shapes.next()` が `None` の枝（`:583`）は来ないので `internal::bug` にする。
`guard_pattern` の `match` は、`Bad` 以外の全てを今の `head.choice_row()` に写し、出力を変えない。

**A26（変える）.** A25 の理由を、診断の note で言い分ける（W3-21/b の指摘 12）。
〔第 2 版〕W3-21/b の指摘 12 は、ほかに次の形を挙げる。範囲を広げたので見積もりを 20 から 35 にした。
- 範囲の端が式として読めない・端の中にコメントがある・`{ 8 }` の端: E0020 の行と同じ文面と note のまま、候補が出ない理由を言わない。
- `@` の `Differ`（コメント）でも「no comparison a guard can write」と出る（`AtBindingComplex` の行）。
- 補間を含む文字列と `-` を付けた定数（`Form::Str | Negated`）は選択の行を持たず、枝の形が違っても E0020 の行の文面で E0002 になる（`guard.rs:46`）。
例（今の `target/debug/onsa`）:

```
fn f(x: F32) -> I32 {
    match x {
        1.0 // c
        | 2.0 => 1,
        _ => 0,
    }
}
```

今: `E0002 float literals cannot be patterns, and these alternatives do not merge into one guard`、note は `a pattern holds no float literal; alternatives of other shapes are split into arms, or written in a guard (§7)`、候補 0。
二つの選択肢は同じ骨格で、候補を作らない理由は消す所のコメント（S-251）なのに、文面は「合わない」と言う。
後（案）: 文面は同じで、note に「the comment between the alternatives would be removed: move it out, and the guard can be written」の類を足す（文面は利用者の了承を取る）。
直す所は `guard_pattern` と行の表（`foreign/rows.rs` は領域 B の大きいファイル）で、`spec/foreign-forms.toml` の例と golden が変わる。待つ S は無い（文面は実装が決める）。

**A27（保つ）.** `list_fixes` を、決定の順に並べた候補の表にする: `[(条件, 作る関数)]` を順に当て、「`=>` が続く腕の記号」は先に当たれば他を見ない、の形。
今の三つの分岐（腕の記号、`,`、二つの文字列か間隙の除去）は、文書の箇条（`foreign/lists.rs:34〜49`）と一対一になる。
`,` の条件（`declaration`・`array`・`comma`）は一つの関数 `comma_goes(c, list)` に出す。

**A28（保つ）.** 「何で終わる文か」を `NodeKind` の表にする: `End::of(kind, keyword) -> Option<End>`（`foreign.rs` の `End` の隣）。
`LetStmt`・`VarStmt`・`AssignStmt`・`ReturnStmt`・`AssertStmt` は `Bound`、`ForStmt`・`WhileStmt` と `const`・`type` でない `Item` は `NoOperand`。
`Parser::complete` が、その表に当たる節を閉じたときに `end_with` を呼ぶ。8 か所の呼び出しは消える。
`complete` は回復の道でも呼ばれうるので、今 `end_with` を呼ばない道で `complete` される `LetStmt` などが無いかを、実装の前に `rg 'complete\(.*NodeKind::(LetStmt|VarStmt|AssignStmt|ReturnStmt|AssertStmt|ForStmt|WhileStmt|Item)'` で確かめる。
〔第 2 版〕RF-7 の「(1) の候補の約束の論点の後」の (1) は、4be65d0 の `docs/carryovers.md` の 256 行目「(1) 修正候補の約束を一段弱める案」（今の `issues/X/X-3.md:25`）を指す。X-3 は DONE（2026-10-18）なので前提は満たされ、A28 を待たせるものは無い。
W3-06/b の単位 2 の再確認（`w306b2/handback.md` の「14. 整理」）は、`ends` が `Snapshot` に入り（`parser.rs:326`）、昇順の `debug_assert` が 2 万件の変異で発火しなかったと言う。`complete` で記録する形にしても、`Snapshot` の `ends: usize` と試し読みでの巻き戻しはそのまま残す。

**A29（保つ）.** `many` の検出の行の並びを、検出の隣に置く: 各検出のモジュールに `pub(super) const ROWS: &[RowId]` を置き、`MATCHERS` は `Matcher::many(guard::ROWS, guard_pattern)` と書く。
行を足すときは、行の定義（`ROWS` の表）と検出のモジュール（関数と並び）の二か所になる。
加えて、`spec/foreign-forms.toml` の例を回して、`many` の各行が実際に作られることを確かめる自己テストを `foreign_tests.rs` に足す（今の自己テストが捕まえない二つ目、RF の本文の持ち越し）。
`MATCHERS` は領域 B の `foreign/rows.rs` にあるので、B の作業と順を決める（4 章）。

**A36（保つ、〔危険〕あり、〔第 2 版〕）.** `onsa_sema/src/modes.rs` の `Pos` に、名前の付いた述語を二つ置く: `takes_a_written_move()`（`:462`、`PlanarElem` を含む）と `consumes()`（`:632`、含まない）。
違いは注釈（`:458`、`:630`）のとおり意図したもの（`PlanarElem` は書いた `move` を受けるが、裸の場所は消費しない）なので、一つにはしない。`matches!` の二つを述語の呼び出しに替えるだけで、出力は変わらない。

**A30（保つ）.** `CARET_RULE`・`IF_TILDE_ELSE_RULE` を `parser/expressions.rs` へ、`PathInfo` を `parser/signatures.rs` へ移す（どちらも `pub(super)` が要らなくなる）。
`binop` は消し、3 か所は `kind.binop().is_some()` と書く。B1 と同じ回にする。

**A31（保つ）.** `foreign.rs:179` のリンクを、リンクにしない字（`` `lists::list_fixes` ``）にする。
`Want` は `pub` で、子の非公開の項目へのリンクは公開の文書から解決しない（RF-10 の本文）。`pub(crate)` の項目の中のリンク（`:528,534,595`）は `--document-private-items` で解決するので、そのまま。

**A32（保つ、〔危険〕あり）.** `onsa_sema/src/modes.rs` の `strip` を消し、`place_of` は `self.ast.without_parens(e)` を呼ぶ。
`groups.rs:714〜720` の負のリテラルの判定は `self.ast.negated_literal(e).is_some()` と同じ（`-` の後の括弧を外してから整数か浮動小数のリテラル）なので、それに置き換える。
`onsa_sema/src/flow_map.rs:145` の `promotes_as_written` の同じ走査も `without_parens` にできる（RF-15 の表に無い 3 つ目。C1 の範囲の sema のファイル）。
modes に触れるので〔危険〕。ただし同じ値を返す関数の置き換えだけ。

## 3. 大きいファイル

**`crates/onsa_syntax/src/parser.rs`（1241 行）: 分ける。**
役が四つ混ざっている（8.1 の「名前が役割を表す」）: 節と段（入れ子の上限）の組み立て、字句の読み手、失敗の報告と表への問い、宣言の表。
- `parser/nodes.rs`: `snapshot`・`restore`・`end_trial`、`enter`・`enter_unit`・`start`・`in_type`・`level`・`height`・`limit`・`too_deep`・`reshape`・`without_node`・`finish`・`complete`・`precede`・`close_open`（421〜626 行と 381〜420 行、約 250 行）。
- `parser/cursor.rs`: `significant`〜`src`（627〜870 行、約 245 行）、`EMPTY_BRACKETS_RULE`。
- `parser/failure.rs`: `report`〜`release_held`（871〜1104 行、約 235 行）と `Own`。
- `parser/declarations.rs`: `starts_heading`、`TOP` などの場所、`Declaration`・`DECLARATIONS`・`declaration`・`declaration_node`・`is_declaration_keyword`（1124〜1212 行、約 90 行）。
- `is_opening`・`is_closing`・`close_bracket` は `parser/file.rs` だけが使うので、そこへ移す（6 章の括弧の対も参照）。
- `Parsed`（`crate::parse` の結果、`AstMap` を持つ）は `lib.rs` へ移す。パーサが `crate::lower` に依存する唯一の理由（`parser.rs:52`）が消え、依存の向きが「parser → lower」でなくなる。
- 残る `parser.rs`: 文書、`ParseOutput`、`ParseError`、`ItemCtx`、`Marker`・`Completed`・`Open`、`NESTING_LIMIT`、`Parser`・`Snapshot`、`new`（約 330 行）。
- 上の項目と同じ所: A30（定数と `PathInfo`、`binop`）、A28（`complete`）、A22（`without_node`）、A16（`in_type`）。

**`crates/onsa_syntax/src/lower.rs`（1324 行）: 分ける。**
`parser/` と同じ単位で分け、名前で役を示す。
- `lower/failed.rs`: 構文の誤りで止まった項目の読み（`failed_item`、`head`、`add_head_item`、`read_name`、`failed_generics`・`failed_type`・`failed_expr`・`failed_members`・`failed_params`・`failed_kind`・`failed_derives`、`Head`。約 370 行）。
- `lower/items.rs`: `vis`・`derives`・`attr`・`item_kind`・`field`・`variant`・`fn_decl`・`item_list`・`generics`・`mode`・`params`・`struct_rest`・`effect_row`・`path`（約 300 行）。
- `lower/exprs.rs`: ブロックと文と式（`block`〜`args`、918〜1231 行、約 315 行）。
- 残る `lower.rs`: 文書、`AstMap`、`lower`、`Lower`、木の読みの補助、`add_*`、型、パターン、リテラル（約 340 行）。
- 上の項目と同じ所: A1（`chain` の閉包）、A5 のテストが読む `chain`。
- 分けた後も `failed_kind`（193 行）と `item_kind`（115 行）は項目の種類ごとに並行する（6 章）。

**`crates/onsa_syntax/src/ast.rs`（1095 行）: 分けてよいが、優先は低い。**
大半は節の型の定義で、一つの役（AST の形）なので、行数だけでは分けない。
ただし演算子と強弱（§3.1）の部分は判断を持ち、`parser/chain.rs`・`lower.rs`・`groups.rs`・`foreign/assign.rs`・`foreign/guard.rs` が読む。
- 分けるなら `ast/ops.rs`: `BinOp`・`OpGroup`（`stronger`）・`Side`・`Operand`・`BinOp::bare`・`group`・`takes`・`symbol`・`Chain`・`UnOp`（629〜871 行、約 240 行）。`ast.rs` で `pub use` し、使う側の経路は変えない。
- 上の項目と同じ所: A1〜A3（強弱と鍵）、A11（`Operand`）。

## 4. 項目どうしの依存

同じファイル・関数を触る組:
- `groups.rs`: A2、A3、A6、A32（`evaluated_once`）。一人の担当にまとめる。A6（移すだけ）を先に、次に A3、A2、A32。
- `parser.rs` と `parser/`: B1、A30、A28、A22、A15、A8、A11（`reads_as_expr`）、A16（`in_type`）。B1 と A30 を先に（移すだけ）、その後に中身の直し。
- `lower.rs`: B2、A1、A5（テストが読む）。B2 を先に。
- `ast.rs`: B3、A3、A11。B3 を先に（`pub use` で経路が変わらないので、A2・A3 と並べても衝突は小さい）。
- `foreign/edits.rs` と `foreign/*.rs` の `use`: A9。`foreign/` の多くのファイルの `use` を触るので、領域 B の作業（`foreign/` の検出、`rows.rs`）より先に入れるか、B と同じ担当にする。
- `foreign/guard.rs`: A11（`operand` の呼び出し）、A17、A25、A26。A25 を先に、A26 は変える の流れ（テストの票と了承）なので後。
- `foreign/rows.rs`（領域 B の大きいファイル）: A26、A29。B が `rows.rs` を分けるなら、その後に A29。
- `foreign/lists.rs`: A27 のみ。`foreign/lines.rs`・`foreign/spaces.rs`: A21 のみ（B の R-210 が `foreign/assign.rs` に触るなら、A11 の `operand` と同じファイル）。
- `onsa_sema/src/modes.rs`: A32 と A36（C1 が `modes.rs` を触るなら順を合わせる。どちらも数行）。
- `token.rs`・`starts.rs`: A7、A17、A21（どれも述語を足すだけで、衝突は小さい）。

先に済ませたほうがよい順:
1. 移すだけ: A6（`nesting.rs`）、A9（crate 直下の `edits.rs`）、B1（と A30・A31）、B2、B3。
2. 判断を一か所にする小さい直し: A1、A3、A15、A16、A21、A22、A23、A32、A36、A7、A8。
3. 構造の直し: A2（と A5 のテスト）、A25、A27、A28、A29、A17。
4. 条件付き: A11（差を見てから）。
5. 変える の流れ: A26（テストの票を先に出し、文面の了承）。

## 5. 材料の要点

第 1 版のときは、材料の scratchpad は全て空だった（ディレクトリだけ残る）。〔第 2 版〕親が `scratchpad/x6/materials/` に取り戻したものの要点を、この節の最後に足した。
- `前の回の scratchpad の w307b/`: 空。
- `前の回の scratchpad の w309b/`: 空。
- `前の回の scratchpad の w319b/`: 空。
- `前の回の scratchpad の w306b2/`: 空（`handback_b.md`・`handback_b2.md` は無い。同じ親のディレクトリに `rf`・`rfb1`・`rfb2`・`rfi` などは残る）。
- `前の回の scratchpad の w306b1a/`: 空。

`issues/X/X-6/` に移す要点は、材料からは無い。RF の本文と `issues/X/X-6.md` の持ち越しの記述から、修正方針に効いた点だけ:
- 持ち越しの「`&` の次が `mut`」、`comma_list` の重なり、`layout.rs` と `parser.rs` の循環は、どれも RF-1〜RF-4 の単位 1・2（7fd6b15、826fc8a）で済んでいる（A33〜A35）。持ち越しから外してよい。
- RF-6 の R3（登録簿の型）と R4（`interpolated`）、W3-19/b の型引数の塊、W3-20/b の `in_type` の層の向きも済んでいる（A12、A13、A18、A24）。
- 「出力を変えない条件の例外」（ブロックコメントを行の継続でコメントとして数えた案 A）があるので、A7 では読む所を `is_comment` に替えない。

### 〔第 2 版〕取り戻した材料の要点

出所は `44 回目の scratchpad の x6/materials/` の下。読んだのはリファクタリングの候補の節と、指摘の該当の番号だけ。
- `w307b/handback.md`「リファクタリングの候補」: A1〜A6 の元。今も効くのは、`Flat::new` の読み直し（A2）、鍵の位置の対応（A3）、`parser::Chain` の名の重なり（A1）、AST の高さのテスト（A5）、`groups.rs` の分け方（A6）。閾値のリテラル（80・48・60−13）は `READINGS_MAX`（`groups.rs:442`）になり済み。`children` は C1。
- `w309b/report.md`「S-1」の 6・8 と「リファクタリングの候補」: 6 は A15 のまま。8 の「位置の判断」は今は `clocks` の一つの `match` で済み（A16）。S-1 の 4 は A11 に含めた。S-1 の 5 は A38。S-1 の 7（`fail_with` の `pop`）は今の `fail_with` に無く済み。S-1 の 1〜3（遅延の名前の表、形の表示名、関門と到達しない腕の置き場所）は sema と core の側で、C1・C2 が見る材料（確かめていない）。
- `w321b/report.md`「12」と「リファクタリングの候補」R-1〜R-8: R-2 は A11、R-3 は A12、R-4 は A13、R-6 と指摘 12 は A25・A26。R-1 と R-7 は済み（A17）。R-5・R-8（`structpat.rs`、sema）は領域 A の外で、確かめていない。
- `w319b/handback.md`「リファクタリングの候補」1〜10: 2・6・8・9 は済み（A20、`const_arg_ahead` は無く、型引数の塊は `foreign/paths.rs`、`is_type_args_mark` は `Cursor` を取る）。4 は A37（W4-13）。5・7 は C1。1・3（`angle_chain` と `turbofish`、`square_comma`）は `foreign/` の検出で領域 B。
- `w315b/handback.md`「リファクタリングの候補」1〜5: 1（`foreign.rs` を分ける）は RF-1〜RF-4 で済み。3 の `PatReader` を消す案は A17 に記録した（範囲に入れない）。2・3 の残り（行の識別子の重複、`statement_end`（`foreign.rs:848`）、`block_shape`（`foreign/comments.rs:7`）、`holds_lines`（`foreign/semicolons.rs:6`）、`TYPE_NAMES`）は領域 B。5（`fix_contract.rs`）は領域 D。
- `w320b/handback.md`「リファクタリングの候補」1〜7: 1 は A20、2 は A21、5 は A22、6 は A23、7 は A24。3 は A36（新しく足した）。4（`.` の位置を AST が持たない）は `CallKind::Value { dot }`（`ast.rs:883`）で済み。
- `w306b2/handback.md`「14. 整理」と「新しい指摘」B: `Parser::ends` が `Snapshot` に入ったこと（A28）。B（「`&` の次が `mut`」の二か所）は A33 で済み。RF-7 の (1) の出所は `issues/X/X-3.md:25`（A28）。

## 6. 範囲の外で気付いたこと

- `lower.rs` の `failed_kind`（`:366`、193 行）と `item_kind`（`:607`、115 行）が、項目の種類ごとに二通りの読みを並べる（13 の腕）。「各項目が何から成るか」の判断が二か所にある。
  `failed_*` の補助が「節が完全なら普通に読む」形なので、項目の種類ごとに一つの読み手にし、足りない部分を `Error` にする形にできる見込み。AST の全体に効くので、B2 の後の別の項目にする案。
- 括弧の対（開き ↔ 閉じ）が `parser.rs` の `is_opening`・`is_closing`・`close_bracket`、`scan.rs:89` の `closer`、`foreign/guard.rs` の `Arm::read`・`foreign/assign.rs` の `operand` の深さの数えにある。`TokenKind::closer()`・`is_opening()` を `token.rs` に置くと一つになる。
- `Parsed` が `parser.rs` にあり、パーサが `crate::lower::AstMap` に依存する（B1 で `lib.rs` へ移す案に入れた）。
- RF-15 の表に無い 3 つ目の括弧を外す走査が `onsa_sema/src/flow_map.rs:145` にある（A32 に書いた）。
- 〔第 2 版〕RF-7 の「(1) の候補の約束の論点」は X-3 の (1) と分かり、済んでいる（A28）。
- 材料の scratchpad が空になっていた。X-6 の手順 1 の始め（親が材料の要点を `issues/X/X-6/` に移す）を、他の領域でも先に確かめる必要がありそう。

# X-6 手順 1 の調べ 領域 B（字句・他言語の形・行の配置・fmt）

確かめた版: dev `ee6a2bd`（コードは `1bb829a` 以後に変わっていない）。挙動は `target/debug/onsa`（10/19 13:08 のビルド。`onsa_syntax` は以後変わっていない）に小さな入力を渡して見た。
再現の入力と道具: `44 回目の scratchpad の x6/step1/B/probe/`（`q.py <onsa> <断片>` が `=== 名前` で区切った断片を `check --json` にかけ、`-e` で編集も出す。断片は `rf9.txt`・`r210.txt`・`w308.txt`、時間は `derive_scale.py`）。
経路は `crates/onsa_syntax/src/` から書く。

## 1. 項目の表

| 項目 | 今もあるか（確かめた所） | 分類 | 〔危険〕 | 触るファイル（関数） | 読むだけのファイル | 見積もり（変える行） |
|---|---|---|---|---|---|---|
| RF-9 (a1) `literal::Form` の二つの役割 | ある。`Form` が「Onsa の数の種類（`Int`・`Float`）」「他言語の形の行（`Suffix`〜`DotExponent`）」「誤り（`Invalid`）」を一つの列挙で持ち、`foreign/literals.rs:34` が `Int \| Float \| Invalid` の腕を `internal::bug` にしている | 保つ | なし | `literal.rs`（`Form`・`number`・`is_float`）、`lexer.rs`（`number` の 369 行の分け）、`foreign/literals.rs`（`foreign_literal`・`spellings`） | `foreign/guard.rs`（別の `Form`） | 40 |
| RF-9 (a2) `literal.rs` と `lexer.rs` の循環 | ある。`literal.rs:313・335・418・419・773` が `lexer::is_ident_start`・`is_ident_continue`・`line_break` を、`lexer.rs` が `literal::number` などを読む | 保つ | なし | 新しい `chars.rs`、`lexer.rs`（`is_ident_*`・`line_break`・`BLANKS`・`is_blank` を移し、`pub use` で残す）、`literal.rs` | `onsa_driver/src/lib.rs:575`（`lexer::is_blank`） | 30（主に移すだけ） |
| RF-9 (a3) `ConstValue::FloatText` を持つ理由の doc | 済んだ。`onsa_sema/src/consteval.rs:16-19` に理由（型が未定の浮動小数を降下で一度だけ丸める、R-20）がある（`4be65d0`） | 済み | — | — | — | 0 |
| RF-9 (b) `strings`・`numbers` の名前の無い組 | ある。`literal.rs:64-65・75-76` の `Vec<(Span, Number)>`・`Vec<(Span, Span)>`、`within` が同じ二分探索の切り出しを 4 回書く | 保つ | なし | `literal.rs`（`Literals`・`Found`・`within`・`foreign_string`・`number`）、`lexer.rs:383・478` | — | 40 |
| RF-9 (c) `at_failure` の `StringPrefix` だけの分かれ | ある。`foreign.rs:564-566` が `prefixed` と `faust::prime_note` の二つをこの行だけに書く | 保つ | なし | `foreign.rs`（`Hit`・`at_failure`・`hit`・`found`）、`foreign/spaces.rs`（`string_prefix`）、`Hit` を直に作る 6 か所（`decls.rs:73・238`、`paths.rs:40`、`literals.rs:58`、`flow.rs:163`、`foreign.rs:503`） | `foreign/faust.rs`（`prime_note`）、`parser.rs:940` | 25 |
| RF-9 (d1) `space_around_dot` の `joins` と `take(3)` | 済んだ。`spaces.rs:136` が `edits::joining`（字句解析器で読み直す一つの判定）を読み、`take(3)` は無い（`74941f1`、W3-13） | 済み | — | — | — | 0 |
| RF-9 (d2) `foreign_literal` の `joins` | ある。`foreign/literals.rs:43-47` の閉包が `point_after_int` で「`.` と合わさって別の数になるか」を自分で判定する（`edits::joining` の重複） | 保つ（差 0 の見込み。格子で確かめる） | なし | `foreign/literals.rs`（`foreign_literal`） | `foreign/edits.rs`（`joining`） | 15 |
| RF-9 (e1) 負のパターンの `-(017)`・`-(0o17)`・`-(1u8)` | ある。`rf9.txt` の `negpat_paren_*` が `E0002 1:33 expected a pattern, found '-'`（候補なし）。`-017`・`(017)`・式の `-(017)` は E0020 | 変える | なし | `parser/patterns.rs`（`foreign_integer`・`parenthesised_int_after_minus`・`parse_pattern_alt` の `Minus` の腕） | `foreign/literals.rs`、`foreign/guard.rs` | 20 |
| RF-9 (e2) 負のパターンの `-0b11f32` | ある（同じ E0002 を `-` に）。正の `0b11f32` は S-456 の仮の扱い | 決定（S-456、OPEN） | なし | `parser/patterns.rs`、`foreign/literals.rs` | — | — |
| RF-9 (f) 接する形を名前の側とリテラルの側の二つに | ある。`extern "C" lib"m"x { }` が `E0002 1:18 expected '{', found identifier` | 決定（S-473、OPEN。S-469、OPEN と一緒に） | なし | `lexer.rs`（`literal`・`name_after`）、`literal.rs`（`Touch`） | — | — |
| RF-12 (a) 行の頭の判定の三通り | ある。`layout.rs:105` `Lines::at_line_head`、`parser/items.rs:50` `Parser::starts_its_line`、`lexer.rs:72・79` `line_start`・`line_head` | 保つ | なし | `parser/items.rs`（`starts_its_line` を消す）、`layout.rs`（doc） | `lexer.rs` | 8 |
| RF-12 (b) `Cursor::indent` ほかの字下げの計算 | ある。`foreign.rs:758`（`&str`）、`parser/file.rs:235`（数）、`docs.rs:224`（`line_head` と切り出し）の三か所 | 保つ | なし | `chars.rs`（(a2) の新しいモジュール）か `lexer.rs` に `indent`、`foreign.rs`、`parser/file.rs`、`docs.rs` | — | 15 |
| RF-12 (c) タブで字下げした行の頭の `/** */` の事例 | ある（無い）。`tests` と `crates/onsa_syntax/src` にタブの後の `/**` の事例が無い | 保つ（テストを足すだけ） | なし | テストの票（`tests/spec` の事例か `foreign_tests.rs`） | `foreign/comments.rs:115` | 0（コード） |
| RF-13 継続の判定の引数を求める走査の二通り | ある。`layout.rs` の `Lines::of` と `fmt/plan.rs:240` `inside_elements` の `(before, last)` | 保つ（fmt の出力で確かめる） | なし | `cst.rs`（`Cst`・`build`・新しい `goes_on`）、`parser.rs`（`build` を呼ぶ所）、`fmt/plan.rs`（`inside_elements`） | `layout.rs` | 30 |
| RF-14 (a) 印字器の `space::space` | ある。`fmt/space.rs:177` が隙間ごとに `ROWS`（40 行）を順に照らす。重いかは測っていない（release で測ってから決める） | 保つ（`compare.py speed` と長い入力の `fmt --check`） | なし | `fmt/space.rs`（`space` に種類で引く索引） | `fmt/table_tests.rs` | 35 |
| RF-14 (b) 書き込む前の確かめの複製 | ある。`fmt.rs:53` `verify` → `diff.rs:302` `same_program` → `Side::new` → `fmt/rewrites.rs:93` が両側の AST を `clone` する | 保つ | なし | `fmt/rewrites.rs`（`normalize`）、`diff.rs`（`Side`・`same_program`）、`fmt.rs`（`verify`） | `dump.rs` | 20 |
| R-210 複合代入の候補が間のコメントを消す | ある。`r210.txt` の `compound_comment` の編集が `3:7-4:5` を ` x + ` に置き換え、`// c` を消す。`/* c */` も同じ | 変える | なし | `foreign/assign.rs`（`compound_assignment`） | `foreign/edits.rs` | 20 |
| W3-08 (1) 見出しが失敗した `#[…]` の偽の文面 | ある。`#[repr(C)]` 改行 `pub(crate struct P …` が `…has no Onsa form in this place` | 変える | なし | `foreign/decls.rs`（`hash_attribute`）、`foreign.rs`（`at_heading_hash` が場所の分からないことを渡す） | `parser/items.rs`（`parse_heading`） | 10 |
| W3-08 (2) `#[derive(…,)]` の末尾の `,` | ある。`h_derive_trailing` が `…cannot be written out as it stands`、`#[repr(C,)]` は候補あり | 変える | なし | `foreign/decls.rs`（`derive` の名前の走査） | `attrs.rs`（`sole_value`） | 10 |
| W3-08 (2') derive の括弧の中のコメント | ある（候補なし） | 範囲の外（今のままにする。理由は 2 節） | — | — | — | 0 |
| W3-08 (3) `derive()` が経路の最後の語で数える | ある。`d_path_head`（`: std.Eq`）の候補は `: Eq` を足さない | 変える | なし | `foreign/decls.rs`（`derive` の `written`） | `onsa_sema/src/sig.rs:782`（`lower_derives`） | 5 |
| W3-08 (4) derive の名前の並びの 2 乗 | ある。debug で N=2000/4000/8000 が 0.027/0.064/0.210 秒（`derive_scale.py`） | 保つ | なし | `foreign/decls.rs`（`derive` の `written`・`add`） | — | 5 |
| W3-08 (5) 直し B の 1・3・4・7 の `tests/spec` の事例の欠け | ある（単体テストと表の例だけ） | 保つ（テストを足すだけ） | なし | テストの票 | — | 0（コード） |
| W3-08 `tuple_struct_many` の文面 | ある。`struct B(4)`・`struct B()` もこの行。診断の文面（`there are no tuple structs; …`）と規則（`TUPLE_STRUCT_RULE`）は正しい。偽なのは `spec/foreign-forms.toml` の 8064 行のコメントと 8163 行の `rule`（「要素が二つ以上のときは」） | 範囲の外（仕様の表の文。親が案、利用者が了承） | — | `spec/foreign-forms.toml` | — | 0（コード） |

分類ごとの数（24 項目）: 保つ 13（うちテストを足すだけ 2）、変える 5、決定 2、済み 2、範囲の外 2。
見積もりの合計（コード）: 保つ 263 行、変える 65 行、計 328 行。

## 2. 項目ごとの修正方針

**RF-9 (a1) `Form` を三つの層に。** `enum Form { Onsa(Kind), Foreign(Foreign), Invalid(Invalid) }` とし、`Kind = Int | Float`、`Foreign = Suffix | Octal | LeadingZero | TrailingDot | DotExponent` にする。
`lexer.rs:369` の分けは `Onsa(k)` → `Int`・`Float`、`Foreign(_)` → `ForeignLit`、`Invalid` → E0001 になる。
`foreign_literal` と `spellings` は `Foreign` だけを受ける形（`Literals::number` が `ForeignLit` の数を `(Number, Foreign)` で返す）にし、`internal::bug` の腕を消す（型で保証する）。
`is_float` の `form == TrailingDot` は `Form::Foreign(Foreign::TrailingDot)` になる。出力は変わらない。

**RF-9 (a2) 文字の種類を一つのモジュールへ。** 新しい `chars.rs`（§2.3・§2.5 の文字の種類: 空白 `BLANKS`・`is_blank`、名前の始まりと続き、改行の長さ `line_break`）を置き、`lexer.rs` と `literal.rs` の両方がそこを読む。
`lexer.rs` は `pub use crate::chars::{BLANKS, is_blank}` を残し、他の crate（`onsa_driver`）と `fmt/align.rs` は変えない。依存は `lexer → literal → chars` の一方向になる。

**RF-9 (b) 名前の付いた型。** `ForeignNumber { token: Span, number: Number }` と `ForeignString { token: Span, range: Span }` を `literal.rs` に置き、`Found` と `Literals` の欄をこれにする。
`within` の 4 回の `partition_point` の切り出しは、「始まりと終わりを持つもの」の小さな trait（`fn span(&self) -> Span`）と一つの関数 `inside_of(&[T], from, to)` にする（`Touch` は `range` で絞る別の条件があるので、絞りだけを閉包で渡す）。
`Found` と `Literals` の二つの型は残す（字句解析器が積む側と、読む側で役割が違う）。

**RF-9 (c) 報告した範囲を `Hit` の欄に。** `Hit` に `held: Option<Span>`（この診断が保留した字句の誤りを代わりに報告する範囲）を足し、`string_prefix` が `held: Some(range)` と `note: faust::prime_note(...)` を自分で入れる。
`at_failure` は `prefixed = prefixed.or(hit.held)` と書き、`RowId::StringPrefix` の比べと note の分かれを消す。note は今も `diagnostic` が行の規則の後に足すので、順は変わらない。
`Hit` を直に組む 6 か所は、`Hit::new(span, fixes)` と欄を足す小さな builder（`.misplaced()`・`.resume(i)`・`.note(n)`）に寄せると、欄を足すたびに 6 か所を直さずに済む。
RF-11 の本文は、W3-23 の残りの「`at_failure` の `StringPrefix` の分かれ」を FAUST の対象外として持ち越しから消したと書く。ここで直すのは `prefixed`（FAUST でない）の分かれで、`prime_note` は動かすだけで残す。親に確かめたい（6 節）。

**RF-9 (d2) 数の候補の「合わさるか」を `edits::joining` に。** `foreign_literal` の `joins` の閉包を消し、候補ごとに `edits::joining(c.file, c.text, c.all, fix.edits())` の `after` を見て落とす（`space_around_dot` と同じ形）。
`1u8.5`（`1.5` になる）・`1u8.)`（`1.`）・`1u8.e3`（`1.e3`）・`0o17.5`（`15.5`）は落ち、`1u8..<3`・`1u8.abs()`・`1i32.(x)` は残る。今の閉包と同じ答えの見込みだが、16 進・2 進の綴りや `017` の 8 進の綴り（`0o17`）の後の `.` で読みが違いうる。
数の形 30 ほど × 後ろの形（`.5`・`.e3`・`.`・`..<`・`.abs()`・`.(x)`・`)`）の格子を、前後のバイナリで比べてから入れる。

**RF-9 (e1) 括弧の中の他言語の整数の負のパターン。** `parse_pattern_alt` の `Minus` の腕で、`-017` だけでなく `-(017)`（括弧の中が `ForeignLit` の整数）も `NegLitPat` を開いて数で失敗させ、表の `foreign_literal` が数の行を出すようにする。
`parenthesised_int_after_minus` を「括弧の中が `Int` か整数の `ForeignLit`」に広げ、`foreign_integer` を数の側の一つの述語（`Number::is_float` を読む）として残す。
出力の例: `match x { -(017) => 1, _ => 2 }` は、今 `E0002 1:33 expected a pattern, found '-'`（候補なし）、後は `E0020 1:35 a decimal integer does not start with 0…`（候補 `read it as decimal` → `-(17)`、`read it as octal` → `-(15)`）。`-(0o17)`・`-(1u8)` も同じ形で数の行になる。
当てた後の `-(17)` は S-227 の形で読める。テストの票を先に出す。

**RF-9 (e2) `-0b11f32`。** 正の `0b11f32` の読み（S-456: 接尾辞だけ除く／候補なし／`3.0`）が決まるまで、負の形も決まらない。S-456 の決定を待つ。

**RF-9 (f) 接する形の二つの側。** S-473（一つのリテラルの前後に名前がある形）が (2) に決まれば、`Touch` を「名前が前」と「名前が後ろ」の二つの記録にし、字句解析器がリテラルごとに両方を見る。S-469（`"C"lib`）と同じ回に決める。

**RF-12 (a) 行の頭の判定を役割で二つに。** トークンの添字の判定は `Lines::at_line_head` の一つにし、`Parser::starts_its_line(k)`（`k == 0 || tokens[k-1] == Newline`）を消して `k == 0 || self.lines.at_line_head(k)` にする。
二つは `k > 0` で同じ値になる（`Gap::then` は改行の後の空白で `Newline` を保ち、他のトークンで `None` に戻す。`token.rs:539`）。ファイルの頭（`k == 0`）だけ違うので、その場合は呼ぶ側に残す。
文面の位置（バイト）の判定は `lexer::line_start`・`line_head` に残し、候補の編集（行ごと動かす）と `comments.rs` の `pre` が使う。`Lines::at_line_head` の doc に、二つの層（トークンと文面）の分けを書く。

**RF-12 (b) 字下げを一つの関数に。** `indent(text, offset) -> &str`（行の頭の空白）を (a2) の `chars.rs`（か `lexer.rs`）に置き、`Cursor::indent` はそれを呼び、`parser/file.rs` の `indent` は `.len()`、`docs.rs:224` は `line_head` が `Some` のときにそれを使う。
`parser/file.rs` の `take_while(' ' | '\t')` の数は、`BLANKS` が同じ二字で ASCII なのでバイト数と同じ。出力は変わらない。

**RF-12 (c) タブの事例。** テストの票で、タブで字下げした `impl` のメンバの前とフィールドの前の `/** d */`（候補 `///`）の事例を一つ足す。`comments.rs:115` の `pre` をスペースだけで数える壊しが落ちることを確かめる（W3-24/b の変異 `pre_no_tab`）。

**RF-13 継続の判定を CST に残す。** `cst::build` に、構文解析器の `Lines` の改行ごとの `goes_on` を全てのトークンの添字（`full`）で渡し、`Cst` に `goes_on: Vec<bool>`（か bit の集合）と `Cst::goes_on(TokenIdx)` を置く。
`fmt/plan.rs` の `inside_elements` は、`(before, last)` と `continues` の呼び出しを消し、`prev` と `t` の間の最後の改行の `cst.goes_on(nl)` を読む。
同じ答えになる理由: `Lines::of` は、二つのコードトークンの間の改行の全てに同じ `continues(two_back, prev, next)` を入れ、計画の `(before, last, tok)` はその三つと同じトークンである（どちらも `is_code` で数える）。
読む改行は「ソースで `t` の直前のコードトークンと `t` の間の改行」にする。「残すトークン `prev` と `t` の間」と書かない。
計画の `before`・`last` は、fmt が落とすトークン（尾の位置の `return`）も数えるので、残すトークンだけで遡ると答えが変わる。W3-11/b の U3c が「落とす `return` で `before`・`last` がずれないこと」を確かめた点で、事例でも押さえる（`return` を落とす本体で、前の行が演算子で続く形）。
`Cst` を作る他の所（`reads_as_expr` などの部分の解析）も、自分の `Lines` から同じものを渡す。確かめは `fmt` の出力の比べ（6 節）と `cargo test -p onsa_syntax`、gate の `fmt-props`。

**RF-14 fmt の速さ。** 先に release で測る（`sample` か `cargo flamegraph` で、長い入力の `fmt --check` の時間の配分を見る）。速くする直しは、測って重いと分かった所だけ入れる。
(a) `space`: `NO` の行だけを、左のトークンの種類で引く索引にする（`OnceLock` で `ROWS` から機械的に作る。表は一か所のまま）。自己テストで、索引の答えと全行を照らす答えが全ての組で同じことを突き合わせる。
(b) 確かめ: `verify` は出力の `Parsed`（`again`）を持っているので、出力の側は `normalize` を `Parsed` を受け取って AST を動かす形（`normalize_owned`）にし、複製を一つ減らす。入力の側は借りているので複製を残す。
項目のダンプの比べ（`dump_item`）は今回触らない。
測り方:
- `compare.py speed all <基> <新> --long <dir>`（`tests`・`std`・`examples` の `check` と `fmt --check`、長い入力の `check`）。プロセスの起動が大半なので、fmt の差は見えにくい。
- 長い入力の `fmt --check` は `compare.py speed` が測らない。W3-11 の `long.py`（`.../f196c460-…/scratchpad/w311u5i/long.py <repo> <outdir> <binA> <binB>`、3 回の最小）を release の前後のバイナリで回す。入力は同じ所の `long/long0〜2.onsa`（41.6MB・11.9MB・21.9MB）が今もある。
- 10 万要素の 1 行（RF-14 の 0.032 → 0.050 s の入力）は残っていないので、`fn f() -> I32 {` 改行 `  let a = [0, 1, …, 99999]` 改行 `  0` 改行 `}` を作って足す。
- 前後とも release で、基は `gate.sh --save-base` の版から作る（`target/base` の基のバイナリは debug）。

**R-210 複合代入の候補の編集をトークンごとに。** `compound_assignment` の二つ目の編集（`=` の後から右辺の始まりまでの置き換え）を、`=` の後と右辺の始まりの間にコメントがあるときだけ、`=` の直後への挿入 ` {lhs} {op}`（括弧が要れば ` (` まで）にし、間の空白・改行・コメントを残す。
コメントが無いときは今の編集のままにする（`compare.py diags` の差が、コメントのある入力だけになる）。
出力の例: `x += // c` 改行 `    1` は、今の候補を当てると `x = x + 1`（`// c` が消える）、後は `x = x + // c` 改行 `    1`（`+` で行が続く）。`x -= /* c */ -y` は、今 `x = x - (-y)`、後は `x = x - ( /* c */ -y)`。
当てた後に新しい誤りが出ないこと（行末の `+` の後のコメントと改行、括弧の中のコメント）を、テストの票の事例で押さえる。
コメントが無いときの改行（`x +=` 改行 `1` が `x = x + 1` になる）は S-251 の「間のトークン」に当たるかが読みの分かれ目なので、親に確かめたい（6 節）。

**W3-08 (1) 場所の分からない `#[…]`。** `hash_attribute` は、閉じる `[…]` で `place` が無いとき一律に `no_form()` を返す（`decls.rs:88`）。
`at_heading_hash` から呼ばれた（見出しが失敗した）ときは `unfixable()`（`…cannot be written out as it stands`）を返し、失敗の所で呼ばれた（宣言が無い `#[inline]` 改行 `let x = 1`）ときは今の `no_form()` を残す。
分けは `Cursor` に「見出しを問う」印（`c.declaration` の有無とは別）を一つ渡す形にする。出力の例: `#[repr(C)]` 改行 `pub(crate struct P { x: I32 }` は、今 `E0002 1:1 …has no Onsa form in this place`、後は `E0002 1:1 …cannot be written out as it stands`（候補なしは同じ）。

**W3-08 (2) derive の末尾の `,`。** `derive` の名前の走査（`decls.rs:160-170`）で、`,` の後が閉じ括弧なら終わりとして受ける。
出力の例: `#[derive(Debug, Clone,)]` 改行 `pub struct P { x: I32 }` は、今 `E0002 …cannot be written out as it stands`、後は `E0020 1:1 attributes are written '@name(...)'`（候補 `write the traits at the head of the declaration`、当てると `pub struct P: Debug + Clone { x: I32 }`）。
括弧の中のコメント（2'）は、候補が属性を消すとコメントも消える（S-251・R-210 と同じ種類）ので、候補なしのままにする。§18.1 は作れない形を `unfixable` にすることを許す（W3-08/b3 の指摘 2）。

**W3-08 (3) derive の既に書かれた名前。** `derive` の `written` に、`.` で続く経路（`std.Eq`）の語を入れない（一語の名前だけを数える）。sema の `lower_derives`（`let [n] = p.segments`）と同じ読みになる。
出力の例: `#[derive(Eq)]` 改行 `pub struct P: std.Eq { x: I32 }` の候補は、今「属性を外すだけ」、後は「属性を外し、`std.Eq` の後に ` + Eq` を足す」。当てた後の `E0416 std.Eq cannot be derived` はどちらも残る（元からある誤り）。

**W3-08 (4) 2 乗の時間。** `written` と `add` の `contains` を `HashSet<&str>` での判定にし、`add` の順（書いた順）は `Vec` に残す。出力は変わらない。`derive_scale.py` を N=8000・16000 で前後に回し、線形になったことを見る。

**W3-08 (5) 事例。** テストの票で、直し B の 1（見出しの文法）・3（括弧の走査）・4（`:` の並び）・7（`}` の直前の `#[…]`）の否定例を `tests/spec` に一つずつ足す（`foreign_tests.rs` の単体テストと同じ入力でよい）。

**`tuple_struct_many` の文面。** コードの文面は正しい。`spec/foreign-forms.toml` のコメント（8064 行「要素が二つ以上なら…」）と `rule`（8163 行）を「要素が二つ以上か、要素が型として読めないか、要素が無いとき」に改める案を、親が利用者に出す。行の名前（`many`）を変えるかも同じ時に決める。

## 3. 大きいファイル: `foreign/rows.rs`（1119 行）

分けない。中身は、行の表 `ROWS`（103 行、約 930 行）、`WAITING`、共有の規則の文、`MATCHERS`（約 105 行）、`READS` で、関数の本体は無い（100 行を超える関数も無い）。
`rules/refactoring.md` 8.1 の観点で、「行の文面と出自を一か所で読む」「`spec/foreign-forms.toml` と一行ずつ突き合わせる」という一つの役割を持っており、族ごとに検出のモジュールへ散らすと突き合わせが難しくなる。行数は表のデータの量で、判断の重複ではない。
分ける候補を挙げるなら、`MATCHERS`・`READS`（どの検出がどの行を名指すかの登録簿）を `foreign/matchers.rs` へ移す形がある。これは領域 A の RF-7（`many` の検出に行を足すときの三か所: `ROWS`・`MATCHERS` の `rows`・検出の本体）が登録簿の形を変えるかで決まるので、領域 A の方針に合わせる。
この領域の項目で `rows.rs` を触るものは無い（`tuple_struct_many` の文面は toml の側）。

## 4. 項目どうしの依存

- 同じファイルを触る組:
  - `lexer.rs`・`literal.rs`: RF-9 (a1)・(a2)・(b)、RF-12 (b)（`indent` の置き場所）。(a2) で `chars.rs` を作ってから (b)・(a1)、RF-12 (b) の順。
  - `foreign/literals.rs`: RF-9 (a1)（`Foreign` だけを受ける）、(d2)（`joins`）、(e1)（読むだけ）。(a1) → (d2) の順。
  - `foreign.rs`: RF-9 (c)（`Hit`・`at_failure`）、RF-12 (b)（`Cursor::indent`）、W3-08 (1)（`at_heading_hash`）。`Hit` は領域 A（RF-7 の `many` の三か所、`Why::Differ`）も触りうるので、`Hit::new` の builder を先に入れると衝突が減る。
  - `foreign/decls.rs`: W3-08 (1)〜(4)。全て `hash_attribute`・`derive` の中で、一つの組にする。`Hit` を組む所（73・238 行）は RF-9 (c) と重なる。
  - `fmt/`: RF-13（`plan.rs`）と RF-14（`space.rs`・`fmt.rs`・`diff.rs`・`rewrites.rs`）。関数は重ならないが、どちらも fmt の出力と速さで確かめるので同じ組にする。RF-13 は `cst.rs` と `parser.rs`（`build` の呼び出し）も触り、領域 A が `parser.rs` を触るなら順を決める。
  - `parser/patterns.rs`: RF-9 (e1) だけ。`parser/items.rs`: RF-12 (a) だけ。
- 先に済ませたほうがよい順:
  1. 移すだけ: RF-9 (a2)（`chars.rs`）。
  2. 保つの直し（並列の流れ）: 組 B1 = RF-9 (a1)・(b)・(d2)、RF-12 (a)・(b)（約 140 行）。組 B2 = RF-9 (c)（約 25 行。領域 A と調整）。組 B3 = RF-13・RF-14（約 85 行。RF-14 は測ってから）。組 B4 = W3-08 (4)（約 5 行。変える組と同じファイルなので、変える組に入れてもよい）。
  3. 変える（テストの票が先、利用者が了承）: R-210、RF-9 (e1)、W3-08 (1)・(2)・(3)。テストを足すだけの RF-12 (c)・W3-08 (5) も同じテストの票に入れる。
  4. 決定を待つ: RF-9 (e2)（S-456）、RF-9 (f)（S-473・S-469）。

## 5. 材料の要点（`issues/X/X-6/` に移す分）

- W3-05/b3（`57cb6739-…/scratchpad/w305b3/handback_b.md`）:
  - 指摘 4(a)（`at_failure` の `StringPrefix` の分かれを `Hit` の「報告した範囲」の欄に）、4(b)(c)（`joins` の二か所、`take(3)`）、指摘 3（負のパターンの `-(017)`・`-0b11f32`。括弧付きの形は `ForeignLit` を見ず、`0b11f32` は `is_float` が真で新しい腕に入らない）。
  - 「リファクタリングの候補」の 3（Touch を名前の側とリテラルの側の 2 種に）、4（整数か浮動小数かをパーサの `foreign_integer` から外す）、5（`strings`・`numbers` に名前）。
  - 退行でない観察: 単位 N 個の `match x { -017 => 1, _ => 2 }` が 2 乗の時間（N=8000 で 15.1 s、原因は未調査）。RF-9 (e1) で負のパターンの経路を触るときに測るとよい。
  - `w305b1/`・`w305b2/` に報告のファイルは無い（入力と道具だけ）。
- W3-24/b2（`fdec036b-…/scratchpad/w324b/handback_b2.md`）: タブの字下げの `/** */` の事例が無く、変異 `pre_no_tab` が通る（RF-12 (c)）。比べの道具は同じ所の `cmp.py`・`cases6.py`〜`cases8.py`・`mutate2.py`。
- W3-11/b の U3c（親が取り戻した報告 `44 回目の scratchpad の x6/materials/w311u3cb/handback.md`）:
  - 指摘 3（低）: `continues` の呼び出しは `Lines::of` と `inside_elements` の 2 か所。判断の関数は一つだが、`before`・`last`（コードトークンを二つ遡る走査）を plan が書き直している。案は `goes_on` を CST に持たせること。判断が分かれる危険は小さく、急がない（RF-13 の出所）。
  - 「確かめて問題の無かった点」: 落とす `return` で `continues` に渡す `before`・`last` がずれない。RF-13 で読む改行の選び方（2 節）に効く。
  - 「速さ」: `inside_elements` を含む計画は、`args`・`arms`・`stmts`・`letattr`・`attrs`・`nest` で 16000 まで線形（道具は同じ所の `bt/speed.py`）。RF-13 の前後でも同じ道具で線形を見るとよい。
- W3-11 の U5（`f196c460-…/scratchpad/`）:
  - `w311u5i/handback_i.md` の「速さ」: release の `fmt --check` が long0/1/2 で 1.70/1.84/1.74 倍（0.293→0.499 s、1.603→2.955 s、0.239→0.416 s）。増えた分は二度目の解析、AST の複製二つ、項目のダンプ。
  - `w311u5i/handback_i3.md`: 書き換えの CST の側で「親の最後の子か」を子の数に比例する形で書くと長い本体で 2 乗になる（`last_node` のように末尾から引く）。RF-14 (b) で `normalize` を触るときの注意。
  - `w311u5b/handback_b.md` の「速さ」: 項目・コメント・文・doc・`return` など 10 の形で 40 万行まで線形、比 1.6〜2.1 倍。道具は同じ所の `scale.py`・`scale2.py`。
  - 長い入力の作り方 `w311u5i/long.py` と入力 `w311u5i/long/long0〜2.onsa` は今もある。
- W3-08/b3（`fdbb2778-…/scratchpad/w308b3/handback_b.md`）: 指摘 1〜4 の原因（`decls.rs` の `let Some(place) = place else { return no_form() }`、`derive()` が `,` の後に `Ident` を求める、`written` が経路の最後の語、`add.contains`・`written.contains` の線形探索）。
  断片の道具は同じ所の `pr.py`（`W/h1.txt`・`h2.txt`・`d1.txt`）。
- RF の単位 1 の差の一覧（`747db489-…/scratchpad/rfi/`）: ディレクトリだけで、ファイルが一つも無い（`dif_*.txt`・`check_diffs.json` も無い）。`issues/X/X-6.md` の「差の一覧は … `rfi/dif_*.txt`・`rfi/check_diffs.json`」は今は辿れない。

### 持ち越しの仕分け: `foreign.rs` の深いリファクタリング

| 箇条 | 仕分け | 確かめた所 |
|---|---|---|
| 範囲: RF-5〜RF-8 を区切りの良い時に | X-6 の範囲（他の領域） | `issues/X/X-6.md` の決めたこと |
| 二つの行が一つの失敗に当たる検査が `debug_assert` | 済んだ（RF-2、`826fc8a`） | `at_failure` は全ての行の診断を出し、`foreign*.rs` に `debug_assert` は無い |
| 出力を変えない条件の例外（RF の単位 1） | 済んだ（記録。`7fd6b15`） | — |
| 性能の条件の判断（RF の単位 2） | 済んだ（記録。`826fc8a`） | — |
| 重なりの選び方の範囲: 検出の中の除外四つ、登録簿の自己テストが捕まえない三つ | 領域 A（RF-7 の `many` の三か所） | `foreign.rs:541-554` の doc に除外四つが残る |
| 材料: `layout.rs` と `parser.rs` の循環 | 済んだ（RF-3、`7fd6b15`） | `layout.rs` は `starts`・`token` だけを読む |
| 材料: `starts_element` の表が構文解析器の「何で始まるか」と別 | 済んだ（`7fd6b15`） | `starts.rs:111` に `starts_element`・`comma_list`・`starts_operand` が一か所 |
| 材料: `merge_strings` の置き場所 | 済んだ（後の作業で `foreign/lists.rs:88` へ） | — |
| 材料: `type_position_path`・`space_in_type_args_mark`・`binary_minus_minus` の `c.gap(c.at + 1)` | 済んだ（`7fd6b15`） | `paths.rs:378・399`、`assign.rs:131` が `gap_after` を読む |
| 材料: R-206 | 済んだ（RF-2、R-206 は DONE） | `docs.py show R-206` |
| 範囲の案は W3-06 の後に親が出す | 済んだ（進め方の記録） | — |
| 行の情報をトークンの属性に、5 つの書き方と `fmt_props.py` の `CONTINUING` を消す | 済んだ（RF-1、`7fd6b15`） | 5 つは `Lines` を読む（`parser/expressions.rs:56・68`、`parser/file.rs:224`）。`fmt_props.py` は `--continuing` でバイナリに問う |
| 壊す側の候補: `Parser::ends` を `closed` から導く | 領域 A（RF-7） | RF-7 の題 |
| 壊す側の候補: `leading_symbol` を記号ごとの関数に | 済んだ（`826fc8a`） | `foreign/lines.rs` の `leading_arrow`・`leading_eq`・`leading_binary` |
| 壊す側の候補: `list_fixes` の三つの分岐を表に | 領域 A（RF-7） | `foreign/lists.rs:53` |
| W3-06/b の B: 「`&` の次が `mut`」の二か所 | 済んだ（`826fc8a`） | `Cursor::ref_mut`（`foreign.rs:639`）を `lines.rs:189` と `modes.rs:21` が読む |
| 移すだけの整理（表を `foreign/rows.rs` へ、検出を族ごとのモジュールへ） | 済んだ（`7fd6b15` ほか） | `foreign/` の 17 のモジュール |

「W3 の終わり」の (5) の R-210 は、この領域の R-210 の行。

## 6. 範囲の外で気付いたこと

1. `compare.py speed` は長い入力に `check` だけを回し、`fmt --check` を測らない。RF-14 のような fmt の速さの直しは `long.py` を別に回すことになる。`--long` で `fmt --check` も測る形にする道具の案（`rules/tools.md` 9.2 で親が判断）。
2. fmt の出力を前後のバイナリで比べる道具が無い（`compare.py diags` は `check --json` だけ）。RF-13・RF-14 を「保つ」で確かめるには、同じ入力の集まり（`tests` の事例と fuzz の種）を二つの一時のディレクトリに写して `onsa fmt` を回し、出力と終了コードを比べる `compare.py fmt` があると、並列の流れのマージの前の確かめに入れられる。
3. RF-9 (c) と RF-11 の重なり: RF-11 は W3-23 の残りの「`at_failure` の `StringPrefix` の分かれ」を FAUST の対象外として持ち越しから消したと書く。RF-9 (c) の分かれの主は `prefixed`（S-400 の保留の解き放ち）で FAUST でないので、この領域で直してよいか。
4. R-210 の範囲: コメントが無いときも、今の編集は `=` の後の改行トークン（`x +=` 改行 `1`）を置き換えて消す。S-251 の「間のトークン」に改行を含めるなら、改行だけの場合も挿入にする（そのときは `compare.py diags` で全ての複合代入の事例の編集が変わる）。
5. W3-05/b3 の観察（単位 N 個の `-017` のパターンで 2 乗の時間）は、まだ測り直していない。RF-9 (e1) の組で前後に測るとよい。
6. `issues/X/X-6.md` が指す 12 回目の `rfi/dif_*.txt`・`check_diffs.json` が無い（5 節）。RF の単位 1 の記録なので無くてよい（親）。

## 7. 未確認

- RF-14 の時間の配分（release での測り）は、ビルドと長い入力の実行が要るので行っていない。(a)・(b) が効くかは測ってから決める。
- RF-9 (d2) の `edits::joining` との一致は、コードの読みだけ（格子での確かめは実装の時）。
- RF-12 (a) で `comments.rs` の `pre` を `Lines::at_line_head` に替えない理由（全角空白などの書けない文字で行が始まるときに文面とトークンの答えが割れうる）は、入力で確かめていない。

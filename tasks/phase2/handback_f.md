## 作業 W3-12/i 単位 U1 の直し（S-536 (1)・S-539・S-546・move の場所・/b の指摘 1・2・6〜9）の報告

**状態:** WIP のコミットは 3 つで、最後は `d43de9e` です。
- `a22194b`: S-536 (1)、/b の指摘 1・2・6〜9
- `a2bbcf1`: テストと rustfmt
- `d43de9e`: S-539、S-546、move の場所、fmt-props の対応付け

作業ツリーは `/Users/centrevillage/projects/onsalang/.claude/worktrees/agent-a268bf037d6b46d1d`（07a0e81 の上）で、作業ツリーに未コミットの変更はありません。`dev` にはコミットしておらず、`git stash` も使っていません。
patch は `P28/w312u1f/u1f.patch` です（`P28` は票の略で、scratchpad の経路）。

**gate の結果は FAIL です。落ちたのは fuzz と gap-marks で、どちらも票が予期した理由です。** 他の項目はすべて PASS でした（test、fmt、clippy、fmt-props、fmt-comments、fmt-cst、gate-selftest、ignores ほか）。

**行数:** 着手の時点の見積もりは、テストとデータを除いて約 +150 −50 でした（`P28/w312u1f/estimate.txt`）。
- 結果は、テストとデータを除いて +310 −290 です（`tools/take.py patch … 07a0e81`）。全体では 22 ファイル、+818 −600 です。
- 見積もりを超えたのは、途中で 3 つの決定（S-539、S-546、move）が加わったためです。正味は +20 で、3 倍の基準には届きません。

### 決まったことごとの変更と証拠

**S-536 (1)（c-i）**
- `fmt/breaks.rs` を書き直しました。
  - 消したもの: `held`・`ends`・`written` の帳簿、`(held && !own)` と `line_end(…) != ends` の判定、「The form so written must read…」の段落、`SPEC-GAP(S-536)` の印。
  - 判定は一つになりました。隣の改行は、行の終わりか並びの縁でなければ一緒に落とします。範囲（最初から最後の落とすトークンまでと、落とす改行の隙間）にコメントがあれば `None` を返します。
  - `rewrites::code_of` のコメントの旗はこの判定に含まれるので外しました。
- U1 の `-> ()`・`uses {}` の出力は、次の形を除いて今と同じです。リポジトリの全ファイルで U1 のバイナリと比べ、違いは下の 3 件だけでした（`compare_out.py`）。
  - 変わる形: 値の無い末尾（型の別名、フィールド、メンバ）の `-> () // c` 改行 `uses {}` です。
  - U1 は 1 回目に `uses {}` だけを落とし、2 回目で `-> ()` も落としていました（冪等の破れ）。今は両方とも残ります。
- コメントの無い形で、土台だけで別の木や構文の誤りになる形は見つかりませんでした。`mut.py` で 8414 件の変異（改行、空行、CRLF を含む）を試し、C（diff）・D（診断）・101 の検出は 0 件でした。
- テスト:
  - `a_comment_out_of_the_range_stays_on_its_line_and_one_in_it_keeps_the_tokens`（単体）
  - `a_comment_in_the_range_of_a_rewrite_keeps_its_tokens_and_one_out_of_it_stays_on_its_line`（CLI）

**指摘 1（後ろに `uses` が続く `uses {}`）**
- `empty_uses` は、次の残るトークンが `uses` か `at` なら節を選びません。
  - `at` も同じ扱いにした理由: `flow g(h: fn() -> I32 uses {} at sample)` を U1 のバイナリにかけると、101 になりました（E0020）。
  - `all_nodes` は外側の節から回ります。そのため `uses {} uses {}` の 2 つは、1 回で両方落ちます。
- `-> ()` を外して後ろの `uses`・`at` の付く先が変わる形はありません。`()` の後ろの `uses` は同じ頭のものです。`-> () at` は、Clock が子にあるので外しません。
- ダンプの設計: `dump.rs` に `result()` を足しました。関数・無名関数・関数型・flow の返り値が関数型なら、`<fn() -> I32 uses {}>` のように `<` `>` で囲みます。
  - 引数の位置の関数型は変えていないので、parser_tests の期待値は不変です。
  - `diff --ast` の結果は、`w/g1.onsa` と `w/g2.onsa` で 1 になりました（U1 では 0）。
- テスト: `an_empty_uses_before_another_uses_stays`（単体と CLI）

**指摘 2（冪等）**
- S-536 (1) だけで冪等になったので、一つの判定にまとめる直しは要りませんでした。
- 証拠: `mut.py` の B は 24 件から 0 件になりました。CRLF 版も 32 件から 0 件です（`P28/w312u1f/bgmut1`、`bgmut2`）。
- gate に足した事例: `tests/spec/fmt/rewrite_heads_comments.onsa`（正規形、parse）。
  - 頭、引数、型の別名、フィールド、trait・extern・effect のメンバに、`-> ()` の後で改行した形を置きました。指摘 1 の形と `at` の形も入れました。
  - U1 のバイナリでは 101 になります。

**指摘 6（二次）**
- `breaks::Pairs` を足しました。各節の括弧の対を一度だけ読み、Ctx に覚えておきます。

| 形（`fmt --check`） | e6a8fa0 | U1 | 直し |
|---|---|---|---|
| trait n=4000 | 0.014s | 0.082s | 0.015s |
| trait n=16000 | 0.052s | 1.287s | 0.059s |
| extern n=16000 | 0.067s | 1.342s | 0.073s |
| effect n=16000 | 0.067s | 1.348s | 0.072s |
| `-> () // c` 改行 `// d` n=20000 | 0.075s | 5.265s | 0.079s |

- 全ファイルの合計（`perfile.py`）は、U1 が 3.173s、直しが 3.157s です。

**指摘 7（名前の長さ）・指摘 9（権限の窓）**
- 一時ファイルの名前は、元の名前の先頭 64 バイトまで（文字の境目で切る）と pid と番号にしました。
- 一時ファイルは mode 0600 で作り、本文を書く前に元の権限にします。
- テスト: `fmt_writes_a_file_whose_name_is_long`（ASCII 250 バイトと 3 バイト文字 254 バイト）。
  - U1 のバイナリでは、ASCII の名前で `File name too long`（2）になりました（`longname.py`）。

**指摘 8（gate の道具）**
- `left_out` を、fmt が実際に落とす条件に揃えました。除くのは次の形です。
  - flow の頭、`at` の前の `-> ()`
  - 後ろに `uses`・`at` が続く `uses {}`
  - 範囲にコメントがある形
  - 無名関数（S-546）
- `line_key` は、行の中の字面ではなく `dropped()`（`left_out`）で、外すトークンを決めるようにしました。
  - これが無いと、新しい事例の `// s2` 改行 `uses {},` で fmt-comments が誤って落ちました（最初の gate）。
- 自己テスト `test_left_out_is_what_the_rewrites_drop` を足しました。
- `fakeprops.py t/f3.txt` で、flow の継続の改行を潰した偽の出力を `breaks` が検出するようになりました。

**親の気付き（`kinds`）**
- `print_tests::kinds` は、`rewrites::choose` の `dropped` だけを比べから外します（`,` は今どおり）。
- 失敗の文面も「a token other than `,` and those the rewrites of §3.3 drop」に揃えました。

**S-539（`init` を外さない）**
- 外したもの: `init`・`init_ast`・`REWRITES` の行、`literal::is_zero`、`Ctx.src`（そのため `choose` と `normalize` の引数から src も外しました）。
- `delay.rs` は残し、doc だけ直しました。
- fmt_props の `zero_inits`・`DELAY_INITS`・`is_zero` と、`init` の部分を外しました。
- CLI のテストは「fmt は `init` を変えない」に改めました。
  - 残した事例: 既定値、綴り違い、`false`（ignore を外した）、`init` に既定値でない値を書いた形（変更なし）、ブロック形（コメント付き）、行末のコメント。
  - `i_beside_kept` は外しました。
  - `diff_ast_sees_…` の `i_bool` の除外も外しました。
- 単体テストは `the_init_of_the_value_zero_stays` です。
- loose の事例から `init_*` の flow を外しました。`rewrite_init_kept.onsa` には 0 の `init` の flow を足し、頭のコメントを直しました。

**S-546（無名関数の `-> ()`・`uses {}` を残す）**
- `HEADS` から `ClosureExpr` を外し、`head_of` の腕も外しました。
- CLI の `u_closures` を「残す」に改めました（テスト名は `unit_return_type_and_empty_uses_of_an_anonymous_function_stay`）。
- `x_combinations` の `let g` は `uses {}` を残す形にし、理由のコメントに S-546 と書きました。
- 単体テストは `the_head_of_an_anonymous_function_and_the_move_of_a_value_stay` です。
- `take(fn(x: I32) -> () { x })` は E0401 のまま残ります。

**move の場所**
- `Ast::place_root` を一つの定義として置きました。名前一つか、場所のフィールド・添字・タプル要素で、括弧も通します。
  - sema の `is_place` は、これに局所かどうかの判定を足して読みます。
  - fmt の `ret_move` は形だけを読みます。
- fmt は `choose` に `Parsed` を渡し、CST の MoveExpr を AST へ引く表を作ります。そのため `print`・`Plan::new` の引数は `&Parsed` になりました。
- 結果: `move g()` と `move h().b` は残ります。`move a`・`move a.b`・`move a[0]`・`move a.b[0].0` は外れます。
  - `move a.b` と `move a[0]` は、前後とも同じ E0711（部分の move）です。
- テスト: CLI の `move_of_a_value_that_is_not_a_place_stays`、上の単体テスト。

`cargo test -p onsa_syntax -p onsa_sema -p onsa_cli` は 954 件が通り、失敗 0、ignore 4 です。

### gate の要約（`P28/w312u1f/bg_gate2/out`）
- `gate: FAIL (fuzz, gap-marks)`
- fuzz は `fix|E0003|move … to the end of the line before|E0001` の 1 類だけでした。前の gate と同じ類で、親が登録済みです。
  - U1 で出ていた E0812 の類（seed は loose の `a.prev~`）は、その flow を外したので今回は出ていません。
- gap-marks は `main.rs:342 S-535` だけで、主のツリーの未コミットの行が無いためです。S-536 の印は外れました。
- 1 回目の gate（`bg_gate`）は fmt-comments も落ちていました。原因は上の `line_key` で、直しました。

### 範囲の外で気付いたこと・原則に反する形
- **原則（判定を変えない）に反する形が 1 つ残ります。** `move` の被演算子が局所でない名前（定数）のときです。
  - 再現: `const K: I32 = 1` と `fn f() -> I32 {` 改行 `move K` 改行 `}`。
  - `check` は E0711 ですが、fmt は `move` を外し、誤りが消えます。
  - 名前が局所かどうかは構文の段では分からないので、`move a` を外す決定とは両立しません。親の判断が要ります。
- **新しい空白の候補です（下に空白の報告の形で書きます）。** `type T = fn(F32) -> ()` 改行 `  uses {} // c` は `type T = fn(F32) // c` になります。
  - 前の改行は一緒に落ち、コメントは範囲の外なので残ります。
  - S-538 の「行にコードが残らなければコメントだけの行として残る」とは別の結果です。
  - gate の道具では、この形は「own から end へ移った」と報告されます。gate の入力には今は現れていません。
- `fmt_rewrites.rs` の `comments_of_an_init_that_goes_from_a_list_are_kept_once_and_in_order` は、名前に「goes」が残っていますが通ります。名前は直していません。
- **ツール化の案:** `compare_out.py`（2 つのバイナリの fmt の出力を全ファイルで比べる）は、出力の変化を見るのに毎回使えます。tools に置く価値があります。

### 空白の報告
- 仕様の空白: NEW。落とすトークンだけの行の行末のコメント。
  - 仕様の文: `docs/onsa-tools.md` §3.4 と S-538（行にコードが残らなければコメントだけの行）、S-536 (1) の土台（隣の改行は一緒に落とす）。
  - 割れる読み:
    - (1) 改行が落ちるので前の行に付く（今）。
    - (2) S-538 と同じく、コメントだけの行として残す。
  - 再現: `type T = fn(F32) -> ()` 改行 `  uses {} // c` 改行 `type U = I32`。今は `type T = fn(F32) // c` になります（`P28/w312u1f/t/j1.onsa`）。
  - 仮の扱い: (1)。待つもの: 無し。急ぎの見立て: U2 の前（括弧の行でも同じ形が出る）。

### golden とテストベクトル
- 変更はありません（`golden: no file differs from HEAD`）。

### 自己点検（§8.5）

| 種類 | 結果 |
|---|---|
| 何も走らずに通る | 新しいテストは、期待値の全文か `formatted` の不動点で比べている。道具の自己テストは 15 の入力の結果を全部比べる |
| 実装待ちの一覧で黙らせる範囲 | 一覧は触っていない |
| 判断の重複（D-15） | 場所の形は `Ast::place_root` の一か所。改行の判断は `breaks.rs` の一か所。fmt_props の `left_out` は、道具が意図して持つ独立の判断 |
| 位置と黙った捨て方 | AST の側の食い違いは、今どおり `internal::bug` |
| この機械 | 落ちるプロセスは作っていない。終了コードは 0・1・2・101 だけ |
| 決定性と時間 | 乱数は使っていない |
| 大きさ | 見積もりの 3 倍未満 |

### 次の担当へ（U2 の担当）
- **状態:** WIP `d43de9e` です。
- **仕組み**
  - `choose(parsed, nodes)` は `&Parsed` を取ります。そのため `print`・`Plan::new` も `&Parsed` を取ります。
  - 字を落とす書き換えは `take_off`（`breaks::with_breaks`）を通します。範囲にコメントがあれば `None` を返し、節は選んだまま字は落としません。
  - 括弧の対は `cx.pairs` で、一度だけ読みます。
- **U2 への注意**
  - ダンプは関数型の返り値を `<…>` で囲みます。型の括弧は `ty()` が書くので、括弧を外す書き換えでは AST の側で `parens` を減らす必要があります。
  - 括弧の (b) の形（範囲にコメントがある形）は、S-536 (1) により残ります。
  - fmt_props の `left_out` に括弧を足すときは、`line_key` が `dropped()` を読むことに注意してください。
- **最初に読むもの:** `fmt/breaks.rs`、`fmt/rewrites.rs` の `empty_uses`・`ret_move`、`dump.rs` の `result`、`tools/fmt_props.py` の `left_out`・`closure_heads`・`dropped`。

### 道具（`P28/w312u1f/`）
- `b/`: /b の道具の写しで、経路を書き換え済みです。
- `scale3.py`: 3 つのバイナリを比べます。
- `compare_out.py <old> <new> <root> [事例ファイル…]`: 全ファイルの fmt の出力を比べます。
- `longname.py <onsa>`: 長い名前の書き込みを試します。
- 再現の入力は `t/` にあります（`s536.cases`、`move.cases`、`j1.onsa`、`at1.onsa`）。
- 旧バイナリ: `bin/onsa-u1`（07a0e81 の release）、`rel/onsa`（直しの release）。

### 引き継ぎの記録
- 指摘 1 の `uses {}` は、残すだけでなく節も選びません（比べでも書き換えない）。正しいプログラムは同じなので、どちらでもよい選択でした。
- `at` の場合も、指摘 1 と同じ扱いに広げました。
- S-539 で `Ctx.src` が要らなくなり、`choose` と `normalize` の引数から外しました。その後、move のために `choose` は `&Parsed` を取る形になりました。
# X-6 手順 1 の調べ: 領域 D（テストの器 onsa_tests・診断の順・道具）

調べた木: 主のツリー `/Users/centrevillage/projects/onsalang`（dev `ee6a2bd`）。コードは変えず、ビルドもしていない。確かめは読むことと `rg`・`git log`・`refactor.py sizes`・道具の `help` だけ。

## 1. 項目の表

| 項目 | 今もあるか（確かめた所） | 分類 | 〔危険〕 | 触るファイル（関数） | 読むだけのファイル | 見積もり（変える行） |
|---|---|---|---|---|---|---|
| RF-10 S1 (a) 表示の順を一つに | ある。`onsa_diag/src/lib.rs:486` の非公開の `sorted`（名前・行・列・終わりの行・列・コード・文面）と `:217` の `Diagnostic::order_in_file`（始め・終わりのバイト・コード・文面）が別の鍵 | 保つ | なし | `crates/onsa_diag/src/lib.rs`（`sorted`、`order_in_file` の doc、新しい公開の関数、テスト） | `onsa_diag/src/source.rs`（`line_col`） | 25（テスト +15） |
| RF-10 S1 (b) `fix_loop` の並べ直し | ある。`onsa_tests/src/fix_loop/walk.rs:132` の `pick` が `order_in_file` で自分で並べ直す | 保つ | なし | `crates/onsa_tests/src/fix_loop/walk.rs`（`pick`） | `fix_loop/mod.rs`（`Checked`） | 10 |
| RF-10 S1 (c) `per_unit` の出力の順 | ある。`onsa_driver/src/reduce.rs:63` の `per_unit` は入力の順（段の順）のまま返す。並べないのは `reduce.rs` の doc の方針（S-234: 順は描くときに一度だけ） | 保つ（doc だけ） | なし | `crates/onsa_driver/src/reduce.rs`（`Reduced` の doc） | `onsa_syntax/src/units.rs:139`（`choose` の鍵） | 6 |
| RF-10 S1 (d) 器の文面の順（`per_unit` の順で読む所） | ある。`fix_contract.rs:821` の `describe` が `analyzed.diagnostics` を段の順で並べる（`[[test.fix]]` の誤りと `clean` の失敗の文面） | 変える（器の失敗の文面だけ。コンパイラの出力は変わらない）。任意 | なし | `crates/onsa_tests/src/fix_contract.rs`（`describe`） | — | 6 |
| RF-18 (A) 作業の ID から段を出す判断 | ある。`docs.py:808`（check (a)）、`:1112-1114`（`due_key`。RF の本文に無い 6 か所目）、`:1421`（`graph`）、`:1530`（`show --relations` の `depended_by`。RF の「waiting」はこの行）、`:1635`（`list --count`）、`pending.py:158`（`stage_of`） | 保つ | なし | `tools/repo.py`（新しい `split_work`）、`tools/docs.py`（上の 5 か所）、`tools/pending.py`（`stage_of`）、`tools/test_gate.py`（自己テスト） | `tools/ignores.py:72`（`WORK_AT_START`。綴りの照合で段は出さない） | 30 |
| RF-18 (B) `spec_tokens.py` の §6.6 の表の読み | ある。`tools/vectors/spec_tokens.py:65-66` が `startswith(("| 整数 |", …))` と `line.split("|")[2]` | 保つ | なし | `tools/vectors/spec_tokens.py`（`spec_constants`）、`tools/vectors/gen.py`（`sys.path` の順） | `tools/repo.py`（`table_cells`） | 10 |
| RF-18 (C1) 頭の欄の `status` の読み | ある。`gap_marks.py:101` の `dropped_ids` と `docs.py:753` の `Index.work_done` が、それぞれ頭の欄を読んで `status` を比べる。`pending.py:165` の `if not works` は `Index.ids` の誤りの文の複製 | 保つ | なし | `tools/docs.py`（`Index` に `statuses`）、`tools/gap_marks.py`（`dropped_ids`）、`tools/pending.py`（`load_docs`） | — | 15 |
| RF-18 (C2) 段の並びの判断 | ある。`pending.py:328` の `stage_key`（表の順 → PH2 → 他は文字列の順）、`docs.py:1637-1639` の `list --count`（表の順 → 他は `id_key(g + "-0")` の番号の順）、`docs.py:1102` の `due_key`（作業込み） | 変える（表に無い段の並びだけ） | なし | `tools/repo.py`（新しい `stage_key`）、`tools/docs.py`（`list --count`、`due_key`）、`tools/pending.py`（`stage_key` を消す）、`tools/test_gate.py` | — | 20 |
| RF-18 (C3) `spec_sections.py` のテストの読み | ある。`spec_sections.py:44` の `TEST_MOD`、`:90` の `without_test_mods`（自前の括弧の走査）、`:133` の名前の規則が、`repo.is_test_file`・`repo.test_lines`・`repo.rust_code`（X-9 U17）と重なる | 変える（道具の判定の境だけ。今の木では差 0 の見込み） | なし | `tools/spec_sections.py`（`without_test_mods`、`compiler_sources`） | `tools/repo.py` | 40（ほぼ消す行） |
| RF-18 (C4) `builtin_names.py` のテストのファイルの名前 | ある。`builtin_names.py:393` の `is_test_file` が `repo.is_test_file`（`NOT_CODE`）の複製。`test_ranges`（`#[cfg(test)]` の下の全ての項目）は `repo` に代わりが無いので残す | 保つ（`crates/` の下では同じ判定） | なし | `tools/builtin_names.py`（`is_test_file`、`scan`） | `tools/repo.py` | 5 |
| 大きいファイル `run.rs` を分ける | 1505 行（テスト込み 2433）。`run_case_with` 259 行、`reconcile` 159 行 | 保つ | なし | `crates/onsa_tests/src/run.rs` → `run/` | `ccheck.rs`・`fix_contract.rs`・`fixes.rs`・`host/tests.rs`・`bin/onsa_cases.rs`（`crate::run::…` の利用者） | 移す約 1050、書き換え約 180 |
| 大きいファイル `fix_contract.rs` を分ける | 1131 行（テスト込み 1500） | 保つ | なし | `crates/onsa_tests/src/fix_contract.rs` → `fix_contract/` | `fragment.rs`・`fixes.rs`・`copy_guard.rs`・`fix_loop/`・`bin/onsa_cases.rs`（利用者） | 移す約 750、書き換え約 70 |

## 2. 項目ごとの修正方針

### RF-10 S1 (a) 表示の順を一つに（保つ）

- 同じ順であることの根拠: 一つのファイルの中では、`line_col` は文字の境のオフセット（ファイルの長さ以下）について狭義に単調（`source.rs:85`。列は文字で数え、`\r` も一字）。よって `(行, 列, 終わりの行, 列)` の比べと `(始め, 終わり)` のバイトの比べは同じ結果になる。文字の中のオフセットは `line_col` の内部エラーで、長さを超えるオフセットは段の誤り（どちらも今の出力に無い）。
- `onsa_diag` に公開の関数を一つ置く: `pub fn printed_order(sources: &SourceMap, diagnostics: &[Diagnostic]) -> Vec<usize>`（安定な並べ替えの添字。鍵は `(sources.file(d.span.file).name(), d.order_in_file())`）。`sorted` はこれを使って参照を返すだけにする（`to_json`・`to_text` は変えない）。
- `order_in_file` の doc を「`printed_order` の一つのファイルの中の部分（§18.1、S-234、S-281）」に改め、`sorted` の doc の鍵の列挙を一か所（`printed_order`）に寄せる。
- 並べ替えで `line_col` を呼ばなくなるので、描く前の並べ替えは速くなる（`compare.py speed` で確かめる）。
- テスト: 今の `the_order_is_the_file_string_then_the_position_then_code_and_message` を残し、多バイトの字と CRLF の行を含むファイルで、`printed_order` と `(行, 列, …)` の鍵の順が一致する単体テストを足す。
- 確かめ: `cargo test -p onsa_diag -p onsa_driver -p onsa_cli`、`compare.py diags`（差 0 件）、`compare.py speed`。

### RF-10 S1 (b) `fix_loop` の `pick`（保つ）

- `walk.rs:127-138` の `pick` を、`onsa_diag::printed_order(&checked.sources, ds)` の並びから候補を持つものに絞り、最初か最後を取る形にする（自前の `sort_by` を消す）。doc は「表示の順（`onsa_diag::printed_order`）」を指すだけにする。
- 一つのファイルの検査なので、今の `order_in_file` での並べ替えと同じ結果（同じ鍵の同順位は、どちらも安定な並べ替えで入力の順）。
- 確かめ: `cargo test -p onsa_tests`（`fix_loop_tests.rs`）、`onsa_cases --fix-loop` の要約（gate の fix-loop の項目と同じ入力）を前後で比べて同じ。W3-22/b の `order_check.py` と同じ観点（候補を持つ最初・最後の診断が fix-loop の 1 歩目と一致、466 回）を自作の掃引で回すとよい。

### RF-10 S1 (c) `per_unit` の出力の順（保つ、doc だけ）

- `per_unit` は並べ替えない（`reduce.rs` の doc の「None of them orders its output」と S-234 の「順は描くときに一度だけ」を保つ）。並べると `diagnostic_units` の対応も並べ直す要があり、利用者（`fix_contract` の `judge` は `diagnostics` と `diagnostic_units` を zip する）に効く。
- `Reduced::diagnostics` の doc に「入力の順（段の順）で、表示の順ではない。表示の順が要る読み手は `onsa_diag::printed_order` を使う」と書く。
- これで RF の「`per_unit` の出力の順は段の順で、表示の順と違う」は、読み手が使う関数が一つになることで閉じる（順そのものを二つ持たない）。
- `units.rs:139` の `choose` の鍵（段の順位、`order_in_file`、添字）は S-281 の「単位の中の選び方」で表示の順とは別の判断なので変えない（`order_in_file` を使うので一つの定義のまま）。

### RF-10 S1 (d) `fix_contract::describe` の順（変える、器の文面だけ、任意）

- `describe` を `printed_order` の順で並べる。変わるのは `onsa_tests` の失敗の文面だけで、コンパイラの出力（`check --json`・`fmt`・`test`・C・値）は変わらない。
- 例: 誤りが構文の段（3:5 の E0020）と型の段（1:1 の E0401）にある事例で、`[[test.fix]]` が名指す診断が無いとき、今は「the check reports E0020 at 3:5, E0401 at 1:1」、後は「E0401 at 1:1, E0020 at 3:5」。
- 器の自己テストは `describe` の並びを固定していない（`rg "the check reports"` で `run.rs`・`fix_contract.rs` のテストに無い）。器の文面を変えてよいかは親が決める（親への質問 1、返答に書いた）。行わなくても S1 は (a)〜(c) で閉じる。

### RF-18 (A) 作業の ID から段を出す判断を一つに（保つ）

- `tools/repo.py` の ID の節（`kind_of` の隣）に `split_work(id_)` を置く: `"W3-05"` → `("W3", 5)`、作業の ID でなければ `None`（`KIND["W"].pattern` で fullmatch してから分ける。作業の ID の綴りを読む一か所、D-15）。
- `docs.py:808` → `split_work(id_)[0]`（`files["W"]` の ID は綴りに合うものだけなので必ず値がある）。`:1112-1114` の `due_key` → `w = repo.split_work(due)` があり `w[0] in stages` なら `(stages.index(w[0]), w[1])`。`:1421`・`:1530`・`:1635` → `split_work(...)[0]`。
- `pending.stage_of` は `PH2` と段の名をそのまま返す分岐を残し、作業の分岐を `(repo.split_work(work) or (None,))[0]` にする（`WORK` の再コンパイルも `repo.id_form("W")` に寄せられる）。
- 呼ぶ所はどれも、作業の ID か綴りを確かめた値だけを渡すので、出力は変わらない。
- 確かめ: `python3 -B tools/test_gate.py`（gate-selftest。`stage_of` の 678・781 行、`due_key` の 7266 行、`list --count` の 7226 行の自己テスト）に `split_work` の自己テストを足す。前後で `docs.py check`、`docs.py list W --count`、`docs.py graph W3`、`docs.py show W3-05 --relations`、`docs.py list S --before W4`、`pending.py check`、`pending.py list` の出力を比べて同じ。

### RF-18 (B) `spec_tokens.py` の §6.6 の表の読み（保つ）

- `spec_constants` を `cells = repo.table_cells(line)` で読み、`cells[:1]` が `["整数"]` か `["浮動小数"]` の行の `cells[1]` から `` `[A-Z_]+` `` を取る。
- `spec_tokens.py` に `import repo` を置くには、`gen.py:30-33` で `import spec_tokens` より前に `tools/` を `sys.path` に足す（今は後）。`test_vectors.py` は `gen` を先に読むので、それで足りる（`spec_tokens.py` 自身が `sys.path` を足す形は他の vectors の模様に合わない）。
- 今の §6.6 の表の行は code span の中に `|` を持たないので、集合は同じ。
- 確かめ: `python3 -B tools/vectors/test_vectors.py`（`spec_tokens.check(O.registry(), spec) == []` を含む）、gate の `vectors` の項目と同じ命令の出力を前後で比べる。前後で `spec_tokens.spec_constants(gen.spec_text())` の集合を出して同じこと。
- `spans()`（`` `…` `` の素朴な正規表現）を `repo.code_spans` に寄せるのは、二重の backtick の扱いが違い集合が変わりうるので、この項目に入れない（材料として 6 章に書いた）。

### RF-18 (C1) 頭の欄の `status` の読み（保つ）

- `docs.Index` に `statuses(name)`（`{ID: status}`、頭の欄を一度だけ読む）を置き、`work_done` は `{w: s == "DONE"}`、`gap_marks.dropped_ids` は `{i for i, s in index.statuses("S").items() if s == "DROPPED"}` にする。
- `pending.load_docs` の `if not works: raise DocsError(...)` は、`index.ids("W")` を先に呼ぶ形にして `Index.ids` の文に任せる（`DocsError` は `repo.RepoError` の別名なので型は同じ。文は「tasks/W/: no file of an ID」で同じ）。
- 確かめ: gate-selftest、`gap_marks.py`・`pending.py check` の出力を前後で比べる。
- 注意: `gap_marks.py` は `rules/tools.md` 9.1 の形（`COMMANDS` と help）でない古い形の道具で、9.1 は「手を入れるときにこの形に合わせる」と言う。`dropped_ids` の一行を変えるだけでも形を合わせるかは親が決める（親への質問 2、返答に書いた）。

### RF-18 (C2) 段の並びの判断（変える、表に無い段だけ）

- `repo.stage_key(stage, stages)` を一つ置く: 表の順 → `PH2` → 表に無いもの（番号の順。`W3` は `W10` より前）。`pending.stage_counts`・`docs.py list --count` が使い、`due_key` は作業の番号を足すところだけ自分で持つ（`(stage_key, 番号)`）。
- 変わる出力: 表に無い段があるときの `pending.py check` の要約の行（`pending by stage: …`）の並び。例: 表に無い `W10` と `W3` の項目がある木で、今は `W10 1, W3 1`（文字列の順）、後は `W3 1, W10 1`（`docs.py list --count` と同じ番号の順。自己テスト 7232 行が固定している順）。
- 表に無い段は `docs.py check` (a) が誤りにするので、正しい木の出力は変わらない。テストの票を先に出すか、器の道具の境の差として親が了承するだけでよいかは親への質問 3（返答に書いた）。
- 行わない場合は、表の順の部分（`stages.index`）だけを共有しても重複は残るので、行うなら上の形を勧める。

### RF-18 (C3) `spec_sections.py` のテストの読み（変える、境だけ）

- `compiler_sources` の名前の規則（`tests.rs`・`*_tests.rs`）を `repo.is_test_file` に、`without_test_mods` を `repo.test_lines` の行を空けた本文に替え、自前の括弧の走査（`CHAR_LITERAL` を含む約 35 行）を消す。
- 判定の違い（今の木には無い形）: (1) `#[cfg(test)] mod t {` を一行に書いた形は、今は切り、後は切らない。(2) `#[cfg(test)]` と `mod t {` の間に別の属性かコメントの行がある形は、今は切らず、後は切る。(3) 今は本文だけ、後は属性の行と閉じ括弧の行も空ける（文字列が無いので結果は同じ）。
- 確かめ: `spec_sections.py --check` と `--list` の出力を前後で比べて同じ（今の木で差 0）。`rg -n "#\[cfg\(test\)\]\s*(pub )?mod" crates` が今は 0 件（コメントの中の 2 件だけ）であることを確かめた。
- `spec_sections.py` も 9.1 の古い形の道具（親への質問 2、返答に書いた）。

### RF-18 (C4) `builtin_names.py` のテストのファイルの名前（保つ）

- `builtin_names.is_test_file` を消し、`scan` で `repo.is_test_file` を使う。`crates/` の下では、`"tests"` のディレクトリ・`tests.rs`・`*_tests.rs` の判定が `NOT_CODE`（`crates/*/tests/*` の `*` は `/` も含む）と同じ。違うのは `crates/tests/…`（crate の名が `tests`）だけで、そのような crate は無い。
- `test_ranges`（`#[cfg(test)]` の下の `fn`・`static` なども除く）は `repo.test_lines`（`mod` だけ）と意味が違い、`onsa_syntax/src/groups.rs:521` などの `#[cfg(test)]` の `static` が数えに入ってしまうので、替えない。
- 確かめ: `builtin_names.py` の出力を前後で比べる。gate-selftest。9.1 の形は親への質問 2 と同じ。

### 大きいファイルの二つ（保つ）は 3 章に書いた。

## 3. 大きいファイル

### `crates/onsa_tests/src/run.rs`（1505 行、テスト込み 2433）

- 分ける（8.1 の観点）: 一つのファイルに、(1) 結果の型（`Problem`・`CaseRun` など、`ccheck`・`fix_contract`・`fixes` も使う）、(2) 一つの事例を回す処理、(3) 目印と fmt の比べ、(4) ビルドと host の列、(5) `test` ブロック、(6) 保留の一覧を当てる判断（`reconcile`）と要約、(7) 全ての事例を回す外枠と JSON が入っている。保留の一覧の規則を変える人（`reconcile`）が事例の回し方を読む必要が無く、名前が役割を表すように分けられる。
- 単位（`run/` のディレクトリのモジュール。公開の名前は `run/mod.rs` で `pub use` し、`crate::run::…` の道は変えない）:
  - `run/mod.rs`（約 450）: モジュールの doc、結果の型（`Stage`・`CheckedMarker`・`TestResult`・`Problem`・`CaseRun`・`Built`・`Stages`・`StageFailure`・`stage_problem`・`internal_problem`・`HostSteps`・`RunOptions`）、`run_case`、`run_case_with`。
  - `run/markers.rs`（約 200）: `compare`・`syntax_only`・`parser_markers`・`canonical`・`first_diff`・`negative_rules`・`lacks_found`。
  - `run/build.rs`（約 140）: `BuildCtx`・`build_target`・`conformance_scope`・`disk_files`・`run_hosts`・`host_not_run`。
  - `run/test_blocks.rs`（約 130）: `run_tests`・`panic_mismatch`・`full_name`・`pending_test`（名前は `tests` を避ける）。
  - `run/report.rs`（約 300）: `CaseReport`・`Report`（`failed`・`failures_text`・`summary`）・`reconcile`。
  - `run/all.rs`（約 160）: `run_all`・`run_all_with`・`fix_sources`・`run_each`・`runs_json`・`run_parallel`。
  - テスト（928 行）は `run/mod.rs` の `#[cfg(test)] mod tests;` から `run/tests.rs` に移す（テストの名前 `run::tests::…` は変わらない。`rg "run::tests"` で名指す所は無い）。
- 関数を分ける（移した後の別のコミット）:
  - `run_case_with`（259 行）を段ごとに: `setup_problems`（316-334 行の事例の形の誤り）、`read_markers`（338-363 行。`Markers { expected, testfails, panics }` を返す）、`marker_targets`（368-381 行）、`fmt_and_parser`（383-414 行）、`check_outputs`（437-490 行の候補の契約・`.fixK`・目印の比べ）、`analysis_outputs`（492-545 行の golden と `test`）。本体は約 60 行の並びにする。
  - `reconcile`（159 行）を: `unknown_entries`（事例も候補も名指さない項目）、`fix_entries_of(run)`（`fix-contract` の項目）、`whole_entry`（事例の全体の項目）、`named_entries`（`<path>::<name>` の test と host の列）に分ける。
- 上の項目と同じ所: 無い（S1 は `run.rs` に触らない。`parser_markers` の `per_unit` は行とコードを自分で並べるので S1 の外）。
- 確かめ: 移すコミットは `python3 -B tools/moved_only.py`（行を移しただけか）。関数を分けるコミットは `cargo test -p onsa_tests` と、`onsa_cases` の要約（`Report::summary`）と失敗の文を前後で比べて同じ。`refactor.py sizes` で前後を並べる。

### `crates/onsa_tests/src/fix_contract.rs`（1131 行、テスト込み 1500）

- 分ける（8.1 の観点）: 利用者が三つある。事例の実行器（`check`・`unchecked*`・`FixSpec` の読み）、fix_loop と fuzz の入口（`check_text`・`check_candidate`・`apply_alone`・`same_place`）、`.fixK` の写しと守り（`Moved`・`moved`・`shift`）。§18.1 の契約の 5 つの点（単位の対応、読みの比べ、最小の編集）がそれぞれ独立の判断で、doc の番号と同じ単位に分けられる。
- 単位（`fix_contract/`。公開の名前は `mod.rs` で `pub use`、`pub(crate)` の道も保つ）:
  - `fix_contract/mod.rs`（約 400）: モジュールの doc、`Checked`・`Files`・`target_name`・`check`・`unchecked_stage`・`unchecked`・`unchecked_in_parse`・`After`・`recheck`・`check_texts`・`judge`・`describe`。
  - `fix_contract/spec.rs`（約 150）: `[[test.fix]]` の項目（`FixSpec`・`RawSpec`・`de_specs`・`locate`・`Place`・`parse_leaf`・`check_specs`。`fragment.rs` が読む）。
  - `fix_contract/units.rs`（約 120）: 触る単位（S-302）: `meet`・`Moved`・`moved`・`shift`・`falls_in`・`Before`・`Correspondence`・`correspond`。
  - `fix_contract/reading.rs`（約 170）: 読みと最小の編集（点 4・5）と `same_code`: `Readings`・`blank`・`falling_in`・`edit_problems`・`not_minimal`・`reading_difference`・`reading_difference_in`・`code_shape`・`code_difference`・`same_code`。
  - `fix_contract/text.rs`（約 80）: 一つの本文の入口: `TextCheck`・`single_file`・`check_text`・`Unapplied`・`apply_alone`・`CandidateCheck`・`check_candidate`。
  - `fix_contract/same_place.rs`（約 170）: fuzz の近い「同じ場所」: `Violation`・`SamePlace`・`same_place`・`outer_form`・`in_same_place`・`found_before`。
  - テスト（369 行）は `fix_contract/tests.rs` へ。非公開の関数（`in_same_place`・`correspond`・`not_minimal` など）を読むので、子のモジュールの項目を `pub(super)` にする。
- 関数を分ける: `check` の候補ごとの本体（約 60 行）を `check_one(…)` に出す（`check` は約 98 行で基準の内なので任意）。
- 上の項目と同じ所: S1 (d) の `describe`（`mod.rs` に残る）。(d) を行うなら、移す前に済ませるか移した後に行う（同じコミットにしない。`moved_only.py` が使えなくなる）。
- 確かめ: `moved_only.py`、`cargo test -p onsa_tests`、`onsa_cases --fix-same-place` と fuzz の候補の確かめの出力を前後で比べる（W3-22/b の `cmp_sp.py` と同じ観点）。

## 4. 項目どうしの依存

- 同じファイル・同じ関数を触る組:
  - RF-18 (A) と (C2): `docs.py` の `due_key`・`list --count` と `pending.py` の段の関数。(A) を先に（出力を変えない）、(C2) を後に。
  - RF-18 (A)・(C1)・(C2) は `tools/test_gate.py` の自己テストを足すので、同じ担当にする（gate-selftest が一つ）。
  - RF-18 (C3)・(C4) は `spec_sections.py`・`builtin_names.py` だけで、(A)〜(C2) と独立。9.1 の形の決め方（親への質問 2）が要る。
  - RF-18 (B) は `tools/vectors/` だけで独立。
  - RF-10 S1 (a) → (b)・(d) の順（(b)・(d) は (a) の `printed_order` を使う）。(c) は doc だけでいつでも。
  - S1 (d) と `fix_contract.rs` の分け方は `describe` が重なる。分けるのを先にして (d) を後にするか、(d) を先にして別のコミットにする。
  - `run.rs` の分け方は他の項目と重ならない。
- 先に済ませたほうがよい順: (1) `run.rs`・`fix_contract.rs` の移すだけの整理（`moved_only.py` で確かめられる） → (2) S1 (a)(b)(c) → (3) 関数の分け方と S1 (d)。道具（RF-18）は crate と独立に並べてよい。
- 他の領域との境（気付いた重なり）: `onsa_diag/src/lib.rs`、`onsa_driver/src/reduce.rs`、`onsa_syntax/src/units.rs`（doc だけ）は他の領域の RF が触るかもしれない。親の手順 2 のグループ分けで確かめてほしい。

## 5. 材料の要点

- 指定の W3-22/b の報告（`094e8e7f…/scratchpad/w322b/handback_b.md`）は無かった。同じディレクトリに `notes.md`（8 行）だけがある。S1 の方針は RF-10 の本文と今のコードで判断した。
- 親が取り戻した報告（`44 回目の scratchpad の x6/materials/w322b/handback.md`）は W3-22/b の再確認（直しの往復 1）で、RF-10 の S1（表示の順が二つ）の節は無い（その中の「S1」は偽の検査の入力の番号、「S-2〜S-7」は前の指摘の番号）。S1 の方針に効く点は無く、方針は変えない。分けた後の確かめに使える点だけ: 「(1) の `--fix-same-place` の出力が旧バイナリと同じ（233 件）」「(2) `fix_contract::shift` の偽陽性は N-3（削除の点を囲む置き換え）だけ」。`shift` は `fix_contract/units.rs` へ移すだけで意味を変えない。
- `w322b/notes.md` の 1 行目: 「`order_check.py`: 候補を持つ最初・最後の診断が fix-loop の 1 歩目と一致（`tests/fuzz` と `tests/spec/fixes` で 466 回、外れ 0、誤りの数は `onsa check` と同じ）」。S1 (b) の確かめに同じ観点が使える。
- 同 2 行目: 「`cmp_sp.py`: `--fix-same-place` の前後が 233 + 320 ファイルで同じ」。`fix_contract.rs` を分けた後の確かめに同じ観点が使える。
- `w322i2/handback_fix2.md` の「判断の重複（D-15）」の行: 印をずらす処理は `fix_contract::shift` の一か所（fix_loop が使う）。分けた後も `shift` を一か所に保つ（`units.rs`）。
- RF-18 の出所: `issues/X/X-2.md` の 111-113 行（U7 の報告の範囲の外）。docs の 4 か所と `pending.stage_of`、`spec_tokens.py` の `split("|")`。今のコードでは `due_key` が 6 か所目。

## 6. 範囲の外で気付いたこと

1. `onsa_sema/src/rt.rs:268` の E0901 の一つの選び方が `span.start` だけで並べる（同じ始めの同順位は入力の順。`order_in_file` と違う）。表示の順ではなく sema の中の選び方なので S1 の外。
2. `onsa_diag/src/unsupported.rs:529` 付近に、Rust の `#[cfg(test)] mod` を読む自前の走査がある（`tools/repo.py` の `test_lines` と同じ判断の Rust の側）。RF-18 の外（Rust）。
3. `rules/tools.md` 9.1 の形（`COMMANDS` と help）でない `tools/*.py` が 20 ファイルある（部品のモジュールを含む）（`gap_marks`・`spec_sections`・`builtin_names`・`diag_codes`・`keywords`・`check_spec_examples`・`ignores`・`gate` など）。RF-18 の (C1)(C3)(C4) で触ると 9.1 の「手を入れるときに合わせる」が掛かる。
4. `tools/docs.py`（2305 行）と `tools/test_gate.py`（7991 行）は、`refactor.py sizes` が `crates/` の `.rs` だけを見るので一覧に出ない。道具の大きさの基準は無い。
5. `tools/vectors/spec_tokens.py` の `spans()` は `` `([^`\n]+)` `` の正規表現で、`repo.code_spans` と二重の backtick の扱いが違う。`section()` も見出しの字で切る（`spec_blocks.section_lines` は小節と fence を除くので代わりにならない）。
6. `docs.py:1638` の `id_key(g[0] + "-0")`（段の名を作業の ID の形にして番号で並べる）は (C2) の `repo.stage_key` で消える。

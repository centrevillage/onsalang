## 作業 X-1/U2 の報告

U2 は実装を終えました。自己テストは 230 件が通り、作業ツリーでの全体の gate も PASS です（626 秒）。いただいた答え（Q1〜Q5、ビルドの命令、主のツリーの導き方を一か所にする直し）は全て反映しました。

先にお伝えすることが二つあります。
- **作業ツリーの `--work W3-13` は FAIL で、絞られてもいません。** 理由は二つです。
  - FAIL の原因は私の書いた説明の文で、直した後の全体の gate では gap-marks も通りました。
  - この作業ツリーの差分は `tools/fuzz.py` と `tools/fmt_props.py` に触れるので、作業票の決まりどおり重い項目は全体で回りました（601 秒）。300 秒の目安との比較は、差分の無い写しで測りました（193 秒）。
- **最後の全体の gate の後に、`gate.py` を一度変えています。** 使い方の誤りの判定を一つの関数にまとめただけです。その後は自己テストと写しでの `--sweep` で確かめ、gate の全体は回し直していません。

- 状態: 作業ツリー `/Users/centrevillage/projects/onsalang/.claude/worktrees/agent-a369aedd884395619` の枝に WIP のコミットが並んでいる。未コミットの変更は無い。
  - `07d09cd` WIP: X-1 U1 (from the patch)
  - `815029e` WIP: X-1 U2
  - `ca1ee76` WIP: X-1 U2（gap-marks が印と読む語の直し）
  - `8552f84` WIP: X-1 U2（使い方の誤りの判定を一つの関数に）
- パッチ（U1 を含む全体）: `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/0ed8f9b9-db30-4d49-bb2b-cb3f68df27e6/scratchpad/x1/u2/u2_all.patch`
  - `take.py patch` の表示は「10 file(s), +1592 -88; without the tests and the data: +899 -85」。

### 見積もりと実際の行数（U1 の分とテストを除く。`git diff --numstat 07d09cd HEAD`）

| ファイル | 見積もり | 実際 |
|---|---|---|
| gate.py | 110〜140 | +215 −29 |
| gate_runs.py（新規） | 90〜120 | +160 |
| gate_steps.py | 35〜45 | +55 −14 |
| narrowing.py | 10〜15 | +23 −9 |
| repo.py | 12〜18 | +38 −1 |
| gap_marks.py | 15〜25 | +21 −9 |
| gate.sh | — | +2 −2 |
| 計 | 270〜360 | +514 −64（空行を除いた追加は 459） |

- 見積もりの約 1.3〜1.4 倍。§8.5 の基準（3 倍かつ差 100 行以上）の内です。
- 増えたのは主に `gate.py` で、`Form`、項目ごとの引数と飛ばし、要約の行、`_history`、説明の文の分です。
- `main` が長くなったので、使い方の誤りの判定を `_form_problem` に分けました（`8552f84`）。
- 自己テストは +386 行。

### 形ごとの表（実装したもの）

| 項目 | whole | stage-end | work | sweep | only |
|---|---|---|---|---|---|
| save-base | 出さない | 出さない | 出さない | 最初 | 挙げられない（`--save-base` を使う） |
| 静的な項目の組（9 項目） | 回す | 回す | 回す | 回す | 名前か `static` を挙げたとき |
| fuzz・fmt-props・fmt-comments・fmt-cst | 全体 | 全体 | `--changed-since auto --sample 0.1 --salt <最初の ID>`。道具の経路に触れたら全体 | `--shard k/K` | 挙げたとき（形は併用した引数のもの） |
| gate-selftest | 回す | 回す | `tools/` に触れたときだけ | 回す | 挙げたら条件無しで回す |
| その他 | 回す | 回す | 回す | 出さない | 挙げたとき |

- 最後の行は形で変わる: `gate (sweep k/K): …`、`gate (only): …`、`gate (quick): …`、それ以外は `gate: …`。
- 時間の警告は work と sweep の形だけで出し、最後の行のすぐ前に置く。
- 履歴は主のツリーで quick 以外の回に書く。要約の `sweep: next …` の行も主のツリーでだけ出す。

### したこと

- `tools/gate_steps.py`
  - 定数: `SAMPLE`、`SHARDS`、`BUDGET_WORK`、`BUDGET_SWEEP`、`BASES_KEPT`、`PARENT = 3`、`FUZZ_TOOLS`、`FMT_TOOLS`。`CODE_CAP` は置いていない。
  - `Step` に属性 `narrows`、`touches`、`static`、`sweep`、`sweep_only`、`parent` を足した。
  - `save-base` の項目（`STEPS` の先頭）と `static_names()` を足し、先頭の説明に形を書いた。
- `tools/gate.py`
  - 形の判定 `Form` と、項目ごとの扱い `_in_form`・`_narrowing`・`_skipped`。
  - 差分を読む `read_diff`。読めないときは絞れる項目を全体で回し、要約に `diff: cannot read it (…)` を出す。
  - 状態 `PARENT`、警告の `time_warning`、`_history`、`_form_problem`。
  - 引数 `--sweep`・`--only`・`--save-base`。`lock_path` は `repo.git_dirs` を使う形にした。
- `tools/gate_runs.py`（新規）
  - 履歴: `read_history`・`record`・`next_shard`・`sweep_line`。
  - 基の保存: `save_base`。ビルドは `fuzz.build` を二回呼ぶ。残す数の処理は「16 進 7 字の名前で `COMMIT` を持つ」ディレクトリだけを対象にする。
- `tools/repo.py`: `git_dirs`・`main_tree`・`tree_kind`。主のツリーの判断は全てここを通る。
- `tools/narrowing.py`
  - `EXCLUDED_FROM_CODES` に `tools/` を足した。
  - `under`（`pick` の `always` と gate が共有）、`base_dir`、`BASE_FILES` を足した。
  - `resolve_base` は `repo.main_tree` を使う形にした（直してほしい点）。U1 の自己テストは文面を変えずに通った。
- `tools/gap_marks.py`
  - `check` は `(problems, for_parent)` を返す。
  - 作業ツリーで、残るのが親の処理待ちだけなら終了 3 で、行は `parent: …` の形で出す。
  - 主のツリーと git でない根では、今のとおり終了 1。
- `tools/gate.sh`: 先頭のコメントの使い方を改めた。

### 主張と証拠

- 自己テスト: `python3 -B tools/test_gate.py` → `Ran 230 tests in 74.155s` / `OK`（U1 の後は 217 件）。新しいテスト:
  - 作業の検査の引数、経路に触れたら全体、gate-selftest の条件、whole と stage-end は今のまま: `GateForms.test_the_work_check_narrows_the_heavy_items`
  - 差分が読めないときの安全側: `GateForms.test_a_diff_that_cannot_be_read_runs_whole`
  - `--only`（`static`、併用した形、名前を挙げた gate-selftest、使い方の誤り）: `GateForms.test_only`
  - 次の k、落ちた回も数える、K を変えたら 0 から、読めない行の数、主のツリーだけ、併用の禁止: `GateForms.test_the_sweep`
  - 履歴（各形、quick と使い方の誤りでは書かない、dirty、作業ツリーでは書かない、書けない・読めないときは落とさない）: `GateForms.test_the_history`
  - 警告の位置と上位 3 つ、whole と `--only` では出さない、sweep の警告、錠の待ちを数えない: `GateForms.test_the_warning_of_the_time`
  - `PARENT` の状態: `GateForms.test_parent`
  - `PARENT` の 3 つの場合（作業ツリー、主のツリー、git でない根）と形の誤り: `GateForms.test_gap_marks_in_the_three_trees`
  - 基の保存（読む側の `resolve_base` が見つける、未コミットの変更で断る、未追跡と docs では断らない、残す数と他のディレクトリに触れない、主のツリーだけ、ビルドの失敗、`--save-base` は単独）: `SaveBase` の 4 件
  - 属性の突き合わせ（静的な組、`narrows` の経路が実在する、sweep の項目と save-base が先頭）: `RealSteps.test_the_forms_of_the_items`
  - `tools/` の診断コードを数えない: `Narrowing.test_changed_paths_and_codes`
- 作業ツリーの `tools/gate.sh --work W3-13`（`815029e`）: 601.0 秒で `gate: FAIL (gap-marks)`。
  - 原因は私が `gate_steps.py` の説明の文に書いた語 `spec gaps` が、印の形の誤りと読まれたこと（`tools/gate_steps.py:44: a malformed SPEC-GAP mark`）。`ca1ee76` で直し、`python3 -B tools/gap_marks.py` → `48 SPEC-GAP mark(s) …; all registered`。
  - 重い項目の行は `whole: the diff touches tools/fuzz.py` などで、作業票の決まりどおり全体で回った。gate-selftest も回った。
  - 警告の行も出た: `warning: the work check took 601s, 301s over its 300s; the longest: fmt-props 184.2s, fmt-comments 102.0s, fuzz 83.9s`
  - 作業ツリーなので履歴は書いていない。
- 絞った回の確かめ（作業票の受け入れ条件の代わり）
  - この作業ツリーの差分は道具の経路に触れるため、ここでは絞った形を見せられない。
  - そこで作業ツリーを scratchpad に `git clone` し、`dev` を HEAD に置いて（差分なし）回した。写しは確かめの後に消した。
  - `tools/gate.sh --only fuzz --work W3-13` → 23.8 秒、`gate (only): PASS`。fuzz の引数は `--changed-since auto --sample 0.1 --salt W3-13`、要約は `152 of 1422 seeds (diff 0, codes 0, sample 152)`。
  - `tools/gate.sh --work W3-13` → 192.7 秒、`gate: PASS`、警告なし。
    - fuzz 8.1 秒、fmt-props 37.1 秒、fmt-comments 19.0 秒、fmt-cst 7.4 秒（どれも narrowed）。
    - gate-selftest は SKIPPED（「the diff does not touch tools/」）。
    - 差分が空なので下限の値。W3-13 の大きさの差分での絞った回の値は、U1 の報告にある（fuzz 19 秒など）。
  - `tools/gate.sh --sweep`（`8552f84`）→ 315.9 秒、`gate (sweep 0/2): PASS`、600 秒の目安の内。
    - save-base は実際の cargo を使って `target/base/8552f84` に写し、`COMMIT` に完全な SHA を書いた。
    - 次の行が出た: `sweep: next 1/2 (0/2 last at 8552f84, 0 commits ago; 1/2 never)`
  - 写しの履歴の 3 行（`only fuzz`、`work W3-13`、`sweep 0/2`）: `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/0ed8f9b9-db30-4d49-bb2b-cb3f68df27e6/scratchpad/x1/u2/clone_history.jsonl`
- 全体の gate `tools/gate.sh`（作業ツリー、`ca1ee76`）→ 626.1 秒で `gate: PASS`。
  - 時間の大きい項目: fmt-props 197.7 秒、fmt-comments 106.0 秒、fuzz 99.8 秒、gate-selftest 74.4 秒、test 47.5 秒。
  - gap-marks は PASS。fuzz-deep は SKIPPED、fix-loop・golden・spec-coverage は INFO。golden は「no file differs from HEAD」。
- gate の出力: `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/0ed8f9b9-db30-4d49-bb2b-cb3f68df27e6/scratchpad/x1/u2/` の下の `gate_work/out`、`gate_whole/out`、`clone_only/out`、`clone_work/out`、`clone_sweep/out`。

### 自己点検（計画 §8.5）

| 種類 | 結果 |
|---|---|
| 何も走らずに通る | 飛ばすのは決まった条件だけで、理由を要約に出す（gate-selftest の「the diff does not touch tools/」）。差分が読めないときは多く回る側に倒す。`--only` の名前が空・不明なら終了 2 |
| 実装待ちの一覧で黙らせる範囲 | 変えていない。`PARENT` は gap-marks の終了 3 だけで、形の誤りと番号の形の誤りは落とす |
| 判断の重複（D-15） | 主のツリーは `repo.git_dirs` 一か所（`lock_path`、`resolve_base`、`tree_kind`）。経路の前方一致は `narrowing.under`。基の置き方は `base_dir`・`BASE_FILES`。値は `gate_steps` だけで、`CODE_CAP` の写しは無い（自己テストで確かめた） |
| 位置と黙った捨て方 | 履歴の読めない行は数を要約に出す。書けない・読めないときも要約に出す。差分が読めない理由も出す |
| この機械 | 偽のビルドと偽の項目は終了コードだけを使う。異常終了したプロセスは無い |
| 決定性と時間 | 次の k は履歴だけで決まる。git の呼び出しは timeout 60 秒。`--time-budget` は変えていない |
| 大きさ | 見積もり 270〜360 に対し実際は +514 −64（上の表）。基準の内 |

### 完了の定義（§8.3）

- 8（gate が通る）: 全体の gate は PASS（上のとおり）。
- 1〜7、9、10: 道具の作業なので当たらない。

### SPEC-GAP、仕様の空白、golden とテストベクトル

- 無し。

### 範囲の外で気付いたこと（直していない）

1. **分割の回でも fuzz が基を解決して表示する。** 例: `base unknown (no …/target/base/ca1ee76/COMMIT)`。分割の回は基を使わないので、表示が紛らわしいだけです（U1 の挙動）。
2. **`tools/fuzz.py`・`tools/fmt_props.py`・`tools/narrowing.py` に触れる作業は、作業の検査でも約 600 秒かかり、毎回警告が出る。** 決まり（手順 1 の A 期）どおりですが、道具の作業の後半で警告が続いても、それは仕様どおりです。
3. **`take.py patch` の表示「the main tree (8552f84b2) differs from 628f8ec」が、作業ツリーの HEAD を「main tree」と呼んでいる。** 中身は調べていません。

### 次の担当へ（U3 の文書に書くべき使い方）

- 担当の報告の前は `tools/gate.sh --work <ID>`（作業の検査）。
  - 重い 4 項目は差分の種と 1 割の抜き取りで回る。道具の経路に触れたら全体で回る。
  - gate-selftest は `tools/` に触れたときだけ回る。
  - 300 秒を超えたら、最後の行の前に `warning:` の行が出る。判定は落とさない。担当は報告に書く。
- 直しの往復では `tools/gate.sh --only <落ちた項目> --work <ID>`。
  - 最後の行は `gate (only): …` で、作業の判定ではない。
  - 静的な項目は `--only static` でまとめて呼べる（親が登録を写した後、M-4）。
- 親がコミットした後は、主のツリーで `tools/bg.py run … -- nice tools/gate.sh --sweep`。
  - 基の保存、静的な項目、gate-selftest、重い項目の次の分割（0 始まりで `0/2`、`1/2`）を回す。最後の行は `gate (sweep k/K): …`。
  - 作業ツリーでは終了 2。基の保存は、`crates/`・`tools/`・`std/`・`runtime/`・`Cargo.*` に追跡しているファイルの未コミットの変更があると FAIL（理由を出す）。
- 基だけを写すときは `tools/gate.sh --save-base`（主のツリーだけ。錠は取らない）。
- 主のツリーの回は `target/gate/history.jsonl` に 1 行を足し、要約に `sweep: next k/K (…)` を出す。担当の作業ツリーでは書かない。
- gap-marks の `PARENT`
  - 作業ツリーで `NEW` と表に無い番号だけが残るときに出る。判定は落とさない。
  - 主のツリーでは今のとおり FAIL なので、親はコミットの前に登録する。
- agent-rules 4 章の「判定は最後の `gate: PASS / FAIL` の行で見る」は、`gate (only)`・`gate (sweep …)` の形を足して直す必要がある（親の U3）。
- 最初に読むファイルと関数:
  - `tools/gate.py` の `Form`・`_in_form`・`_narrowing`・`_skipped`・`main`
  - `tools/gate_runs.py`
  - `tools/gate_steps.py` の先頭の説明と定数
- 決めていないこと: 無し。細部で決めたこと:
  - 作業ツリーでは `sweep:` の行を出さない。
  - 履歴の `items` には SKIPPED の項目も入れる（秒 0）。出さない項目は入れない。

### 引き継ぎの記録

- 文書だけでは足りず補ったこと
  - 作業票の 3 のビルドの命令は、親の答えに従い `fuzz.build` の二つの呼び出しにした。
  - この作業ツリーの差分は道具の経路に触れるので、受け入れ条件の `--only fuzz --work W3-13` を作業ツリーでは絞って見せられなかった。差分の無い写しで確かめた。
  - 作業ツリーの `--work W3-13` は FAIL（gap-marks）で終わった。直した後は全体の gate で通ることを確かめ、`--work` は回し直していない（作業ツリーでは全体と同じ回になるため）。
- 作業票との食い違い
  - 受け入れ条件の「`--only fuzz --work W3-13` が fuzz だけを絞って回す」は、道具の経路に触れたら全体で回す決まりと、この作業ツリーの差分の上では両立しない。
- 前の担当に聞きたかった問い
  - 分割の回でも基を解決するのは意図か（上の 1）。
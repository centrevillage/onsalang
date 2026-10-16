## 作業 X-1/U1 の報告

U1 は実装を終えました。判断を求めた点は A・B とも (b) で作り、自己テスト・実際の木の fuzz と fmt_props・全体の gate が通っています。

- 状態: 作業ツリーの枝に WIP のコミット `0935aef`（`WIP: X-1 U1`。その前は `fb5111a`）。未コミットの変更は無い。
- パッチ: `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/0ed8f9b9-db30-4d49-bb2b-cb3f68df27e6/scratchpad/x1/u1/u1.patch`
  - `take.py patch` の表示: 4 ファイル、+702 −30。テストとデータを除くと +394 −30。

### 見積もりと実際の行数（テストを除く）

| | 行 |
|---|---|
| 見積もり（設計メモ） | 220〜280 |
| 実際（+394 −30） | 約 364 |
| うち空行を除いた追加 | 340（`narrowing.py` 214、`fuzz.py`・`fmt_props.py` 126。説明の文 約 45 を含む） |

- 見積もりの約 1.3 倍。§8.5 の基準（3 倍かつ差 100 行以上）の内なので、リファクタリングはしていない。
- 増えた所は、`narrowing.py` の引数の検証と基の解決の分岐、それと説明の文。

### したこと

- `tools/narrowing.py`（新規）: 選び方の判断を一か所に置いた（D-15）。
  - 引数: `add_arguments`、`selection`、`parse`。
  - git を読む関数: `merge_base`、`changed_paths`、`diff_codes`。
  - 選び方: `pick`、`sampled`（最低 1 件は経路の先頭 3 段で数える。指示 A の (b)）、`in_shard`。
  - 基の解決: `resolve_base`。
  - 診断コードの種は、種の少ないコードから足し、上限を超える手前で止める（指示 B の (b)）。使わなかったコードは要約に書く。
  - `CODE_CAP = 200` はここに置いた。
- `tools/fuzz.py`:
  - `mutants`・`truncations`・`sweep` に引数 `only` を足した。
  - 回す入力を決める部分を `plan()` に切り出した。修正候補の段は、全体の回での番号（種の位置 × per_seed + k）で選ぶ。
  - 見分けは `base_shows()`。`run` に `selection`・`base` を足し、要約にも出す。
  - `--time-budget` の既定は変えていない。
- `tools/fmt_props.py`:
  - `sources` の全体を作った後で源を絞る。絞った回は `ALWAYS = ("tests/spec/fmt",)` を常に入れ、分割の回は入れない。
  - `--base` は持たない。`--time-budget` の既定は変えていない。
- `tools/test_gate.py`:
  - 新しい組 `Narrowing`（6 件）。
  - `Fuzz` に 7 件、`FmtProps` に 1 件を足した。

### 引数の形（U2 への受け渡し。設計メモの形から変えていない）

| 引数 | 使える道具 | 意味 |
|---|---|---|
| `--changed-since REV\|auto` | 両方 | 差分に関わる種と、診断コードの種を足す。`auto` は `git merge-base HEAD dev` |
| `--code-cap N` | 両方 | 診断コードの種の上限。既定は `narrowing.CODE_CAP`（200）。`--changed-since` と一緒のときだけ使える |
| `--sample F --salt ID` | 両方 | 抜き取り。二つは必ず一緒に渡す |
| `--shard I/K` | 両方 | 分割の回。他の選び方の引数とは同時に使えない |
| `--base auto\|none\|DIR` | fuzz だけ | 見分けに使う基のバイナリ。既定は `auto` |

- 使い方の誤りと、git が読めない場合は終了 2。全体の回には倒さない。
- 選び方の引数が無ければ、今と同じ全体の回になる。

### 部分集合と見分け: 確かめたこと

- 実際の木での部分集合の確かめ:
  - 再現: `python3 -B P32/x1/u1/subset_real.py <作業ツリー>`
  - 選び方は `--changed-since 6e26c4c --sample 0.1 --salt X-1`。
  - 結果:
    ```
    picked 341
    mutants 3410 subset True
    truncations 682 subset True
    fix stage 862 of 3555 subset True
    fix stage = whole's of the picked seeds True
    ```
- 全体の回の選び方は変わっていない: 引数無しの fuzz の要約は `14220 mutants ... 3555 mutants through the fix stage`（advisor の数と同じ）。
- 本物の基のバイナリでの見分け:
  - 再現: `python3 -B P32/x1/u1/base_real.py <作業ツリー> P32/x1/u1`
  - `resolve_base(..., "auto")` は `Base(commit='628f8ec', onsa=('/Users/centrevillage/projects/onsalang/target/base/628f8ec/onsa',), ...)` を返した。
  - 許可の一覧の 3 つの入力で、基は `(True, None)`（同じ類と判定）を返した。残った診断の文面だけ変えた類では `(False, None)`。
- 自己テスト `python3 -B tools/test_gate.py` → `Ran 217 tests ... OK`。主なもの:
  - 部分集合: `Fuzz.test_a_narrowed_plan_is_a_part_of_the_whole`
  - 前からの類は落とさない: `Fuzz.test_a_class_the_base_shows_does_not_fail_a_narrowed_run`
  - 基で出ない類は落とす（違反なし・文面が違う・残ったコードが違う・基の道具が失敗）: `Fuzz.test_a_class_the_base_does_not_show_fails`
  - 内部エラーは前からでも落とす: `Fuzz.test_a_crash_from_before_fails`
  - 基が不明・`none`・全体の回・分割の回は落とし、印を付ける: `Fuzz.test_an_unknown_base_and_whole_runs_fail`
  - 絞った回の種と、保存した入力の全体の再生: `Fuzz.test_a_narrowed_run_mutates_the_picked_seeds_only`
  - 引数の誤りが終了 2: `Fuzz.test_main_passes_the_narrowing`、`Narrowing.test_selection`
  - 変えた・未追跡・日本語の名前のファイルと、`tests/`・`docs/` の除外、未追跡のファイルのコード: `Narrowing.test_changed_paths_and_codes`
  - 少ないコードから足して上限で止め、使わなかったコードを書く: `Narrowing.test_pick`
  - 同じ塩で同じ集合、先頭 3 段ごとに最低 1 件: `Narrowing.test_sample`
  - 分割の和が全体で、互いに素: `Narrowing.test_shards_partition_the_whole`
  - 基の解決（作業ツリーから主の `target/base` を見つける、`COMMIT` の先頭一致、ファイルの欠け、実行できない、`dev` が無い、git の木でない）: `Narrowing.test_resolve_base`
  - fmt_props の絞った回・分割の回・全体の回: `FmtProps.test_a_narrowed_run`

### 実際の木の時間（作業ツリー、10 コア、一つずつ順に回した）

絞った回の引数は `--changed-since 6e26c4c --sample 0.1 --salt X-1 --code-cap 200`。

| 項目 | 回 | 選んだ種 | 入力 | 時間 |
|---|---|---|---|---|
| fuzz | 絞った | 341 / 1422（差分 36、コード 157、抜き取り 148） | 変異体 3,410、切り詰め 682、修正候補の段 862 | 19.0 s |
| fuzz | 全体 | 1422 | 変異体 14,220、切り詰め 2,844、修正候補の段 3,555 | 85.6 s |
| fmt core | 絞った | 342 / 1103（差分 36、コード 150、常に 45、抜き取り 111） | 2,125 | 39.7 s |
| fmt core | 全体 | 1103 | 8,049 | 161.0 s |
| fmt comments | 絞った | 342 | 2,125 | 18.8 s |
| fmt comments | 全体 | 1103 | 8,049 | 97.2 s |
| fmt cst | 絞った | 342 | 4,790 | 12.5 s |
| fmt cst | 全体 | 1103 | 14,918 | 33.3 s |

- 4 項目の和は、全体で 377 秒、絞った回で 90 秒。
- どの回も新しい類は 0。fuzz の要約は両方とも `base 628f8ec: 0 pre-existing`。
- 使わなかった診断コード: `E0002 E0020 E0200`。
- 異常終了したプロセスは無い。

### gate（`tools/gate.sh`、`--work` 無しの全体、579 秒）

- `gate: PASS`。
- 時間の大きい項目:

| 項目 | 時間 |
|---|---|
| fmt-props | 179.0 s |
| fmt-comments | 100.8 s |
| fuzz | 82.7 s |
| gate-selftest | 67.8 s |
| test | 51.1 s |

- 残りの項目も全て PASS。fuzz-deep は SKIPPED、fix-loop・golden・spec-coverage は INFO。
- golden: HEAD と違うファイルは無い。

### 自己点検（計画 §8.5）

| 種類 | 結果 |
|---|---|
| 何も走らずに通る | fmt_props は 0 件なら今の「no source ran」で落ちる。fuzz は 0 件でも保存した入力の再生がある。git が読めない・基が不明なときは安全側（終了 2、全て落とす）に倒す |
| 実装待ちの一覧で黙らせる範囲 | 黙らせるのは、絞った回で基が同じ類と文面を出した修正候補の類だけ。内部エラー・異常終了・時間切れは基で回さず落とす |
| 判断の重複 | 選び方・merge-base・基の解決は `narrowing.py` だけに置いた。`CODE_CAP` も一か所 |
| 位置と黙った捨て方 | 基で判定できない理由は ` (the base cannot tell: …)`、基が不明な理由は要約に出す。未追跡で中身が文字でないファイルはコードを持たないとして飛ばす（自己テストあり） |
| この機械 | 偽のバイナリは終了コードと既にある SIGKILL だけを使う。新しい異常終了は作っていない |
| 決定性と時間 | 抜き取りと分割は sha256 で決まる。基での回しは `min(TIMEOUT, 残りの予算)`。git の呼び出しは timeout 60 秒 |
| 大きさ | 見積もり 220〜280 に対し実際は約 364（上の表） |

### 完了の定義（§8.3）

- 自己テストと gate が通った（8.3 の 8）。
- 1〜7、9、10 は道具の作業なので当たらない。

### SPEC-GAP、仕様の空白、golden とテストベクトル

- 無し。

### 範囲の外で気付いたこと（直していない）

1. **`tools/` の下の自己テストのファイルの診断コードも、コードの差分として数える。** `tools/test_gate.py` などは本文に多くの `E\d{4}` を持つので、道具を変えた作業ではコードの種が膨らむ。
   - 上の表の絞った回は、私の `tools/` の差分（`test_gate.py` の足した行の E0005・E0007 など）を含んで数えている。そのためコードの種の数は、W3-13 だけの差分で設計メモに書いた値（402 件で上限を超えた）と違う。
   - 除く範囲に `tools/test_*.py` を足すかは、親か U2 の判断。
2. **fmt_props の絞った回は源の 31%（342 / 1103）になる。** 主な理由はコードの種 150 件。そのうち多くは構文の否定例で、core と comments では fmt が読まないものとして飛ばす（195 件）ので、時間への効きは小さい。

### 次の担当へ（U2）

- 最初に読むもの: `tools/narrowing.py`（説明の文に引数の意味が全てある）、`fuzz.run` の見分けの所、`fuzz.plan`。
- 作業の検査の呼び方: `tools/fuzz.py --changed-since auto --sample <gate_steps の割合> --salt <作業 ID>`。fmt_props も同じ（`--base` は無い）。`--code-cap` は既定で `narrowing.CODE_CAP` を使う。
- 網羅の検査の呼び方: `--shard k/K`。分割の回は前からの類でも落とし、`tests/spec/fmt` を常に入れることもしない。
- 前からの類の行は `pre-existing (the base <7 字> shows it): fix-same-place: <類> (seed …, …)` の形で固定した（落とす行ではないので `FAIL` は付かない）。
- fuzz の要約の末尾の基の表示:
  - `; base <commit>: N pre-existing`
  - `; base unknown (<理由>)`
  - `--base none` のときは何も出さない。
- 基のディレクトリの名前は完全な SHA の先頭 7 字で固定。`COMMIT` には完全な SHA を書くこと（読む側は、7 字以上の先頭一致なら受ける）。
- `--changed-since auto` は git の木でない根（作り物の根）では終了 2 になる。gate の自己テストの根では渡さないこと。
- 道具の側の残り: 無し。gate と文書の側（`--sweep`、`--only`、M-8 など）は U2 と U3。

ファイル（作業ツリーの中）:
- `/Users/centrevillage/projects/onsalang/.claude/worktrees/agent-a34581bb13d0dc9f1/tools/narrowing.py`
- `/Users/centrevillage/projects/onsalang/.claude/worktrees/agent-a34581bb13d0dc9f1/tools/fuzz.py`
- `/Users/centrevillage/projects/onsalang/.claude/worktrees/agent-a34581bb13d0dc9f1/tools/fmt_props.py`
- `/Users/centrevillage/projects/onsalang/.claude/worktrees/agent-a34581bb13d0dc9f1/tools/test_gate.py`

確かめのスクリプト（`P32/x1/u1/` の下）:
- `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/0ed8f9b9-db30-4d49-bb2b-cb3f68df27e6/scratchpad/x1/u1/subset_real.py`
- `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/0ed8f9b9-db30-4d49-bb2b-cb3f68df27e6/scratchpad/x1/u1/base_real.py`
- `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/0ed8f9b9-db30-4d49-bb2b-cb3f68df27e6/scratchpad/x1/u1/count.py`
- `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/0ed8f9b9-db30-4d49-bb2b-cb3f68df27e6/scratchpad/x1/u1/count2.py`

gate の出力: `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/0ed8f9b9-db30-4d49-bb2b-cb3f68df27e6/scratchpad/x1/u1/gate/out`
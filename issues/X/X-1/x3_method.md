# X-1 の U3・U4 の方法（X-3 の実績の後、39 回目、2026-10-18）

材料は `effect_x3.md`。どちらも利用者が了承した（2026-10-18）。U3 → U4 の順に、別の単位で入れる。

## U3（X1-1）: W の外の単位の作業の検査と、取り込みでの確かめ

- `--work` が W の外の単位の ID（`X-3/U1` の形: 改善の項目の ID と単位）も受ける。実装待ちの項目の `until` との照合は W の ID のときだけ行い、絞りの salt と形は同じに使う。打ち間違いを拾うため、項目の ID が `issues/X/` にあることは確かめる（形は設計メモで担当が決める）。
- 作業ツリーの gate も最後の回を控える（形、判定、HEAD、その時の木の hash。作業ツリーの `target/gate/`）。今は主のツリーだけが履歴を書く（`tools/gate.py` の `_history`）。
- `take.py patch` が、作業ツリーの最後の回を要約に出し、「基 = 主のツリーの HEAD、そのまま当たる、最後の形が `--work` で PASS、その後に木が変わっていない」なら「回し直し不要」と一行で示す（M-4 の条件を道具が示す）。そうでなければ、どれが欠けるか（作業の検査が無い / `--quick` だけ / 検査の後に変わった / 基が違う）を示す。
- 見積もり: コード 45〜80 行、自己テスト 30〜50 行。
- 実装（`7352d01`）: 基が主のツリーの HEAD と違っても、その差がコードと事例（`narrowing.SWEPT`）の外だけなら、重い項目を回し直さず `--only static` を示す（`take.py patch --help`。`rules/process.md` 8.5 の回し直しの条件に合わせた）。

## U4（X1-2）: コミットを合図に網羅の検査と基を起こす

利用者の採用（2026-10-18、39 回目）: git の post-commit フックを手当て付きで。advisor のレビュー（`adv/handback_x3_review2.md`）を入れた第 2 版を、利用者が了承した。

### 形

```
git commit（親、主のツリー）
  └─ tools/hooks/post-commit（追跡する。core.hooksPath = tools/hooks）
       └─ python3 -B <木の最上位>/tools/after_commit.py   … すぐ返る（1 秒未満）
            ├─ 作業ツリー / 重くないコミット / hold → 何もしない（状態に控える）
            └─ 依頼を書き、走り役の錠が空いていれば bg.py で起こす（環境から GIT_* を外す）
                 └─ after_commit.py --drive（nice、裏、錠 target/gate/auto/lock を持つ）
                      ├─ 静かな間（180 秒）を待つ
                      ├─ 未コミットのコード・事例があれば、clean になるまで 60 秒ごとに最大 60 分待つ
                      ├─ tools/gate.sh --sweep（gate の錠を取る。基の保存を含む）
                      ├─ 出力を target/gate/auto/runs/ に写す
                      └─ 走っている間に新しい依頼が来ていれば、最新の HEAD でもう一度
```

### 手当てと仕組み

| 手当て | 仕組み | 置き場所 |
|---|---|---|
| 文書だけのコミットでは回さない | `git diff-tree -r --no-commit-id --name-only HEAD` が `narrowing.BUILT_FROM` か `tests/` に触れるときだけ依頼を書く（`-r` と `--no-commit-id` が無いと、1 行目にコミットの SHA が混ざる） | `after_commit.py` |
| 文書だけのコミットでも基が見つかる | `resolve_base` が merge base の基が無いとき、first-parent を 50 までさかのぼり、`git diff --quiet <祖先> <merge base> -- BUILT_FROM`（累積の差）が空の一番近い祖先の基を使う | `narrowing.py` の `resolve_base` |
| 基の入力の抜け | `BUILT_FROM` に `rust-toolchain.toml` を足す（toolchain の更新はバイナリを変える） | `narrowing.py` |
| 走り役は一つ | 走り役が `target/gate/auto/lock` に `flock(LOCK_EX \| LOCK_NB)` を取る（gate の `one_gate` と同じ手。プロセスが死ねば外れ、再起動でも残らない）。フックは同じ錠を試し、取れたら放して起こす。取れなければ依頼を書くだけ。PID の生死では見ない（再起動の後の PID の再利用で、黙って止まる） | `after_commit.py` |
| 続けたコミットは 1 回にまとめる | 依頼は一つのファイル（`target/gate/auto/request`: 時刻と HEAD、tmp + replace で書く）。走り役は最後の依頼から 180 秒たってから、その時の HEAD で回す | 同上 |
| 走っている間のコミット | 回し終えたとき、依頼の時刻が回し始めより後なら、最新の HEAD でもう一度。待つのは最大 1 回分 | 同上 |
| 止めたいとき | `target/gate/hold` があれば依頼を控えるだけで回さない | 同上 |
| 親が全体を回した後 | 主のツリーの全体の回（whole / stage-end）も、コードに未コミットの変更が無ければ終わりに基を保存する（今は sweep と `--save-base` だけが保存する）。履歴に同じ HEAD の全体の回が依頼より後にあれば、その依頼は済み。`sweep_line` は全体の回を全ての shard を回した回として数える | `gate.py`、`gate_runs.py` の `_sweeps` |
| 未コミットのコード・事例 | 回す前に `code_changes` と `tests/` の差を見る。あれば clean になるまで 60 秒ごとに最大 60 分待ち、なお dirty なら回さずに状態を「skipped: uncommitted <経路>」にする（dirty の木では回さない。その HEAD で回したことにならないため）。`--now` で手で起こせる | `after_commit.py` |
| 走っている間に木が変わる | 回す前と後で、一時の索引（`GIT_INDEX_FILE=<一時>` で `read-tree HEAD`、`add -A -- BUILT_FROM tests`、`write-tree`）で木の hash を取って比べ、違えば履歴に「tree changed during the run」と書いて、その shard を済みにしない。本物の索引は触らない | `gate.py` の sweep |
| 作業ツリーでは何もしない | `repo.tree_kind(root) != "main"` なら即座に 0 で返る（担当の WIP のコミット）。基がフックより前の作業ツリーでは、フックのファイルが無く、何も走らない（エラーも出ない） | `after_commit.py` |
| フックの環境 | post-commit は `GIT_INDEX_FILE`（主のツリーでは相対の `.git/index`）、作業ツリーでは `GIT_DIR` も入れる。`after_commit.py` は始めに `GIT_` で始まる環境変数を全て外し、その環境で走り役を起こす | 同上 |
| 機械の負荷 | 走り役は `nice -n 10`。担当の gate は錠で最大 1 回分（約 5〜6 分）待つ（今と同じ）。担当の `cargo` との重なりは縛らない（W4 の初めの数で sweep の秒を見る） | 同上 |
| 止まったこと・落ちたことに気付く | 主のツリーの gate の要約と `take.py patch` の頭に、常に一行 `auto sweep: <状態>` を出す。状態は「last PASS at <commit> (<n> commits ago)」「FAILED at <commit>: <項目> (<出力の経路>)」「requested at <commit> <時刻>, no runner」「waiting (quiet until …)」「skipped at <commit>: uncommitted <経路>」「held since …」。走り役とフックが `target/gate/auto/state`（小さな JSON、tmp + replace）に書く | `gate_runs.py`、`gate.py`、`take.py` |
| 手で起こす | `after_commit.py --now`: 残った依頼を今すぐ処理する（hold は無視しない）。再起動の後、hold を外した後、skipped の後に使う | `after_commit.py` |
| 出力が消えない | `bg.py run` は起こすたびに `out` を消すので、走り役は回し終えたら `out` を `target/gate/auto/runs/<時刻>-<HEAD の先頭 7>.out` に写し、最後の 10 個を残す | `after_commit.py` |
| 基を消す隙 | `BASES_KEPT` を 5 から 8 にする（1 個約 43 MB、計約 350 MB）。担当の絞ったファズが使っている基を、主の sweep の刈り込みが消す隙を狭める | `gate_steps.py` |

### フックを入れること

- `tools/hooks/post-commit`（数行の sh: `exec python3 -B "$(git rev-parse --show-toplevel)/tools/after_commit.py"`。post-commit の終了コードは git が無視するので、失敗してもコミットは止まらない）。
- `git config core.hooksPath tools/hooks` は利用者が打つ（設定の変更）。今の `.git/hooks` に有効なフックは無い（sample だけ）。相対の経路は、フックが走るツリーの最上位から解かれる（advisor が git 2.53.0 で確かめた）。
- 入れた直後に `tools/gate.sh --save-base` を 1 回（フックの前の HEAD の基）。
- post-commit が走るのは `commit`・`--amend`・`cherry-pick`・`rebase`（コミットごと）。`merge` では走らない（親は使わない）。

### 見積もり

- コード 220〜290 行、自己テスト 100〜130 行（advisor の見積もり。手当ての直しの分が約 100〜120 行乗った）。道具の単位の目安（16〜30 万トークン）の上の方。
- X1-1 とは別の単位にし、X1-1 → X1-2 の順にする（X1-1 は約 40〜70 行で短く、先に入れば次の X の単位から `--work` が使える。触るファイルは重なるが場所が違う）。同じ担当に U1（X1-1）→ U2（X1-2）と続けさせ、U1 の WIP の後に一度報告させる。

### 規則の文（道具が入った後）

- 利用者が了承して直した（2026-10-18、`06f7a6f`）。下の案のうち規則に入れなかった所（前からの類の FAILED が出続けること、`target/fuzz/new/`、登録だけのコミット）は、`tools/after_commit.py` の help に足す（X-9 の方針、39 回目の文書の点検）。
- `rules/process.md` 8.5 の「網羅の検査」と `rules/leader.md` 4 章: 「コミットがフックで網羅の検査を起こす。親は `auto sweep:` の行を区切りで見て、FAILED なら `runs/` の出力と `target/fuzz/new/` を読み、4.5 の形で仕分ける。前からの類で FAILED が区切りまで出続けるのは設計どおり。全体を自分で回す前と、続けて大きく変えるときは `target/gate/hold`、外した後は `--now`。」
- `tests/pending.toml`・`tests/fuzz/allowed.toml` だけのコミットも網羅の検査を起こす（登録の後に FAILED が消えるのを確かめる役に立つ）。

### 確かめ方（W4 の初めの数に足す）

- コード・事例のコミットの数に対する自動の網羅の検査の回数、skipped と hold の回数、「base unknown」の回数（0 に近いこと）、段の終わり以外に親が全体を回した回数、sweep の秒（担当のビルドとの重なり）。

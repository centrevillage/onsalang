# X-1/U2 の設計メモ（gate の側）

- 状態: 作業ツリー `agent-a369aedd884395619`、dev `628f8ec` の上に `07d09cd WIP: X-1 U1 (from the patch)`（`take.py apply` は plain で当たった）。
- 実現する決定: `step3_measures.md` の M-2、M-4（道具の側）、M-5、M-6、M-7、M-8 と、作業票の「する」の 1〜8。
- 判断を求める点は、最後の「決めてほしいこと」に Q1〜Q5 として並べた。

## 1. 置き場所

| ファイル | 置くもの |
|---|---|
| `tools/gate_steps.py` | 定数（割合、K、時間の目安、基を残す数、`PARENT` の終了コード）、`Step` の新しい属性、`save-base` の項目 |
| `tools/gate.py` | 形（whole / stage-end / work / sweep / only / quick）の判定、項目ごとの引数と飛ばし、`PARENT` の状態、要約の警告と sweep の行、`--save-base` の入口 |
| `tools/gate_runs.py`（新規） | 履歴（足す、読む、次の k、sweep の行）と、基のバイナリの保存。`gate.py` を膨らませないために分ける |
| `tools/narrowing.py` | `EXCLUDED_FROM_CODES` に `tools/`。経路の前方一致 `under(path, dirs)` を切り出し、`pick` の `always` と gate の「経路に触れたか」が使う。基の置き方 `base_dir(main, full)`・`BASE_FILES` を切り出し、読む側と写す側が使う |
| `tools/repo.py` | `git_dirs(root)`（根が git の木の頂上なら `(git-dir, common-dir)`、でなければ None）と `tree_kind(root)`（`"main"` / `"worktree"` / None）。`gate.lock_path`・履歴・`--sweep`・`gap_marks` が使う |
| `tools/gap_marks.py` | 問題を二つに分け、作業ツリーでは親の処理待ちを終了 3 で返す |

- 主のツリーかの判断は `repo.tree_kind` 一か所。`gate.lock_path` の頂上の確かめと共通の部分も `repo.git_dirs` に寄せる（挙動は変えない）。
- `narrowing.resolve_base` の主のツリーの見つけ方（common-dir の親）は変えない（U1 の自己テストの文面を保つ）。写す側は主のツリーでだけ動くので、根そのものを使い、`base_dir` だけを共有する。

## 2. `gate_steps.py` の定数と属性

```python
SAMPLE = 0.1            # 作業の検査の抜き取りの割合（M-1）
SHARDS = 2              # 網羅の検査の分割の数 K（M-2）
BUDGET_WORK = 300       # 秒。作業の検査の目安（M-8）
BUDGET_SWEEP = 600      # 秒。網羅の検査の 1 回の目安
BASES_KEPT = 5          # 残す基のバイナリの数（M-3）
PARENT = 3              # 「親の処理待ち」の終了コード（M-5）。CANNOT_RUN（2）とも 1 とも違う
```

- `CODE_CAP` は置かない。gate は `--code-cap` を渡さず、道具が既定の `narrowing.CODE_CAP` を使う（値は一か所）。説明の文で `narrowing.CODE_CAP` を指す。
- `Step` の新しい属性:

| 属性 | 意味 | 付ける項目 |
|---|---|---|
| `narrows: tuple = ()` | 絞れる項目と、その道具の経路。差分がこの経路に触れたら作業の検査でも全体で回す | fuzz: `("tools/fuzz.py", "tools/narrowing.py")`。fmt-props・fmt-comments・fmt-cst: `("tools/fmt_props.py", "tools/narrowing.py")` |
| `touches: tuple = ()` | 作業の検査では、差分がこの経路に触れるときだけ回す | gate-selftest: `("tools/",)` |
| `static: bool = False` | 静的な項目の組。網羅の検査に毎回入り、`--only static` で呼べる | pending、ignores、gap-marks、diag-registry、diag-negatives、builtin-names、spec-examples、spec-sections、default-inits |
| `sweep: bool = False` | 網羅の検査に入る（`static` と `narrows` の項目は付けなくても入る） | gate-selftest、save-base |
| `sweep_only: bool = False` | 網羅の検査でだけ回る。他の形では一覧にも出さない | save-base |
| `parent: bool = False` | 終了 `PARENT` を「親の処理待ち」の状態 `PARENT` として読む | gap-marks |

- 新しい項目 `Step("save-base", (*PY, gate.py, "--save-base"), sweep=True, sweep_only=True, slow=True)` を `STEPS` の先頭に置く（網羅の検査で最初に回るように）。
  - 子のプロセスにすると、出力・秒・終了コードが他の項目と同じ扱いになり、単独の `--save-base` と同じコードになる。
  - `--save-base` は `--golden` と同じく錠を取らない（網羅の検査が錠を持ったまま子として呼ぶため。ビルドは cargo の錠が並べる）。
- `static_names()`（`static` の項目の名前）を足す。`--only static` の展開と自己テストの突き合わせに使う。

## 3. 形ごとの項目と引数

形の決め方（`gate.py` の `Form`）:

| 引数 | 形 | 履歴の `form` |
|---|---|---|
| 無し | whole | `whole` |
| `--stage-end S`（`--work` があっても） | stage-end | `stage-end S` |
| `--work ID...` | work | `work ID[,ID...]` |
| `--sweep` | sweep | `sweep k/K` |
| `--only a,b`（`--work`・`--stage-end` と併用可） | only（引数は併用した形のもの） | `only a,b` |
| `--quick` | quick（今のまま） | 書かない |

- `--sweep` は他の引数と併用できない（終了 2）。`--only` は `--quick`・`--sweep` と併用できない（終了 2）。`--save-base` は単独だけ（終了 2）。
- `--only` の名前は項目の名前か `static`。知らない名前は終了 2（知っている名前を並べる）。

項目ごと（「全体」は今と同じ引数）:

| 項目 | whole | stage-end | work | sweep | only |
|---|---|---|---|---|---|
| save-base | 出さない | 出さない | 出さない | 最初に回す | 挙げられない（`--save-base` を使う） |
| 静的な項目の組（9 項目） | 回す | 回す | 回す | 回す | 挙げたとき（`static` で全て） |
| fuzz、fmt-props、fmt-comments、fmt-cst | 全体 | 全体 | `--changed-since auto --sample 0.1 --salt <最初の ID>`。差分が `narrows` に触れたら全体 | `--shard k/K` | 挙げたとき。引数は併用した形のもの |
| gate-selftest | 回す | 回す | 差分が `tools/` に触れたときだけ（他は SKIPPED「the diff does not touch tools/」） | 回す | 挙げたら条件無しで回す（Q3） |
| fuzz-deep | SKIPPED | 回す | SKIPPED | 出さない | 挙げても `--stage-end` が無ければ SKIPPED（今の規則） |
| 他（fmt、clippy、test、fix-loop、vectors 類、ignored-files、keywords、C、golden、spec-coverage） | 回す | 回す | 回す | 出さない | 挙げたとき |

- 実装待ちの一覧に全体で載る項目の飛ばし（`_skipped`）と `--quick` の飛ばしは、どの形でも今のまま当てる。
- 「出さない」は要約の行にも出さない（網羅の検査の要約を短く保つ）。「SKIPPED」は理由付きで要約に出す。
- 要約の各行に、絞った回の印を足す: `narrowed (sample 0.1, salt W3-13)`、`whole: the diff touches tools/fuzz.py`、`shard 1/2`。`Result` に `note` を足して `describe` の前に出す。

## 4. 差分の経路の取り方

- 作業の検査（と `--work` 付きの `--only`）で、回す項目に `narrows` か `touches` を持つものがあるときだけ、gate の始めに一度読む:
  `since = narrowing.merge_base(root)`、`changed = narrowing.changed_paths(root, since)`（道具の `--changed-since auto` と同じ関数。未追跡のファイルと未コミットの変更を含む）。
- 触れたかは `narrowing.under(path, dirs)`（`path == d` か `path` が `d/` で始まる）。`pick` の `always` の前方一致もこれに替え、判断を一か所にする。
- 差分を読めないとき（git の木でない、`dev` が無い）は安全側に倒す: 絞れる項目は全体で回し、`touches` の項目も回す。要約に `diff: cannot read it (<理由>); the narrowable items run whole` を出す。
  - 道具に `--changed-since auto` を渡すと道具の側が終了 2 になるので、渡さない方を選んだ。判定は落とさない（何も走らずに通ることは無く、多く回るだけ）。
- 塩は最初の `--work` の ID（作業票のとおり）。merge-base は道具の側でも一度ずつ求めるが、同じ木の同じ HEAD なので同じ値になる。

## 5. `--sweep` の次の k

- 主のツリーでだけ回せる: `repo.tree_kind(root) == "main"` でなければ終了 2（`--sweep runs only in the main tree (a worktree / not a git work tree)`）。
- 履歴 `target/gate/history.jsonl` の `form` が `sweep i/K` の行のうち、K が今の `SHARDS` と同じ最後の行の i を取り、次は `(i + 1) % K`。無ければ 0。
  - K を変えた後は、違う K の行を読まないので 0 から一巡し直す。
  - 落ちた回も数える（分割は回った。仕分けは親が区切りで行う）。途中で止めた回は行を書かないので、同じ k をもう一度回す。
- 分割の番号は `--shard` と同じ 0 始まり（`0/2`、`1/2`）で、表示と履歴も同じ番号にする（Q1）。
- 要約の一行（主のツリーで回したどの形でも出す）:
  `  sweep: next 1/2 (0/2 last at 628f8ec, 3 commits ago; 1/2 never)`
  - 何コミット前かは `git rev-list --count <SHA>..HEAD`。HEAD の祖先でなければ `not an ancestor of HEAD`。
  - 読めない行（JSON でない）は飛ばし、数をこの行に `; 2 unreadable lines in the history` と書く（黙って捨てない）。

## 6. 基のバイナリの保存（`--save-base`、網羅の検査の最初の項目）

`gate_runs.save_base(root, keep, build=fuzz.build, target_directory=fuzz.target_directory)`（自己テストはビルドを偽物に替える）:

1. `repo.tree_kind(root) == "main"` でなければ終了 2（担当の作業ツリーは主のリポジトリに書かない）。
2. `git diff HEAD --name-only -- crates tools std runtime ':(glob)Cargo.*'` が空でなければ断る（終了 1、変わったファイルを並べる）。追跡しているファイルの未コミットの変更だけを見る（作業票のとおり。未追跡のファイルは見ない）。
3. `fuzz.build(root)` と `fuzz.build(root, cases=True)`（fuzz と同じ二つの cargo の呼び出し）。
   作業票の一つの呼び出し `cargo build -q -p onsa_cli -p onsa_tests --bin onsa_cases` は、`--bin` が対象を `onsa_cases` に絞るので `onsa` を作らないはず（未確認。実装の始めに確かめる）。fuzz と同じ呼び方なら確か。
4. `fuzz.target_directory(root)/debug/{onsa,onsa_cases}` を、`target/base/.tmp-<pid>/` に写し、`COMMIT` に HEAD の完全な SHA を書き、`narrowing.base_dir(root, sha)`（`target/base/<先頭 7 字>`）へ名前を替える。同じ名前があれば消して置き換える（途中で止まっても読む側が半端な基を見ない）。
5. 残す数: `target/base/` の下の、名前が 16 進 7 字で `COMMIT` を持つディレクトリだけを数え、`COMMIT` の更新時刻の古いものから、`BASES_KEPT` を超える分を消す。それ以外のものには触れない。
- 出力: `save-base: target/base/628f8ec (628f8ec05e…); kept 5, removed 1c2d3e4`。失敗の理由（ビルド、写し）は終了 1。

## 7. 履歴の行

主のツリー（`tree_kind == "main"`）で、quick 以外の形（使い方の誤りを除く）の gate 1 回につき 1 行を、錠を持ったまま要約の後に足す:

```json
{"time": "2026-10-16T21:04:05+0900", "commit": "<HEAD の完全な SHA>", "dirty": false,
 "form": "sweep 1/2", "works": [], "verdict": "PASS", "seconds": 371.2,
 "items": {"save-base": ["PASS", 31.0], "fuzz": ["PASS", 52.4], "gap-marks": ["PARENT", 0.4]}}
```

- `dirty` は `git status --porcelain` が空でないこと（未追跡のファイルを含む。道具は未追跡のファイルも種に入れるため）。
- `items` は回した項目と SKIPPED の項目（秒は 0）。出さない項目は書かない。
- `seconds` は項目の秒の和（錠の待ちを含まない。警告と同じ数）。
- 作業ツリーと git でない根では書かない。書けない（ディレクトリが作れない）ときは要約に `history: cannot write (<理由>)` を出し、判定は落とさない（Q5）。
- 絞った種の数（step3 の M-8 の案）は、道具の出力を読み直すことになるので入れない（作業票の 5 に無い）。

## 8. 時間の警告（M-8）

- 形が work と sweep のときだけ（`--only` 付きは除く）。和は回した項目の `Result.seconds` の和。錠は `one_gate` が `run_steps` の前に待つので、和に入らない。
- 目安を超えたら、最後の行のすぐ前に:
  `warning: the work check took 512s, 212s over its 300s; the longest: fmt-props 179.0s, fmt-comments 100.8s, fuzz 82.7s`
  （網羅の検査は `the sweep took …s, …s over its 600s`）。判定は落とさない。
- `--time-budget` は変えない。

## 9. `PARENT`（gap-marks、M-5）

- `gap_marks.check(marks, known)` を `(problems, for_parent)` を返す形に変える。
  - `for_parent`: `NEW` と「表に無い番号」（S / R / A の形で表に無い）。
  - `problems`: 印の形の誤り、S / R / A の形でない番号（担当が直せる）。
- `main`: `repo.tree_kind(root) == "worktree"` のときだけ `for_parent` を分ける。
  - 主のツリーと None（git でない根、自己テストの作り物の根）では、今のとおり両方を問題として落とす（終了 1）。
  - 作業ツリーで `problems` が空で `for_parent` があれば終了 `gate_steps.PARENT`（3）。行は `parent: <経路>:<行>: …` の形で出し、最後の行は `N mark(s) …; M for the parent to register`。
  - `problems` があれば終了 1（`for_parent` も並べる）。
- gate: `Result.status` は、`step.parent` で終了が `PARENT` なら `PARENT`（落とさない）。`describe` は `waits for the parent (see gap-marks)`。`info` の `INFO` とは別の名前。
- 実装待ちの一覧の扱いとは交わらない（gap-marks は pendable でない）。

## 10. 見積もり（テストを除く。説明の文を含む）

| ファイル | 行 |
|---|---|
| `gate_steps.py`（定数、属性、save-base、説明の文） | 35〜45 |
| `gate.py`（引数と検証、`Form`、項目ごとの引数と飛ばし、差分、`PARENT`、要約の三つの行、履歴の呼び出し、説明の文） | 110〜140 |
| `gate_runs.py`（履歴、次の k、sweep の行、基の保存） | 90〜120 |
| `narrowing.py`（除外、`under`、`base_dir`・`BASE_FILES`） | 10〜15 |
| `repo.py`（`git_dirs`、`tree_kind`） | 12〜18 |
| `gap_marks.py` | 15〜25 |
| 計 | 270〜360 |

- step3 の見積もり（U2 で 120〜180）の約 2 倍。増えた所は、基の保存（step3 では親の手作業の扱い）と `--only`・`PARENT` の配線と説明の文。
- §8.5 の単位の目安（約 300 行）の上の端に掛かる。分けるなら、U2a（作業の検査の引数、gate-selftest の条件、`--only`、`PARENT`、`EXCLUDED_FROM_CODES`。約 150 行）と U2b（`--sweep`、基の保存、履歴、警告。約 170 行）に切れる。私は分けずに続けられる見込み（文脈は今 約 9 万）。
- 自己テストは 150〜200 行の見込み（作業票の 8 の各場合。git の木は `Narrowing` の `git_in` と同じ作り方、ビルドは偽物、異常終了は作らない）。

## 11. 決めてほしいこと

- Q1 分割の番号: `--shard` に合わせて 0 始まり（`sweep 0/2`、`1/2`）で表示と履歴を揃える（推す）か、表示だけ 1 始まりにするか。step3 の例は「次は 2/2」で 1 始まりに読める。
- Q2 最後の行: `--sweep` と `--only` は作業の判定でないので、`--quick` に倣い `gate (sweep 1/2): PASS`・`gate (only): FAIL (fuzz)` にする（推す）か、`gate: PASS / FAIL` のままにするか。作業票の 4 は「`gate: PASS / FAIL` の行のすぐ前」と書くので、推す案では「最後の行のすぐ前」と読む。
- Q3 `--only gate-selftest --work ID` で差分が `tools/` に触れないとき: 名前を挙げたので回す（推す）か、作業の検査と同じく SKIPPED にするか。
- Q4 差分を読めないときの作業の検査: 安全側（全体で回す、`touches` の項目も回す。推す）か、使い方の誤り（終了 2）にするか。
- Q5 履歴が書けないとき: 判定を落とさずに要約に出す（推す）か、落とすか。
- 確かめ: 作業票の 3 の cargo の一つの呼び出しを fuzz と同じ二つの呼び出しに替える（上の 6 の 3）。

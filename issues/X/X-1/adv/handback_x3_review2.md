# X1-2 の方法の案（`P39/x1/design_x1_2.md`）のレビュー

確かめは、道具の読み（`tools/gate.py`・`gate_runs.py`・`narrowing.py`・`bg.py`・`repo.py`・`fuzz.py`）と、scratchpad の使い捨てのリポジトリでの git の実験（git 2.53.0。スクリプトは `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/d0a3bab9-5639-49ba-ae7b-a3c1e6029c6f/scratchpad/x1/adv/hooktest/run.py` と `full.py`、結果のリポジトリは同じ下の `repo/`）。
gate・`cargo test`・ファズは回していない。

## 1. git のフックの挙動

**1-1 post-commit の環境: 直す（環境から `GIT_*` を外す）。確信: 高。**
- 実験: 主のツリーで `git commit` → フックの cwd はツリーの最上位、`GIT_DIR` は未設定、**`GIT_INDEX_FILE=.git/index`（相対）** が入る。サブディレクトリからのコミットでは `GIT_PREFIX=sub/` も入る。作業ツリーでは `GIT_DIR` と `GIT_INDEX_FILE` が絶対の経路（`…/main/.git/worktrees/<名>`）で入る。
- 継いだときの害（実験）: `GIT_DIR`（主の `.git`）を継いだ子が別の cwd で `git rev-parse --show-toplevel` を呼ぶと cwd を返し、作業ツリーで `git status` を呼ぶと主の索引と比べて偽の削除が並ぶ。`bg.py` で起こす走り役はフックの環境をそのまま継ぐので、`gate.sh` の中の git（`repo.git_dirs`、`narrowing.git`、`golden_changes`）が cwd を変える場面で誤る余地がある。
- 形: `after_commit.py` の始めに `GIT_DIR`・`GIT_INDEX_FILE`・`GIT_WORK_TREE`・`GIT_PREFIX`・`GIT_COMMON_DIR` を `os.environ` から外し、`bg.py run` にはその環境を渡す（3〜5 行）。

**1-2 `core.hooksPath` の相対の経路: このままでよい（注記を足す）。確信: 高。**
- 実験: 相対の `tools/hooks` は、フックが走るツリーの最上位から解かれる。主のツリーは主の `tools/hooks/post-commit`、作業ツリーは自分の `tools/hooks/post-commit` を使う。
- フックのコミットより前を基にした作業ツリー（ファイルが無い）: フックは走らず、エラーも出ず、コミットは成功する（終了コード 0）。作業ツリーでは何もしない設計なので害は無い。注記: 作業ツリーのフックは `after_commit.py` が無い木では動かないが、それでよい、と docstring に一行。

**1-3 どの操作で走るか: このままでよい（案の前提は正しい）。確信: 高。**
- 実験: `git commit`、`--amend`、`cherry-pick`、`rebase`（再生したコミットごとに 1 回ずつ、2 回確かめた）で走る。`git merge`（ff でも非 ff でも）では走らない（post-merge の領分）。親の `git reset --soft` の後の作り直し（`rules/leader.md` 3.5）は `commit` なので走り、依頼は最新の HEAD で上書きされる。

**1-4 `git diff-tree --name-only HEAD`: 直す。確信: 高。**
- 実験: `-r` と `--no-commit-id` が無いと、1 行目にコミットの SHA が出て、ディレクトリは最上位しか出ない（`tools` だけ）。`BUILT_FROM` と `tests/` の判定なら最上位で足りるが、SHA の行が「触れた経路」に混ざる。
  形: `git diff-tree -r --no-commit-id --name-only HEAD`（または `git diff --name-only HEAD~ HEAD`。根のコミットは無視でよい）。マージのコミットは `-m` 無しでは空になるが、1-3 のとおり post-commit はマージで走らないので関係ない。

## 2. 競合と停止

**2-1 走り役が一つであること: 直す（flock で縛る）。確信: 高。**
- 案は `bg.py` の固定のディレクトリで「生きていれば起こさない」とする。`bg.run` は `going(d)`（`os.kill(pid, 0)`）で見る（`bg.py` 71〜75 行、118〜121 行）ので、(a) 二つのフックが同時に `going` を見てから書くまでの隙に二つ起きうる（同じ秒の二度のコミットは親が直列なので現実には薄い）、(b) **再起動の後に PID が別のプロセスに再利用されると `going` が真のまま**になり、新しい走り役が二度と起きない（黙って止まる形）。
- 形: 走り役が `target/gate/auto/lock` に `fcntl.flock(LOCK_EX | LOCK_NB)` を取る（`gate.py` の `one_gate` と同じ手。プロセスが死ねば系が外し、再起動でも残らない）。フックは同じ錠を `LOCK_NB` で試し、取れたら走り役は居ない → 錠を放し、`job/` のファイルを消してから `bg.py run`。取れなければ依頼を書くだけ。約 15 行。

**2-2 依頼のファイル: このままでよい（書き方だけ）。確信: 高。**
- 一つのファイルに時刻と HEAD、最新が勝つ、でよい。書くのは `bg.write` と同じ tmp + `replace`（原子的）。同じ秒の二度のコミットは、後の HEAD が残り、走り役は 180 秒の静けさの後に `git rev-parse HEAD` を見直すので、依頼の HEAD は参考の値でよい（走る対象は常に今の HEAD）。

**2-3 止まったことに気付く形: 足す。確信: 高。**
- 案の「落ちたことに気付く」は FAIL のときだけ。黙って止まる経路が三つある: 走り役が落ちた・再起動（依頼は残り、次のコミットまで何も起きない）、hold の置き忘れ（案にある）、「未コミットのコード・事例があれば見送る」が続く場合（下の 3-3）。
- 形: 主のツリーの gate の要約と `take.py patch` の頭に、常に一行 `auto sweep: <状態>` を出す。
  状態は「last PASS at <commit> (<n> commits ago)」「FAILED at <commit>: <項目>」「requested at <commit> <時刻>, no runner」「waiting (quiet until …)」「skipped at <commit>: uncommitted <経路>」「held since …」。
  走り役の状態は `target/gate/auto/state`（走り役と フックが tmp + replace で書く小さな JSON）から読む。`gate_runs.py` に 20〜30 行（案の 20〜30 行の中に収まる見込み）。
- 手で起こす入口 `after_commit.py --now`（hold を無視せず、残った依頼を今すぐ処理）も足す（5〜10 行）。再起動の後と hold を外した後に使う。

**2-4 走り役の出力が消える: 足す。確信: 高。**
- `bg.run` は起こすたびに `cmd`・`out`・`exit` を消す（`bg.py` 122〜124 行）。FAIL の `job/out` は次の走り役が起きた時点で消え、要約の「FAILED at …」だけが残る。ファズの最小化した入力は `target/fuzz/new/<ハッシュ>.onsa` に内容の名で残る（`fuzz.py` 799〜804 行。消されない）が、どの類か（`signature`・`left`）は `out` にしかない。
- 形: 走り役が回し終えたら `job/out` を `target/gate/auto/runs/<時刻>-<HEAD の先頭 7>.out` に写し、最後の 10 個を残す（5〜10 行）。要約の FAILED の行はその経路を指す。

**2-5 gate の錠と順: このままでよい（一言足す）。確信: 中。**
- 走り役の `--sweep` は `one_gate` の錠を取るので、担当の gate と親の全体の gate は後ろで待つ（最大 1 回分。今の見積もりは分割 1 つで約 5〜6 分）。順は先に錠を取った者で、優先は付けられない（flock）。
- 錠は gate 同士しか縛らず、担当の `cargo build/test` との重なりは縛らない（X-3 の 875 秒の回と同じ）。`nice -n 10` は CPU の取り合いにだけ効く。180 秒の静けさの後は、親が次の担当を起こしてビルドが始まる時刻と重なりやすい。これは受け入れて、W4 の初めの数に「sweep の秒」を足して見る（既に `history.jsonl` にある）。

## 3. 正しさ

**3-1 `resolve_base` の祖先へのさかのぼり: 正しい。条件の書き方を一つ直す。確信: 高。**
- 基の意味は「merge base のソースから作ったバイナリ」。祖先 A と merge base M の間で `BUILT_FROM` に差が無ければ、同じソースなのでバイナリは同じ（ビルドが決定的で、`BUILT_FROM` がビルドの入力を全て含む前提）。
  条件は「各段で差が無い」でなく、`git diff --quiet A M -- <BUILT_FROM>` を一発で見る（累積の差。`narrowing.git` で `diff --name-only`、空なら採用）。first-parent を 50 までさかのぼるのは十分（コードのコミットの間に文書のコミットが 50 続くことは無い）。
- **`BUILT_FROM` に `rust-toolchain.toml` が無い**（`narrowing.py` 45 行: `crates`, `tools`, `std`, `runtime`, `:(glob)Cargo.*`。`rust-toolchain.toml` は追跡されている）。toolchain の更新はバイナリを変える。1 行足す。
- `BASES_KEPT = 5` の刈り込み（`gate_runs._prune`、`COMMIT` の mtime の古い順）との整合: 基はコードのコミットの sweep でだけ保存され、文書のコミットは消費しない。よって 5 個 = 最近 5 つのコードのコミットで、さかのぼりの対象（コードの差が無い祖先）は必ず最後の基の後ろにある。合う。
- 刈り込みの隙: 担当の作業ツリーの絞ったファズが基のバイナリを実行している間に、主の sweep の `_prune` がその基を消すと、`base_shows` が途中で失敗する（merge base が 6 つ以上前のコードのコミットのときだけ。今の `target/base` は 5 個で 217 MB、1 個約 43 MB）。起きにくいが、`BASES_KEPT` を 8〜10 にしても約 400 MB で済む。値は親の判断。

**3-2 回す前と後の木の hash の比べ: 足りる（取り方を決める）。確信: 中。**
- fuzz は種（`seeds(root)`、`fuzz.py` 363 行）とバイナリ（`fuzz.build`）を回の始めに読み・作り、fmt の性質も始めに読む。途中で変わりうるのは、親がパッチを当てて `cargo build`/`cargo test` を直接回し `target/debug/onsa` が差し替わる場合。前後の比べで「tree changed」と記し、その shard を済みにしない、でよい。
- 取り方: 索引を触らずに木を作る。`GIT_INDEX_FILE=<一時ファイル>` で `git read-tree HEAD`、`git add -A -- <BUILT_FROM> tests`、`git write-tree`（実験で確かめた: 一時の索引で書いても本物の索引は変わらない）。追跡外のファイルも含むので、`status --porcelain` の文字列より確か。
  約 10 行。`git stash create` は使わない（`rules/common.md` 1.4）。

**3-3 「同じ HEAD の全体の回があれば済み」と「未コミットなら見送る」: 直す。確信: 高。**
- 全体の回（whole / stage-end）は**基を保存しない**（`save_base` は `--sweep` と `--save-base` だけ。`gate.py` 391 行、`gate_steps` の sweep の形）。この規則で依頼を済みにすると、その HEAD の基が無いまま次の担当の絞ったファズが「base unknown」になる。
  形: 主のツリーの全体の回も、`code_changes` が空なら終わりに `save_base` を呼ぶ（`gate.py` の `_history` の近くに 3〜5 行。ビルド済みなので写すだけ）。こうすれば「済み」の規則は正しい。
- 「未コミットのコード・事例があれば見送り、次のコミットを待つ」は、親の主のツリーが長く dirty な運用（パッチを当ててレビューに 1 時間）で飢える。180 秒の静けさの間に次のパッチが当たると、次のコミットまで何も回らず、依頼だけが残る。
  形: (a) フックの時点（コミット直後はふつう clean）で `code_changes` と `tests/` の差を見て、clean ならその事実を依頼に書く。(b) 走り役は、回す前に dirty なら、最大 30 分（60 秒ごと）clean を待ってから、なお dirty なら **回す**（履歴の `dirty: true` が付く。見つけた類の帰属は後で基で絞れる）。
  ただし `save_base` は断る（今の `save_base` のまま）。見送りを続けると「黙って止まる」側に倒れるので、回す側に倒す。2-3 の状態の行に「ran dirty」を出す。
- `sweep_line`（`gate_runs.py` 105〜125 行）は `sweep k/K` の行しか見ないので、全体の回の後も「last at … n commits ago」が古いまま。全体の回は全 shard を済みとして数える（`_sweeps` に whole / stage-end の行を全 shard として足す。5 行）。

## 4. 代わりの形との比べ（短く）

| 形 | 利用者の設定 | 親が忘れうるか | 利用者自身のコミット | 備考 |
|---|---|---|---|---|
| git の post-commit（案） | `git config core.hooksPath tools/hooks` 1 回（リポジトリの `.git/config`） | 忘れられない | 拾う | フックのファイルは追跡。作業ツリーは早期に返る（1-2） |
| Claude Code の `PostToolUse`（Bash の `git commit` に一致） | `.claude/settings.json` | 一致の文字列次第（`tools/commit.py` 経由や複合コマンドで外れる） | 拾わない | 道具の呼び方に依存し、縛りとして弱い |
| `tools/commit.py` の包み | 無し（または `PreToolUse` で素の `git commit` を拒む設定） | 忘れうる（規則の文で縛る形に戻る） | 拾わない | X-9 の「git の命令を道具にする」には合うが、合図の確かさは post-commit に劣る |

結論: 案（post-commit）のままでよい。`commit.py` は、後で枝の整理（X-9 の候補）と一緒に作るとき、同じフックの上に載せればよい。確信: 高。

## 5. 抜け

- 5-1 落ちた後の仕分けの流れ: 要約の「FAILED」から、`target/gate/auto/runs/<…>.out`（2-4）と `target/fuzz/new/` を読み、`rules/leader.md` 4.5 の形で仕分け、登録の後に `--only fuzz` か次の sweep で消える、という一連を規則の文に書く（親の作業。道具は 2-3・2-4 で揃う）。
  前からの類で sweep は FAIL し続ける（shard は基と比べない。`fuzz.py` の docstring「A whole run and a shard fail as it does」）ので、FAILED の行が区切りまで出続けるのは設計どおりと注記する。
- 5-2 入れた直後: フックの前の HEAD には基が無い。入れるときに `tools/gate.sh --save-base` を 1 回（規則の文か、票の受け入れ条件に）。
- 5-3 ディスク: `target/base` は 1 個約 43 MB × `BASES_KEPT`（3-1）。`runs/` の出力は 10 個で数 MB。`target/debug` の警告は今のまま。問題なし。
- 5-4 段の終わりとの関係: `--stage-end` を clean な HEAD で回してから文書のコミットをする順なら、フックは依頼を書かない（文書だけ）。全体の回が基を保存する（3-3）ので、段の終わりの後の担当も基を持つ。
- 5-5 `tests/pending.toml`・`tests/fuzz/allowed.toml` だけのコミットも `tests/` に触れるので sweep が走る。登録のコミット（R の許可の一覧）の直後に走るのは、FAILED が消えるのを確かめる役に立つので、むしろよい。注記だけ。
- 5-6 フックの sh は `python3 -B "$(git rev-parse --show-toplevel)/tools/after_commit.py"` のように自分の木の経路で呼ぶ（cwd は最上位だが、`GIT_PREFIX` が付く場合の相対の経路の読み違いを避ける）。

## 6. 見積もりと X1-1 との単位

- 見積もり: 案のコード 120〜170 行に、この報告の直し（1-1 環境 5、2-1 flock 15、2-3 状態の行と `--now` 30〜40、2-4 出力の保存 10、3-1 条件と `rust-toolchain.toml` 5、3-2 木の hash 10、3-3 全体の回の `save_base` と dirty の待ち 20、`_sweeps` 5）で約 100〜120 行が乗り、**コード 220〜290 行、自己テスト 100〜130 行**（状態の行、flock、dirty の待ち、全体の回の基の保存の事例が増える）。
  道具の単位の目安（`rules/process.md` 8.5、16〜30 万トークン）の上の方だが中に収まる。確信: 中。
- X1-1 と一つの単位にするか: 触るファイルは重なる（`gate.py`、`take.py`、`test_gate.py`）が、場所は違う（X1-1 は `gate.py` 411〜414 行の `--work` の照合と 438 行の履歴の条件、`take.py` の `patch` の要約。X1-2 は `gate.py` の sweep の終わりと要約、`take.py` の頭）。
  衝突は軽い。ただし X1-2 だけで単位の上の方なので、**別の単位にして X1-1 → X1-2 の順**を推す（X1-1 は約 40〜70 行で短く、先に入れば次の X の単位から `--work` が使え、作業ツリーの履歴が X1-2 の「auto sweep」の行と同じ `history.jsonl` の読み方に乗る）。
  一つにするなら、担当 1 体で U1（X1-1）→ U2（X1-2）と続け、U1 の WIP の後に報告させる。確信: 中。

## 全体

**直してから実装の票にする。** 作り直しは要らない。必ず直すのは、1-1（`GIT_*` を外す）、1-4（`diff-tree -r --no-commit-id`）、2-1（flock。再起動の後に黙って止まる形を塞ぐ）、2-3・2-4（止まったこと・落ちたことが見える形と出力の保存）、3-3（全体の回も基を保存する。dirty のときは待ってから回す）。
足すとよいのは 3-1 の `rust-toolchain.toml`、3-2 の木の取り方、5-2 の入れた直後の `--save-base`。

主なファイル:
- `/Users/centrevillage/projects/onsalang/tools/gate_runs.py`（`save_base` 130〜170 行、`_prune`、`_sweeps`・`sweep_line` 90〜125 行）
- `/Users/centrevillage/projects/onsalang/tools/narrowing.py`（`BUILT_FROM` 45 行、`resolve_base` 196〜224 行、`code_changes` 227 行）
- `/Users/centrevillage/projects/onsalang/tools/bg.py`（`going`・`run` 71〜75 行、118〜131 行）
- `/Users/centrevillage/projects/onsalang/tools/gate.py`（`lock_path`・`one_gate` 249〜276 行、`--sweep`・`_history` 420〜457 行）
- 実験: `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/d0a3bab9-5639-49ba-ae7b-a3c1e6029c6f/scratchpad/x1/adv/hooktest/run.py`、`full.py`
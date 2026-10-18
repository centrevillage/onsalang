# 規則の文を道具とフックに合わせる（X-9 の残り、X9-8 の棚卸しと一緒に）: 直す箇所の一覧

基: dev `b17dfb0`。探した範囲: `rules/`、`.claude/agents/`、`README.md`、`CLAUDE.md` の、道具・git・`python3` を書いた行（約 76 行）。
形: 規則には時機と道具だけを書き、使い方は道具の help に置く（`rules/tools.md` 9.3）。設定やフックが止めるものは、禁止の文を消して代わりの手だけを残す（40 回目の `0b2f871` の前例。番号は詰めない）。

## 群 1: 作業ツリーの手順（`work.py` に置き換わる）

| ID | 所 | 今 | 直す向き |
|---|---|---|---|
| N-1 | `common.md` 2.1 | 始めに `git log -1` で確かめ、違えば `git merge --ff-only dev` | 「始めに `work.py sync`」の一文に |
| N-2 | `common.md` 2.2 | WIP を置いて `git merge dev`、衝突を解く | 「`work.py sync` を回す。衝突で止まったら解いてコミット」に。WIP を残してよい、は残す |
| N-3 | `common.md` 2.4 の二段目 | 親が `take.py patch`、担当が `take.py apply` で当てて WIP | 「担当は `work.py sync --apply <パッチ>`」に。一段目（報告の前の WIP）は今のまま（下の K-3） |
| N-4 | 定義 onsa-impl・onsa-test | 先に `git merge --ff-only dev` | 「先に `work.py sync`」に（定義は利用者が直す） |
| N-5 | `leader.md` 2.10 の「状態の基」 | 枝・WIP・`take.py patch` のパッチ、担当は `take.py apply` | パッチは `work.py patch`、担当は `work.py sync --apply` |
| N-6 | `leader.md` 3.2 | `take.py` の patch → check → apply の 3 段、`--to`・`--main` の説明 | 「`work.py take <名前>` で写す。止まったら check を読み `--go`」に。読み方は help へ |
| N-7 | `leader.md` 3.3 | 基のコミットの選び方、取り込ませるときの WIP と merge | 基は `take` が merge-base で決める。取り込ませるときは `work.py sync` |
| N-8 | `leader.md` 3.5 | `take.py apply` が索引から外す、`git commit <パス>`、`reset --soft` | 「親のコミットは `work.py commit` で、名指した経路だけ」に |
| N-9 | `leader.md` 3.6 | 消す前に写ったかと報告の保存を確かめる | 「写した後は `work.py done`、区切りは `work.py close`（道具が確かめる）」に |
| N-10 | `process.md` 8.6（124・126 行） | `take.py patch` の `work check:`・`auto sweep:` の行 | `work.py take` の行、読み方は `work.py help patch` |
| N-23 | `process.md` 8.6 の並べ方 | 親が写して作業ツリーを消す、実装の作業ツリーは 3-way で当てる（W1-07） | 「写すのは `take`、消すのは `done`」。3-way の文は消す（check が決める）（advisor で足した） |
| N-24 | `leader.md` 1.2 | 区切りの手順に作業ツリーの片付けが無い | 区切りの手に `work.py close`（3.6 を指す一言）（advisor で足した） |

## 群 2: フックが受け持った規則

| ID | 所 | 今 | 直す向き |
|---|---|---|---|
| N-11 | `leader.md` 1.1 | 定義の一覧、`git log`・`status`・`worktree list` を確かめる | 「フックの状態の要約を記憶と突き合わせる」に。scratchpad の成果の確かめと、Agent の一覧に定義が全て読み込まれたかの確かめ（フックはファイル名を出すだけ）は残す（advisor で直した） |
| N-12 | `leader.md` 2.2 | `model` を渡さない | 禁止を消し「`subagent_type` で呼ぶ」だけを残す（フックが止める） |
| N-13 | `leader.md` 2.6・2.9 | 報告を jsonl からスクリプトで保存（`handback.py save`）、返事を scratchpad に控える | 報告はフックが `handback/` に、SendMessage は `messages/` に控える。`handback.py save` はフックが保存していない分（前のセッション、`hooks/errors.log` に失敗があるとき）（advisor で直した）。報告の名前のファイルを書かせない、は残す |
| N-14 | `leader.md` 3.1 | 担当の作業ツリーに `cd` しない | 禁止を消し、`git -C` と絶対パス、道具には引数で、を残す |
| N-15 | `checks.md` 4.1 と `common.md` 1.8 | Bash の timeout を 600000 に | timeout の部分を消す（フックが直す）。回し直す・`wait` を繰り返す、は残す |
| N-16 | `checks.md` 4.2 | fuzz の `--deep` は回さない | 消す（フックが止める。番号は詰めない） |

## 群 3: help への指しと `python3 -B` の名残（40 回目の文書の点検の F7・F8）

| ID | 所 | 今 | 直す向き |
|---|---|---|---|
| N-17 | `common.md` 1 章（新しい行） | 規則から `help --role` を指す所が無い（F7） | 「道具の使い方は `<道具> help --role <役割>`」の一行を足す（全員が読む所） |
| N-18 | `documents.md` 5.3 | `python3 -B`、「表の列の数も見る」、swaps の括弧の注意 | `-B` を外す。列の数は `check` が見るので消す。swaps の注意は help の時機と同じ文なので縮める。`\|\|` の書き方は help に無いので残す（advisor で足した） |
| N-19 | `process.md` 8.1、`README.md` 34 行、定義 onsa-docs 12 行 | `python3 -B tools/docs.py …` | `-B` を外す（設定の `env` が入れている。定義は利用者） |
| N-20 | 定義 onsa-docs 13 行 | `show`・`path`・`back` の使い方 | 「`show` で読む。他は `docs.py help --role docs`」に（利用者） |
| N-21 | `leader.md` 4.10、`process.md` 8.6（154 行） | trailer を手で書く、`docs.py set … status=DONE` | `work.py commit --docs-checked`・`--done` に |
| N-25 | `leader.md` 5.6 | `graph <ID> --back`・`changes --section <§>` | B-1 の答えに従う（命令の名までにするなら引数を消す）（advisor で足した） |

## 群 4: コミットの分け方と題（X-9 の決定で X9-8 に回したもの）

| ID | 所 | 今 | 直す向き |
|---|---|---|---|
| N-22 | `leader.md` 4.6・4.7 | コミットの分け方、題の形と今の慣習の例 3 つ | 読む道具が無いので縛りは今のまま。4.7 の例を外して短くする案（例は `git log` にある） |

## 親がする（利用者の了承の要らないもの）

- 道具の docstring の `take.py patch`（`after_commit.py`・`fuzz.py`・`gate.py`・`gate_runs.py`）を `work.py` に直す。規則が `work.py` を指した後に `tools/take.py` を消す（決定の「規則を直すまで残す」）。
- フックの止めの文面が指す規則の番号（`checks.md` 4.2 など）を、消した規則を指さない形に直す（理由を文面に書く）。
- 規則の直しの後に、文書の点検の担当（onsa-docs）を回す（`docs-due` の 2 件と合わせる）。
- help どうしのずれを揃える（advisor の M-2・M-3）: `docs.py help set` の時機（DONE）と `work.py commit --done`、`work.py help apply` の時機（担当の引き継ぎ）と `sync --apply`。規則が一つを名指した後に、help の方を規則に合わせる。
- 後に回す（advisor の M-4、低）: `rules/budgets.md` の「担当の文脈の予算 約 30 万」と `handback.CONTEXT_BUDGET` の二重。

## 利用者の判断が要るもの（advisor の段 2 の (B)）

- B-1 `rules/tools.md` 9.3 の字面「使い方（下位の命令、引数、例）は help に置く」と、上の直す向き（`work.py sync`、`commit --done` などを規則に書く）の食い違い。X-9 の決定も「始めに `work.py sync`」と命令の名を書いている。
- B-2 フックの止めの誤り（advisor の M-8 ほか、親が再現した）を X-9 の残りで直すか。ヒアドキュメントの本文やバッククォートの中の道具の名を命令として読み、正しい操作を止める（`rules/tools.md` 9.2 の 5 に触れる）。

## 今のまま（理由）

- K-1 help の無い道具の使い方（`documents.md` 5.2 の `ignores.py`・`pending.py`、`common.md` 1.8 の `bg.py`、`checks.md` 4.7 の `run_cases.py`、`process.md` 8.6 の gate の回し方）: 道具に help が無いので、規則から消すと使い方が無くなる。help は道具に手を入れるときに当てる（X9-7 の決定）。
- K-2 `common.md` 1.5（引用符の無いヒアドキュメント）: フックは知らせるだけで、命令は走る。規則が先に要る。
- K-3 `common.md` 2.4 の一段目（報告の前の WIP）: 作業ツリーは残り `patch` は未コミットも写すが、WIP は単位ごとの差と直しの差を分けて読むのに使う。
- K-4 定義 onsa-test の「`crates/` のソースを読まない」と onsa-gap の「自分でビルドしない」: 禁止だけでなく、作業の仕方（期待値を仕様から導く、親のバイナリを使う）の原則。フックは歯止め。
- K-5 `leader.md` 3.4（`pending.toml` は dev の版から作り直す）: `take` は 3-way のときに 3.4 を指す行を出すだけで、作り直しは手で行う。

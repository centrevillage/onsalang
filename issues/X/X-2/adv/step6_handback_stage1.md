## X-2 手順 6（文書の移行）第 1 段: 独立の案

読んだもの: 作業票、`rules/README.md`・`common.md`・`criteria.md`・`documents.md`、`docs/process_improvement_after_w3.md` 2 章、`step2_structure.md`〜`step5_manager.md`、U3 の報告、`docs/carryovers.md` の「X-2 の移行」の行、`tools/repo.py`（`KINDS`・`Layout`・`spec_doc`）、`tools/docs.py`（`read_head`・`render_head`・`head_update`、`SEC_QUALIFIERS`）、`tools/test_gate.py` の `Repo`・`NEW_LAYOUT`・`OLD_LAYOUT` の位置、段 (2) の `split.py`・`rewrite.py` の頭。
大きな文書は見出しと行数と標本の行だけを引いた。

### 数えた事実（案の根拠。2026-10-16 の dev `0adb450`）

- 計画 §2 の S の行 551（ID は一意）。✅ 417、✅ なし 134。行の中に日付を含む 529、W の ID を含む 358。「決める時期」の値は W3 251、M3 46、W2 43、M2 42、M4 37、W4 33、M1 32、W7 17、— 13、W5 12、P2 5、M5 5。
- 変更点 §4（`docs/onsa-0.3-changes.md` 82〜498 行）は `| ID | 内容 | 仕様 |` の表で S の項目 380（複数 ID の行あり）。`spec` の欄の出所に使える。
- rework §3 の W の行 105、✅ 48。「実現する決定」のセルの最長 1,834 バイト。「役割・印」の値は空 46、〔危険〕23、基盤 11、〔メモ〕〔危険〕7、テスト 6、〔メモ〕5、基盤（U3）1、テスト・壊す側 1 と、列ずれに見える行が数件。rework §2 の段の表は 10 行。
- レビュー: R の本文 `#### R-nnn 題` 235、§8 の行 241（ID 236。R-90 が (i)〜(iv) の 4 行、R-08・R-113 が 2 行。本文の無い ID が 1 つ）。本文の最初の箕条は `低〜中・直す（…）・観点 1｜syntax（…）｜§18.1（S-236）` の定型。
- D 16（計画 §1）、K 23（rework §1）、Q 15〜16（`process-improvement-phase1.md` §2）、A 14（表）、RF 16（持ち越しに ID あり）。計画 §3 は 3.1〜3.6 の 6 節、約 2.7 万バイト。
- 空白の資料: `### S-nnn 題` の見出し 153（DF-4 の 152 とほぼ一致）。各組に `## 一覧`（ID・論点・推奨・確度・待つ作業・Fable・状態）の表があり、「状態」は 回答待ち・決定・反映済み。
- 持ち越し: 最上位の箕条 69。頭が `**W<段>-<番号>` のもの 41、`**W<段> の…`（段だけ）6、`**M6` 1、`**S-nnn の下書き` 2、`**リファクタリングの候補` 3、残り約 16。
- 経路の参照（`crates`・`tests`・`tools`・`std`、`test_gate.py` を除く）: `onsa-tools.md` 196、`foreign-forms.toml` 102（うち `crates/onsa_tests/src/foreign_forms.rs:33` の `pub const PATH = "docs/foreign-forms.toml"` は実行時に読む経路）、`implementation-tasks.md` 13、`onsa-lang-spec-0.3.md` 3、`rework-phase1.md` 3、`api-candidates.md` 3、`review-impl-phase1.md` 2、`consistency-check` 1。`rules/` には leader 10、process 8、criteria 4、documents 2、common 1。
  担当の定義 5 ファイルに 7 行。`tests/pending.toml` のコメント 3 行。
- 仕様: H1 と前書きの後に `---`、各章の前に `---` と空行。章の大きさは §11 が約 4.8 万バイト、§2 4.2 万、§18 3.4 万、§6 3.0 万、§4 2.7 万（DS-7 の「全ての章が 2.5 万字に収まる」はバイトでは外れる。目安で gate は落とさないので支障なし。確信 低〜中、字数で数え直していない）。
- `test_gate.py`: 今の配置の作り物 `Repo`（167 行〜）は `Repo(` が 3 か所、`DOC_*` と今の文書名の参照が 20 か所。`OLD_LAYOUT`（4366 行）と `NEW_LAYOUT`（4273 行）が並ぶ。

### M1 段の分け方と順

**結論: DS-9 の (3)〜(7) をそのままの順で行う。(4) と (5) は分けたまま、同じ区切りに続けて行う。(3) に `foreign-forms.toml` の置き場所の決定と移動を足す。各段は「文書の移動のコミット」1 つを基本にし、規則の文と道具の掃除は別のコミットにする。** 確信 中〜高。

- (3) 仕様の章の分割と `spec/tools.md`、`spec/foreign-forms.toml`:
  - 動かすもの: `onsa-lang-spec-0.3.md` → `spec/README.md`（H1・前書き・§0・§1・章の一覧の表）+ 章 20 ファイル（`02-lexical.md`〜`20-order.md`。§19 も章）。`docs/onsa-tools.md` → `spec/tools.md`。`docs/foreign-forms.toml` → `spec/foreign-forms.toml`（下の M4）。
  - 経路の置き換え: `onsa-tools.md` 196 + `foreign-forms.toml` 102 + 仕様のファイル名 3 を同じコミットに入れる（DS-9 で決定済み。`rules/common.md` 1.11、`criteria.md` 7.32 の経路も）。`spec_sections` の `tools.md §` の判定は「`tools.md` の直後の §」なので（`repo.SECTION_RE`）、経路が変わっても § の照合は通る。
  - gate が通る条件: `repo.spec_doc` が `spec/README.md` の `## 章の一覧` の前と章を結合する（U2 で済み）。`Layout.source("spec")` は `spec/README.md` の存在で切り替わるので道具のコミットは要らない。
  - コミット: 1 つ（移動 + 分割 + 経路）。ただし `tests/cst/*.onsa` 2 件と `tests/spec/**/*.onsa` 約 80 件のコメントの経路が変わる。CST の golden はコメントの字とバイトの位置を含みうるので、golden の更新が出れば同じコミットに入れる（下の M6 のリスク）。
- (4) 決定の切り出し: S 551（計画 §2）、D 16（計画 §1）、K 23（rework §1）、Q 15〜16（PI §2）、A 14、`decisions/design/`（計画 §3 を 3.1〜3.6 の 6 ファイル）。合計約 625 ファイル。
  - S の `tasks` は rework §3 の「実現する決定」の逆引きから作る（表は読むだけで動かさない）。R の `fix` も §8 を読むが、R は (5)。
  - gate: `Layout.source("S")`・`("A")` が `decisions/S/`・`decisions/A/` の存在で切り替わる。`decisions/README.md` の頭の欄の表（`## 頭の欄`）が無いと `check` が「no field table」で落ちるので、README は親が段の前に用意する（M3）。
  - コミット: 2 つ。(a) 決定のファイル + 計画 §1〜§3 と API の表と rework §1 と PI §2 の削除 + 経路の直し、(b) 担当の定義（`onsa-gap` 9・13 行、`onsa-impl` 15、`onsa-advisor` 13・16、`onsa-break` 15。親が文を提案し利用者が直す。持ち越しの行のとおり）。
- (5) 問題と作業: W 105（rework §3）、R 235〜236（本文 + §8）、RF 16、X 2（`process_improvement_after_w3.md` の 1・2 章）と `issues/X/X-1/`・`X-2/`（今の `docs/process_improvement_after_w3/`）、`tasks/README.md`（rework §2 の段の表、「作業の数」の欄を除く）、`tasks/diag-codes.md`（計画 §5）、持ち越し 69 項目の解体。
  約 370 ファイル。
  - gate: `Layout.source("W")`・`("R")`・`("diag")`。`pending.load_docs` の W の読みは `layout` 経由（U2）。持ち越しの行の「`pending.PHASE1_END = "M9"` と `stage_of`」は (5) で計画 §4 が残る間は壊れないが、(6) の前に段の一覧の読み先を決める（M4・M5）。
  - コミット: 2 つ。(a) 文書の移動 + 経路（`tests/pending.toml` 13 行のコメントを含む）、(b) `rules/leader.md` 6.2「揃えて更新する文書」と 6.3（計画 §5 → `tasks/diag-codes.md`）の文（DS-9 は「同時に書き換える」。規則の文なので利用者の了承の後、同じ区切りの別のコミット）。
- (6) 履歴と索引: 残りを `history/` に `git mv`（0.2・kumi・ori の仕様、`review-draft-*`、`impl-review-0.3`、`implementation-plan`、`onsa-0.2-changes`、`onsa-0.3-changes`、`comparison-ori-kumi`、`kumi-vs-rust`、`consistency-check-phase1`、`spec-gaps-*` 3 つ、PI の残り、レビューの §0〜§7、計画の §0・§4・§6・§7、rework の §4・§5）、`docs/` を消す、直下の `README.md` を索引にする（`rules/leader.md` の付録の地図を移す）、各ディレクトリの README。
  - gate: `Layout.source("T")` が `None` になり `pending` の T の読みが消える。残りの経路 25 か所の置き換え。
  - コミット: 2 つ。(a) 移動 + 索引 + 経路、(b) 道具の掃除（DT-7。`repo.rows`・`section`・`DOC_*`・`Layout` の `old` の枝、`docs.Ids._old`・`Index.known` の旧の枝、`test_gate.Repo` と `OLD_LAYOUT`、旧のファイル名を文に出す 5 か所、T の扱いの一本化。見積もり −300〜−500 行、+50 行。「`layout` が `docs/` を読まない」自己テストを足す）。
- (7) 規則の文の見直し（M7）。

分ける・まとめる・入れ替えの判断:
- (4) と (5) をまとめない理由: 一度の親のレビューが約 1,000 ファイルと二種類の判断の一覧になり、失敗の戻しも大きい。gate を一回分減らす利益より小さい。同じ区切りに続けて行えば W4 の停止の期間は同じ。確信 中。
- (3) を最初に置く理由: 判断が無く、往復が `spec_doc` そのもので確かめられ、道具と担当の手順の試運転になる。
- 履歴の移動を (3) に前倒ししない: 利益が無い（gate は履歴を読まない）。README のリンクが二度変わるだけ。

### M2 移行の道具

置き場所は `docs/process_improvement_after_w3/x2/tools/`（(5) で `issues/X/X-2/tools/` に動く）。全て Python、標準ライブラリ、`tools/repo.py`・`tools/docs.py` を import する。
各道具は「読み → 出力ディレクトリ（scratchpad）に書く → 往復を確かめる → 一覧を出す」の一方向で、主のツリーに書くのは往復が通ったときだけ（`--apply`）。どれも入力の大きさに線形、固定点も再帰も無く、一度の走査で止まる。

1. `split_spec.py <repo> <out>`: 仕様を `spec/README.md` と章に切る。章の切れ目は `## N. ` の見出しの前の `---` と空行の扱いを `repo.spec_doc` の約束（章は末尾の `---` を持ち、`## N. ` で始まる）に合わせる。章のファイル名と一行の要約は親が表（`chapters.tsv`）で渡す。
   往復: `repo.spec_doc(out).text == read_exact(repo, SPEC)` をバイトで比べる（本番の読み手が逆関数なので、別の結合を書かない。D-15）。出力: ファイルと大きさの一覧、不一致なら最初の差の行。
2. `rewrite_paths.py <repo> <map.tsv> <log>`: 段 (2) の `rewrite.py` の一般化。
   対応表（旧の経路 → 新。長い鍵から当てる）を `crates`・`tests`・`tools`・`std`・`rules`・残る `docs`・`README.md`・`CLAUDE.md` に当て、変えた行を全て記録に出す。`.claude/agents/` と `history/` は対象外。前に grep で数えた件数と置き換えの数が一致しなければ止める。冪等（二度目は 0 件）。
3. `split_tables.py <repo> <out> --kind S|D|K|Q|A|W|R [--overrides map.toml]`: 表の行と見出しの節を ID ごとのファイルにする。
   - 本文は全ての欄を元の欄名のラベルで `- <欄名>: <セル>` として移す（`\|` は `|` に戻す。コードスパンの中の `|` は `docs.table_cells` の切り方）。見出し形式（D・K・Q・R の本文）は見出しの下の箕条をそのまま。
   - 頭の欄は固定の規則で導く（M4 の表）。規則に当たらない値は書かず、`judgments.tsv`（ID、キー、元の字、当たらなかった規則）に出す。親は `overrides.toml`（ID → キー = 値）を書いて再実行する。一覧に無い ID・キーの override は拒む（一覧が単調に減る）。
   - 往復: 新しいファイルの本文のラベルから元の表の行（と見出しの節）を作り直し、元の節とバイトで比べる。頭の欄は表には無いので往復の対象外で、代わりに `docs.py check` と、逆引きの一致（S の `tasks` の和集合 == W のセルの ID の集合、R の `fix` == §8 の反映の欄の W の集合）を別に出す。
   - 書き手は `docs.render_head`・`head_update` の正規形を使う（書き方を二つにしない、DT-8）。
4. `split_carryovers.py <repo> <out> [--map map.toml]`: 最上位の箕条ごとに宛先を決め、作業のファイルの `- 持ち越し:` の下に出所付きで足す。規則: 頭の太字が `W<段>-<番号>` で始まれば（複数なら各 ID に写す）その作業へ。
   それ以外は親の対応表（宛先: W の ID、`R`、`RF-n`、`X-n`、`rules`、`history`）。対応表に無い項目は書かず一覧に出す。往復: 動かした項目を元の順で連結し、元の文書の本文とバイトで比べる。
5. `move_history.py <repo> <map.tsv>`: `git mv` の列と README のリンクの確かめ。往復は `git diff -M --stat` の 100% の改名と、`tools/moved_only.py` の考え方で「移すだけ」を確かめる。

親に出す一覧（段ごと）: 書いたファイルの数（種類ごと）、往復の結果、`judgments.tsv`、経路の置き換えの記録、`docs.py check` の出力、grep の ID の総数の前後比較（S 551、R 235、W 105、D 16、K 23、Q 15〜16、A 14、RF 16。履歴を除いて前後で同じ数）。

### M3 誰が書き、誰が回すか

- 移行の道具は `onsa-impl` が書く（`onsa-docs` はコードを書かない。`rules/documents.md` 5.6 の外枠）。親が書く案は、段 (2) の 330 行の前例があるが、(4)(5) の道具は逆引き・判断の一覧・override の再実行を持ち、親の文脈に 500 行を入れる費用の方が高い。
  単位は 2 つ: U4（`split_spec`・`rewrite_paths`・`move_history`。約 150〜200 行）、U5（`split_tables`・`split_carryovers`。約 350〜450 行）。設計メモは短くてよい（表の欄 → ラベルと頭の欄の規則の表が設計メモそのもの）。
  自己テストは「本番の文書に対する往復が一致する」ことと、小さな作り物での判断の一覧。壊す側は置かない（一度きりの道具で、出力は往復・`check`・gate・親の一覧で確かめる。検証の深さの釣り合い）。確信 中。
- U5 は U4 と並行して作業ツリーで書ける（触るファイルが違う）。(3) を主のツリーで回す間に U5 を書ける（主のツリーを触るのは一度に一つ）。
- 段の実作業は `onsa-docs` が主のツリーで行う（DM-7、決定済み）。ただし判断の一覧が要る段は二票にする: (A) 乾いた実行（出力は scratchpad、一覧と、持ち越しの宛先の案を報告。作業ツリーでよい）、(B) 親の対応表を当てて主のツリーに書き、`check` と gate を回し、報告。(3) と (6) は (B) だけ。
  (4) は一覧が機械的（✅ の食い違い、§、日付）なので親が乾いた実行を自分で一コマンド回し、(B) だけ担当に出すのが安い。(5) は持ち越しの約 28 項目の宛先の案に担当の読みが要るので (A)(B)。確信 中。
- 親が段の前に用意するもの（親の字として票に添える）: 各ディレクトリの README（頭の欄の表は `test_gate.NEW_LAYOUT` の形がそのまま使える。本文のラベルの箕条は `new` が読む）、`spec/README.md` の章の表の一行の要約、章のファイル名の表、design の 6 ファイル名、A の状態の対応表、持ち越しの対応表。
- 親のレビューの読み方: ファイルを開いて読まない。読むのは (a) `git diff --stat` と改名の割合、(b) 往復の出力、(c) 判断の一覧と当てた override、(d) `check` と gate の出力、(e) 種類ごとに 3〜5 ファイルの標本（最大の行、複数行の R-90、✅ の無い S、印の修飾のある W）、(f) 経路の置き換えの記録の全行（数百行）。
- 単位の大きさ: docs の一票は道具の出力と一覧が主で、10〜15 万トークンの見込み（未測。DM-1 の見込みと同じ）。(5) の (A) は持ち越し 8 万バイトを読むので上限に近い。

### M4 判断の要るもの（段ごと。機械 / 親 / 利用者）

(3)
- 章のファイル名 20、要約 20 行: 親。
- `foreign-forms.toml` の置き場所: 親が提案し利用者に一言で出す（DS-1 で「移行で決める」）。私の案は `spec/foreign-forms.toml`。理由: §18.1 と S-250 が指す閉じた一覧で、人が読まない規範の表（`criteria.md` 7.10）。`repo.chapters` は `*.md` だけを見るので支障なし。
  代替は `tools/`（`builtin_names.toml` の隣だが、あちらは仕様から作る道具のデータで性質が違う）。確信 中。
- `---` の帰属（章の末尾か頭か）: 機械（`spec_doc` の約束に従う）。

(4) S
- `status`: ✅ → DECIDED、無し → OPEN（機械）。食い違いの一覧: ✅ 無しで行に `決定（` を含むか、空白の資料の一覧の「状態」が 決定・反映済み（親が一件ずつ）。✅ ありで一覧が 回答待ち（親）。
- `decided`: 行の最初の `決定（YYYY-MM-DD` の日付（機械。529 行に日付があるが、`決定（` の形でないものは書かない）。複数の日付の行は一覧。無いものは書かず、`changes` の注が後で挙げる（DT-6）。
- `spec`: 変更点 §4 の「仕様」の欄（380 項目）、無ければ行の中の `§` 全て（機械）。仕様の見出しに無い § 9 個（持ち越しの行）は一覧 → 親が字を直す。
- `tasks`: rework §3 のセルの逆引き（機械）。「決める時期」が W の段なのに W の行に無い S は一覧（親。宛先の無い決定、`leader.md` 6.5）。
- `group`・題・元の下書き: 空白の資料の `## 第 N 組` と `### S-nnn 題` から（機械。153 件に題、一覧の表にある S に `group`）。本文の末尾に `- 元の下書き: <履歴のファイル> の「### S-nnn …」` を足す（DS-2 が構造の欄に挙げるが DF-4 の表に無い。人が読むだけなので本文。履歴は直さないので安定）。
- 本文のラベル: 元の欄名（`項目`・`提案`・`決める時期`）のまま移すことを推す（移すだけで往復が成り立つ。DF-4 の `空白`・`決定` に揃えるなら親の対応表 `項目→空白`、✅ の行の `提案→決定`、無しの行の `提案→案`。`案` は S のラベルの一覧に無いので一覧の変更が要る）。親。確信 中。
- 空白の資料で 回答待ち の S（下書きが済んで未決）: `decisions/S/S-nnn.draft.md` を作るか、履歴の見出しを指すだけにするか。利用者が答えの途中かもしれないので親が件数を見て決める。
- 計画 §2 の前書き 2 段落: `decisions/S/README.md` か履歴。親。
(4) D・K・Q・A・design
- D・K: `status = DECIDED` 一律（機械）。`spec` は本文の § 全て。
- Q: PI §4 の決定の記録の表から（採用・保留）→ 親が対応表。
- A: 「状態」の欄 不採用（日付）/ 保留 / 採用 → `status` と `decided` の三項の対応表（例: 不採用 → DECIDED と本文 `決定: 不採用`、保留 → OPEN）。親。
- design の 6 ファイル名: 親。

(5) W
- `status`: ✅ → DONE、無し → PLAN（機械）。DOING・PENDING は親が一覧で指定。
- `size`: S/M/L（機械）。`depends`: W の ID の抽出（機械）、ID 以外の字を含む欄は本文 `- 依存:` に残して一覧。
- `marks`: 〔〕を外して閉じた値に一致する語（機械）。修飾のある 4 行程度（基盤（U3）、テスト・壊す側 など）は一覧 → 本文の `単位` へ（親の対応表）。
- 「実現する決定」の欄: 本文に元のラベルで残すことを推す（セルに `(4)`・`の定数のパターンの降下` のような部分の修飾があり、ID だけに落とすと失われる。頭の欄の関係は S の `tasks` と R の `fix` が持ち、`show` が出す）。重複を嫌うなら消す案だが、その場合は修飾のあるセルの一覧を親が読む。親（利用者に一言）。確信 中。
(5) R
- 本文の最初の箕条の定型から `severity`・`aspect`・`spec`・`decisions`（機械）。定型に合わない R は一覧。
- `fix`: §8 の反映の欄の W の ID（機械）。W が無い行（「仕様 §… に反映済み」だけ、「直さない」）は一覧 → 親が OPEN / WONTFIX / DONE を決める。
- `status`: `fix` が全て ✅ の W なら DONE、それ以外 OPEN（機械。`check` の (c) と同じ規則）。
- §8 の複数行（R-90 ×4、R-08・R-113 ×2）: 行ごとに `- 決定（2026-10-02）: <決定> / 反映: <反映>` を順に足す（機械）。本文の無い 1 件は一覧。
- `found_by`: 書かない。
(5) 持ち越し
- 41 項目は機械。残り約 28: 担当が案を出し親が決める。「W4〜W7 のテストの票」は `rules/process.md`（DF-5 で決定済み。(7) の文として親が提案）。`M6` と「W3 の終わり」「W3 の後、W4 の前」の 6 項目は、済んだものは履歴、残るものは X か R。「S-nnn の下書き」2 件は決定のファイルの本文に `補い`。「リファクタリングの候補」3 件は RF の ID の有無で分ける。
(5) その他
- `tasks/README.md` の段の表: 「作業の数」の欄を落とし、「W10 の後は M5〜M9（§4）」の文を残すか: 親。
- 段の一覧の読み先と `PHASE1_END`: (6) の前に道具を直す。私の案は、`tasks/README.md` の段の表に W1〜W10 と、M5〜M9 を一行（残りの段）として置き、`pending.stage_of` はこの表から段の名を読み、`PHASE1_END` はコードの定数のまま。親（利用者に一言）。

(6)
- 履歴のファイル名: 元の名のまま平らに置く（`history/onsa-lang-spec-0.2.md`、`history/spec-gaps-w3b.md`）。親。
- 直下の README の文と各 README の目的の文: 親が書く。利用者はコミットで見る。
- `.claude/agents/` と `CLAUDE.md` の経路: 利用者が直す（親が文を提案）。

### M5 道具とコードとテストの経路

- 置き換えは対象が動く段で行う: (3) `docs/onsa-tools.md`→`spec/tools.md`（196）、`docs/foreign-forms.toml`→`spec/foreign-forms.toml`（102。`foreign_forms.rs` の `PATH` は実行時の経路なので同じコミットでないとテストが落ちる）、`onsa-lang-spec-0.3.md`（3。章の経路でなく `spec/` と書く）。
  (4) `implementation-tasks.md` の §1〜§3 を指すもの（13 の一部。`§3.6` は `decisions/design/`）。(5) `rework-phase1.md`（3）、`review-impl-phase1.md`（2）、計画 §5 を指すもの（`tasks/diag-codes.md`）、`tests/pending.toml` のコメント 3 行。
  (6) 残り（`api-candidates.md` 3 は (4) で `decisions/A/`、`consistency-check` 1 は履歴）。
- gate の読み先: S・A・W・R・diag・spec・tools は `Layout` の存在の判定（U2）。T は (6) で `None`。`pending.load_docs` の呼び出し元 5 つは変えない。
  計画 §5 の「欠番:」と「第 2 期」の読み（`repo.retired_codes`・`phase2_codes`）は `tasks/diag-codes.md` へ（`FILES["diag"]` あり）。`rules/leader.md` 6.3 の文は (5) で直す。
- 最後の段の掃除（(6) の (b) のコミット、impl か親）: 持ち越しの行の全項目。加えて U3 の「範囲の外」1（`check_write` に ID の存在の確かめ）は数行なので同じ回に入れてよい（`criteria.md` 7.12）。`pending.load` を `repo` へ移す循環の解消は任意。

### M6 進め方とリスク

- 段の前提: 主のツリーが clean で、担当が動いていない。票に基のコミットを書く。
- 戻し方: 段の中はコミットしないので、失敗したら `git restore --staged --worktree :/` と、新しいディレクトリに限った `git clean -fd -- spec decisions issues tasks history` で基に戻る（`git stash` は使わない。1.4）。段の間でセッションが切れても、状態は「段 k まで済み」のコミットで一意。道具は基の状態に対して冪等なので再実行でよい。
- W4 を止める期間の見当（未測。gate の全体は主のツリーで約 19 分、31 回目）: (3) 約 1 時間（gate 1 回 + golden の確かめ）、(4) 1〜1.5 時間（乾いた実行 + 判断 + 本番 + gate）、(5) 2 時間（(A)(B) の二票 + 規則 6.2 の了承）、(6) 1 時間 + 掃除の道具。合計 1〜1.5 日分のセッション。
  U4・U5 の実装は W4 の前なので W4 を止めない。(7) の規則の文は W4 と並べて進められるが、8.1 の票の雛形の変更は W4 の最初の票の前に済ませたい。
- 費用の見当（未測。`leader.md` 2.8 の実測から）: impl 2 単位 × 20〜50 万、docs 6 票 × 10〜15 万、親のレビューは一覧と標本だけなので段ごとに数万。
- 情報が欠けないことの確かめ（利用者の「事前のチェックツール」）: (i) 切り出しはバイトの往復、(ii) 移すだけは `git` の改名 100% と `moved_only.py` の考え、(iii) ID の数の前後比較（履歴を除く）、(iv) `docs.py check` 0 件、(v) 頭の欄の逆引きの一致。この確かめが見ないもの: 頭の欄の値の意味（✅ → DECIDED の読み替えなど）。そこは判断の一覧と親の標本で見る。
- リスク: (3) の経路の置き換えが `tests/cst/*.onsa`（2 件）と `tests/spec/**/*.onsa`（約 80 件）のコメントを変え、CST の golden（コメントの字とバイト位置）と `//~` の列が動きうる。(3) は `--quick` でなく全体の gate を回し、golden の更新は同じコミットに入れる。
  代替は test の入力の経路は書き換えないこと（古い経路のコメントが残るが無害）。私は書き換えて gate で確かめる方を推す。確信 中。
- リスク: `docs check` (b) が、頭の欄付きのファイルに移った本文の無い ID（`R-2` のような報告の中の番号、U3 の報告の not found 27 の一部）と § 9 個で落ちる。乾いた実行の `check` で一覧にし、親が字を直す。
- リスク: README の頭の欄の表が無いと `check` がそのディレクトリ全体を一件で止める（DT-1）。段の前に親が置く。
- リスク: 持ち越しの解体で宛先の W が DONE のもの（済んだ作業への持ち越し）は、作業のファイルに残してよい（DF-6「DONE になっても消さない」）。
- リスク: `test_gate.Repo` の掃除で、`pending`・`ignores`・`gap_marks` の自己テストが今の配置の作り物に依存している所を新しい配置の作り物に差し替える量が見積もりより大きい可能性（20 か所）。(6) の (b) は見積もりを設計メモで出させる。

### M7 段 (7) の範囲（文の案は書かない。項目の一覧）

経路だけの直しは各段で docs が行う（5.6 の除外）。文の変更は (7) で親が提案し利用者が了承する。古くなるきっかけの段を括弧に書く。

- `rules/process.md`: 8.1 の雛形（票は作業のファイルを指す、`ticket` の骨組み、「使う番号が登録済みか」。DF-6）。8.2 の作業の一覧の経路（(5)）。8.4 の空白の報告が指す「計画 §2」（(4)）。8.5・8.6 の箕条の番号付け（段 (2) から回したもの）。8.6 の 6（決定のコミットが仕様・変更点・計画 §2・反映の作業・レビューの表を揃える → 決定のファイル一つと `set`・`amend`。(4)(5)）。8.6 の下書きの置き場所（`decisions/S/S-xxx.draft.md`。(4)）。
- `rules/leader.md`: 1.4（壊す側の報告を消さない → 要る点は R・RF へ。DF-5）。2 章（票を書くとき `ticket`・`show --relations` を使う）。5.6（登録の網で `back`・`list S --section` を使う）。6.2（揃えて更新する文書。(5) と同時）。6.3（計画 §5 → `tasks/diag-codes.md`。(5)）。付録の地図（直下の README へ。(6)）。
- `rules/common.md`: 1.9 の注（文書の整理の後に見直す、と自分で書いている）。1.11 の `docs/onsa-tools.md`（(3)、経路のみ）。2.3 の例外の文言。
- `rules/documents.md`: 5.3（スワップの確かめの対象 `docs/`・`rules/` → 新しいディレクトリ、`swaps` を使う。「Python の一意一致置換」→ Edit ツールと `set`・`note`）。文書を編集した後に `fmt` を回す規則（DT-4）。「ID のファイルは `show` で読む」（DT-2）。持ち越しの行き先と `note` の使い方（DF-6 の「入れた行はコミットで消す」を改める）。
- `rules/criteria.md`: 7.12・7.30 の `docs/api-candidates.md` → `decisions/A/`（経路、(4)）。7.32 の `docs/foreign-forms.toml`（経路、(3)）。
- `rules/checks.md`: 計画への参照があれば経路（確かめていない）。
- README の約束（規則でなく README に書く。親）: 頭の欄に `\` とコメントを書かない、本文に `+++` だけの行を書かない、`set` が正規形に揃える、`tests/pending.toml` は `check` の対象外、`new` の雛形のラベル。
- 担当の定義（利用者）: gap 9・13・14 行、impl 15、advisor 13・16、break 15。`CLAUDE.md` の仕様の経路。

### M8 もっと単純な代替と、利用者の観点への異論

- 代替 1: (3) と (6) は担当を呼ばず親が道具を一コマンド回す。段 (2) を親が自分で行った前例があり、この二段は判断が無い。費用は docs の票 2 つ分（20〜30 万トークン）減る。代償は gate を待つ時間が親の文脈に入ること（`bg.py` で待てるので小さい）と、DM-7 の「段ごとに一票」から外れること。利用者が担当の試運転を望むなら (3) は担当に出す価値がある。
- 代替 2: 頭の欄を導かず、本文のラベルだけで移してから、別の段で `set` を使って頭の欄を埋める。往復は単純になるが、頭の欄の無いファイルは `check` の「要る欄」で落ちるので gate が通らず、DS-9 の前提に反する。採らない。
- 代替 3: (4) と (5) を一つの段にする（gate が一回減る）。親のレビューと戻しが大きくなるので採らない（M1）。
- 利用者の観点への異論: 「事前のチェックツール」は、移す・分けるの字の保存は保証するが、新しく作る情報（`status`・`fix`・`tasks` などの頭の欄）の正しさは保証できない。そこは機械の規則 + 判断の一覧 + `check` の関係の規則で囲むのが上限で、「情報が欠けない」の約束の範囲をそう明記して進めるのがよい。
- DS-7 の「全ての章が 2.5 万字に収まる」はバイトでは §11 が 4.8 万で外れる。目安で gate は落とさないので支障は無いが、字数で数え直して README に書く数を決めるとよい（確信 低〜中）。

### 関係するファイル

- `/Users/centrevillage/projects/onsalang/docs/process_improvement_after_w3/x2/step2_structure.md`（DS-5・DS-9）、`step3_format.md`（DF-4〜DF-6）、`step4_tools.md`（DT-7・DT-8）、`step5_manager.md`（DM-2・DM-7）
- `/Users/centrevillage/projects/onsalang/tools/repo.py`（`KINDS` 195〜209 行、`Layout` 259〜342 行、`spec_doc` 387〜410 行）
- `/Users/centrevillage/projects/onsalang/tools/docs.py`（`read_head`・`render_head`・`head_update` 462〜526 行、`SEC_QUALIFIERS` 739 行）
- `/Users/centrevillage/projects/onsalang/tools/test_gate.py`（`Repo` 167 行、`NEW_LAYOUT` 4273 行、`OLD_LAYOUT` 4366 行）
- `/Users/centrevillage/projects/onsalang/crates/onsa_tests/src/foreign_forms.rs`（33 行の `PATH`）
- `/Users/centrevillage/projects/onsalang/docs/carryovers.md`（362〜376 行、X-2 の移行に宛てたもの）
- `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/bab613c4-c622-431d-af45-acb02bb8d8c9/scratchpad/s2/split.py`・`rewrite.py`（段 (2) の形）

第 1 段の終わり
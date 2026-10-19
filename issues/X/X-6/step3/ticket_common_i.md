# X-6 の実装の票（共通）

X-6 はリファクタリングの項目で、W の作業ではない。`rules/process.md` 8.2〜8.5 と `rules/refactoring.md`（8 章）に従い、8.3 の完了の定義の代わりに下の受け入れ条件を使う。

- 始めに: 作業ツリーの中で `python3 -B tools/work.py sync` を回す。次に `issues/X/X-6.md` の「決めたこと」（素案の見直し・手順 1・手順 2）、`issues/X/X-6/step1/review.md`、`issues/X/X-6/step2/groups.md` を読む。
  自分の項目の修正方針は `issues/X/X-6/step1/<領域>.md`（グループの票が名指す節）にある。方針と今のコードが違えば、直す前に報告に書く（作った後に dev が進んでいることがある）。
- 範囲を守る: グループの票の項目だけを行う。範囲の外は直さず報告する（8.2 の 6）。関数の中身を変えない移しでは、移したついでの直しをしない。
- 移すだけのコミットと中身を変えるコミットを分ける（作業ツリーの WIP のコミットでよい）。移すだけのものは `python3 -B tools/moved_only.py --orig dev:<元の経路> <分けた先の経路>...` で、移しただけかを確かめる（使い方は `--help`）。
- 基のバイナリ: `/Users/centrevillage/projects/onsalang/target/base/0c22312/onsa`（作業ツリーの基 `0c22312` の dev のビルド）。
- 検査（X-6 の例外。`gate.sh --work` は回さない。〔危険〕のグループだけ票が名指す）:
  1. 触った crate の `cargo test -p <crate>`。
  2. `python3 -B tools/compare.py diags /Users/centrevillage/projects/onsalang/target/base/0c22312/onsa target/debug/onsa`、同じ二つのバイナリで `compare.py fmt`・`compare.py core`（差が 0 件か、票が許す差だけ。`rules/refactoring.md` 8.3）。
  3. `python3 -B tools/compare.py speed`（前後の時間。`rules/refactoring.md` 8.2。使い方は `compare.py help speed`）。
  4. `tools/gate.sh --only static`（`builtin-names` などの静的な項目。分けたファイルの `tools/builtin_names.toml` の節を合わせる）。
  5. 分けたファイルがあれば、`python3 -B tools/refactor.py sizes` の前後。
  6. 文書を触ったら `python3 -B tools/docs.py check`。
- 予算: 文脈は約 30 万トークン（`rules/budgets.md` の「担当の文脈の予算」）。近づいたら、次の区切り（絞ったテストが通る所）で WIP のコミットと「次の担当へ」を書いて止める。
- 見積もり: 着手の前（最初の段）に、テストとデータのファイルを除いて手で書く行を見積もり、親に一行で知らせてから進める（返事は待たなくてよい）。報告には `python3 -B tools/work.py lines --estimate <N>` の出力を付ける。移す行は手で書く行と分けて書く（`git diff -M --stat`）。
- 報告: 最後の返答の本文で、`rules/process.md` 8.4 の形。「完了の定義」の行の代わりに、上の検査 1〜6 の結果（コマンドと要約）と、8.5 の自己点検の表の結果を書く。最後に「次の担当へ」（`rules/common.md` 6.6）。
- 評価の材料（X-6 の手順 8）: 報告の先頭に、見積もりと実際の行数、移した行数、直しに要した往復を書く（親が費用と時間を測る）。

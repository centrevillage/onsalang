# 規則

`.claude/agents/` の `onsa-*` の担当と親が従う規則である。各担当の定義は、役割に固有の規則と、下の表の自分の役割の行への参照を持つ。定義と規則が食い違う場合は定義を優先し、不一致を報告する。

規則は、親が文を提案し、利用者が了承してから親が書く。日付の付いた注意（機械の状態、既知の落ちる入力）は、担当の定義には書かず、規則に書く。直ったら親が改める。
章の見出しの括弧は、対象の役割である（t は `onsa-test`、i は `onsa-impl`、b は `onsa-break`、advisor は `onsa-advisor`、gap は `onsa-gap`、docs は `onsa-docs`）。各担当は、括弧に自分の役割か「全員」がある章に従う。
規則は `rules/common.md` 1.4 のように、ファイルと番号で指す。

## 始めに読む

| 役割 | ファイル |
|---|---|
| 親 | [`leader.md`](leader.md) |
| t、i、b | [`common.md`](common.md)、[`process.md`](process.md) の 8.2〜8.6 |
| advisor、gap | [`common.md`](common.md) |
| docs | [`common.md`](common.md)、[`documents.md`](documents.md) |

## 要るときに読む

| ファイル | 時機 |
|---|---|
| [`checks.md`](checks.md)（4 章） | 検査（gate、テスト、ファズ、自作の掃引）を回す前 |
| [`documents.md`](documents.md)（5 章） | 実装待ちの一覧、テストの ignore、文書を編集する前 |
| [`criteria.md`](criteria.md)（7 章） | 推奨と独立の判断を出す前 |
| [`refactoring.md`](refactoring.md)（8 章） | リファクタリングをする前と、その差分を確かめるとき |
| [`tools.md`](tools.md)（9 章） | 道具を作るか直す前、ツール化の案を出す前 |
| [`process.md`](process.md) | 作業票を書くとき（8.1）、報告を書くとき（8.4）、仕様の空白の流れに関わるとき（8.6） |
| [`budgets.md`](budgets.md) | 作業票を書くとき、担当を動かすとき、費用と大きさを見積もるとき |

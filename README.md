# onsalang

**Onsa** — LLM が書き、人間が監査し、コンパイラが局所的に否定する、DSP 開発のための言語（仕様策定中）。

- 最新の仕様: [`spec/`](spec/README.md)
- 過去の草案と資料（Onsa 0.2、Kumi 0.1、Ori 0.1、変更点、レビュー、実装の計画）: [`history/`](history/README.md)

## 文書の地図

| 場所 | 中身 | 誰が、いつ変えるか |
|---|---|---|
| [`spec/`](spec/README.md) | 仕様（章ごとのファイル）、表示の約束 `tools.md`、他言語の形の表 `foreign-forms.toml` | 親が、決定を反映するとき |
| [`decisions/`](decisions/README.md) | 決定（S・D・K・Q・A） | 親が書き、利用者が決める |
| [`design/`](design/README.md) | 実装の共通の設計 | 親が、設計の決定を受けて |
| [`issues/R/`](issues/R/README.md)・[`issues/RF/`](issues/RF/README.md)・[`issues/X/`](issues/X/README.md) | 問題、リファクタリング、改善の項目 | 親が、見つけたときと判断したとき |
| [`tasks/`](tasks/README.md) | 作業（W）、段の一覧、診断コードの表、第 2 期の持ち越し | 親が、作業を足すときと進めるとき |
| [`rules/`](rules/README.md) | 親と担当の規則と、役割ごとの始めに読むもの | 親が文を出し、利用者が了承して |
| [`history/`](history/README.md) | 過去の文書 | 変えない |
| `.claude/agents/` | 担当の定義 | 利用者 |
| `tests/pending.toml` | 実装待ちの一覧（形はファイルの先頭のコメント） | 作業の票で |
| `tools/gate.sh` | 検査 | — |

## ID と経路

ID ごとに一つのファイルを置く。頭の欄の値と本文のラベルは、各ディレクトリの `README.md` が定める。
頭の欄は TOML で、`+++` だけの行で囲む（本文に `+++` だけの行を書かない）。値に `\` を書かない、キーを重ねない、頭の欄の中にコメントを書かない。頭の欄は `docs.py set` が正規形に揃えて書き、本文の補いは `docs.py note` で足す。

| 種類 | 経路 |
|---|---|
| S・D・K・Q・A | `decisions/<種類>/<ID>.md` |
| R・RF・X | `issues/<種類>/<ID>.md` |
| W | `tasks/W/<ID>.md` |

一覧は `python3 -B tools/docs.py list <種類>`、一つの ID は `docs.py show <ID>`、経路は `docs.py path <ID>`。

## 役割ごとの始めに読むもの

[`rules/README.md`](rules/README.md)。

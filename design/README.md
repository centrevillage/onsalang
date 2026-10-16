# 実装の共通の設計

実装の型と、判断の置き場所の、クレートの境界で共有する形。仕様（`spec/`）を実装の型に落としたもので、決定（`decisions/` の D・Q など）を受けて改める。
実装の担当と壊す側の担当は、構造がこの形に合っているかを照らす。

| § | ファイル | 中身 |
|---|---|---|
| 3.1 | [`01-diag.md`](01-diag.md) | スパンと診断（`onsa_diag`） |
| 3.2 | [`02-ast.md`](02-ast.md) | トークン、CST と AST（`onsa_syntax`） |
| 3.3 | [`03-types.md`](03-types.md) | 型と種（`onsa_sema`） |
| 3.4 | [`04-core.md`](04-core.md) | Core IR と検証器の規則（`onsa_core`） |
| 3.5 | [`05-flow-lowering.md`](05-flow-lowering.md) | flow の降下の形 |
| 3.6 | [`06-placement.md`](06-placement.md) | 判断の置き場所（Q-14）。作業票と gate の直書きの検査が参照する |

各ファイルは計画 §3 の節を一字も変えずに移したもので、§ の番号（3.1〜3.6）は見出しのまま。

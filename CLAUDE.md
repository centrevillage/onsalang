# Onsa

音声信号処理の言語 Onsa の仕様とコンパイラ。仕様は `spec/`（入口は `spec/README.md`）。

- 主のセッションは親（監督とレビュー）として動く。始めに `rules/leader.md` を読む。
- 担当（`.claude/agents/` の `onsa-*`）として呼ばれたときは、上の行を読み飛ばし、自分の定義と `rules/README.md` の自分の役割の行に従う。

+++
status = "OPEN"
+++
# RF-8 sema・core の `children()` の 3 か所と `Ty`/`Rate`/`FlowRate` の並行

- 場所: 構文の crate の外
- 内容:
  - **リファクタリングの候補（W3-10/b・b2、10 回目）:** `Ty` / `Rate` / `FlowRate` の並行、core の `ReadWalk` と sema の `mark` の重複（`At` / `Feedback` の腕が両方に増えた）、遅延の三つ組の対応（W3-10 の最後の直しで一か所にしなければ）。報告は 10 回目の scratchpad の `w310b/report_b.md`・`w310b2/report_b2.md`。

+++
status = "OPEN"
+++
# RF-8 sema・core の `children()` の 3 か所と `Ty`/`Rate`/`FlowRate` の並行

- 場所: 構文の crate の外
- 内容:
  - **リファクタリングの候補（W3-10/b・b2、10 回目）:** `Ty` / `Rate` / `FlowRate` の並行、core の `ReadWalk` と sema の `mark` の重複（`At` / `Feedback` の腕が両方に増えた）、遅延の三つ組の対応（W3-10 の最後の直しで一か所にしなければ）。報告は 10 回目の scratchpad の `w310b/report_b.md`・`w310b2/report_b2.md`。
- 判断（2026-10-19、親）: X-6 の手順 1（44 回目）: (A)・(B) を X-6 で行い、(C) は W7-03、(D) は W7-02 の持ち越しに写した（C-01）。(A)・(B) を済ませたら DONE にする。経緯の報告（W3-10/b・b2）は 44 回目に担当の記録から取り戻し、要点を `issues/X/X-6/step1/C1.md` の 5 章に置いた

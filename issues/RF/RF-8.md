+++
status = "DONE"
+++
# RF-8 sema・core の `children()` の 3 か所と `Ty`/`Rate`/`FlowRate` の並行

- 場所: 構文の crate の外
- 内容:
  - **リファクタリングの候補（W3-10/b・b2、10 回目）:** `Ty` / `Rate` / `FlowRate` の並行、core の `ReadWalk` と sema の `mark` の重複（`At` / `Feedback` の腕が両方に増えた）、遅延の三つ組の対応（W3-10 の最後の直しで一か所にしなければ）。報告は 10 回目の scratchpad の `w310b/report_b.md`・`w310b2/report_b2.md`。
- 判断（2026-10-19、親）: X-6 の手順 1（44 回目）: (A)・(B) を X-6 で行い、(C) は W7-03、(D) は W7-02 の持ち越しに写した（C-01）。(A)・(B) を済ませたら DONE にする。経緯の報告（W3-10/b・b2）は 44 回目に担当の記録から取り戻し、要点を `issues/X/X-6/step1/C1.md` の 5 章に置いた
- 反映（2026-10-19、親）: X-6 M2a（`149e868`、44 回目）で (B)（状態に置く判断を sema の一度の走査にし、`FlowInfo::read_at` を core が読む）、X-6 M2b（`51ec4fb`、45 回目）で (A)（子の列挙を `onsa_syntax` の `Ast::sub_exprs` の一か所にし、sema の `mark` と `onsa graph` が呼ぶ）を行った。
  前後の `compare.py diags`・`core`・`fmt` と flow を持つ全事例の `onsa graph` が差 0。(C)・(D) は W7-03・W7-02 の持ち越し。

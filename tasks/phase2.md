# 第 2 期の持ち越し

第 2 期の作業を作るときに、各作業の `持ち越し` へ移す。

- **第 2 期（fmt の書き換えの残り。29 回目、W3-12 の範囲を縮めた）:** `-> ()`・空の `uses {}` の除去（S-540。無名関数では外さない、S-546）と、冗長な括弧の除去（S-339 の基準、S-115・S-336・S-45 の fmt、S-536 の括弧、S-537 の fmt の部分）を入れる。
  範囲にコメントがあれば書き換えない（S-536 (1)、S-538 (s2)）。書き換えはどのプログラムでも各段の判定を変えない（仕様 §18.2。gate の性質 `meaning` が確かめる）。
  - 材料: `tasks/phase2/`（`u1b_07a0e81.patch`、`u1fix1_d43de9e.patch`、`u2t_dd958b1.patch`、`u1_all_d43de9e.patch`、`handback_f.md`。28 回目の scratchpad の `p2save/` から写した）。
    担当の報告は残さない（X-2 の DF-D）。28 回目の壊す側（/b）の報告の指摘 1〜6（`-> ()`・`uses {}`・`init` の除去の形で、第 2 期の確かめに使える）だけを、その節と再現の入力のまま `tasks/phase2/handback_b_findings.md`・`tasks/phase2/b_repro/` に写した。
  - `crates/onsa_cli/tests/fmt_rewrites.rs` の `PH2:` の ignore 12 件のうち、`x_combinations` の `reset_all`・`alloc_only`、`x_module` の `touch`、`r78` の `set_one` は、値の無い末尾の `return` を外す期待値で、S-547 と食い違う。ignore を外すときに直す（`tasks/phase2/` のパッチの側も同じ）。
  - `tests/spec/fmt/rewrite_unit_uses_until_ph2.onsa` は除去までの形で、除去を入れたら書き換える。
  - 歩きの重複（所見）: `fmt/plan.rs` と `rewrites::normalize` が、どちらも `REWRITES` × 全ての節に CST の側を当てる（選んだ節の一覧を一度作って両方が読める）。`///` の行末の空白は `comment()` を通らず `align::finish` が落とし、比べる側は `comment_text` を使う（食い違えば確かめが 101 にするので安全側）。
  - **W3-12（W3-20 の直し、2026-10-09）:** `-> (fn()) uses {…}` の返り値の関数型を囲む括弧は冗長でない（外すと `uses` が内側の型に付き、型が変わる）。S-339 の基準で外さないことを確かめる事例を足す。型を文字列にする所は `TyStore::parens_before_uses` が同じ規則を持つ。
  - **W3-12（23 回目、第 28 組の下書き）:** 括弧の中に継続の位置でない改行があると、その括弧は冗長でない（`let y = (x` 改行 `as F64)` の括弧を外すと `as` が文の頭になり E0002。S-339 の「外しても構文の段の誤りにならない」の基準）。判定を演算子の強弱だけで書くと漏れ、書き込む前の確かめ（R-204）で内部エラーになる。どの改行が残るかは S-497 の決定による。

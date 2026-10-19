+++
status = "OPEN"
+++
# RF-5 強弱の判断の 3 か所

- 内容: 強弱の判断の 3 か所（`parser` の `tighter`、`lower` の `chain()`、`groups` の `Order::tighter`）と `groups.rs` が AST を `Flat::new` で平らに戻して読み直すこと、パーサの高さと AST の高さを突き合わせるテスト（W3-07/b）。
  - **リファクタリングの候補（時期は別に決める）:**
    - W3-07/b（2026-10-09）: 強弱の判断の閉包が 3 か所（`parser.rs` の `tighter`、`lower.rs` の `chain()`、`groups.rs` の `Order::tighter`）。
      - `groups.rs` が AST の木を `Flat::new` で平らに戻して読み直す（E0010 の判定は AST の辺で足りる、D-15）。
      - `key()`・`GROUPS`・`KEYS` が位置で対応。
      - AST の子を列挙する `children()` が 3 か所（sema の flow、Core の flow、`graph.rs`）。
      - パーサの高さと AST の木の高さを突き合わせるテストが無い。
      - `groups.rs` は約 430 行で、判定・読みの列挙・候補の書き出し・入れ子の確かめに分けられる。
- 補い（2026-10-19、親）: X-6 の S1 の壊す側（44 回目）: `groups.rs` の `chain_nodes` と `Flat::new` が同じ鎖を二度平らにする（E0010 の出る鎖だけ。演算子の順の約束も二つ）。得が小さいので X-6 では直していない

+++
status = "OPEN"
+++
# RF-5 強弱の判断の 3 か所

- 内容: 強弱の判断の 3 か所（`parser` の `tighter`、`lower` の `chain()`、`groups` の `Order::tighter`）と `groups.rs` が AST を `Flat::new` で平らに戻して読み直すこと、パーサの高さと AST の高さを突き合わせるテスト（W3-07/b）。

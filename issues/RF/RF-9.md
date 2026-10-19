+++
status = "OPEN"
+++
# RF-9 W3-05 の壊す側の候補

- 内容:
  - `literal::Form` の二つの役割の混在、`literal.rs` と `lexer.rs` の循環（`is_ident_start`）、`ConstValue::FloatText` を持つ理由を doc に。
  - `Found` と `Literals` の `strings: Vec<(Span, Span)>`・`numbers: Vec<(Span, Number)>` に名前の付いた型を。
  - `foreign::at_failure` の `RowId::StringPrefix` だけの分かれを、`Hit` の「報告した範囲」の欄に（他の行が同じ手段を要したときに分かれを増やさない）。
  - 「空白を除くと別の数の読みになるか」の判定が `spaces.rs` の `space_around_dot` と `literals.rs` の `foreign_literal` の二か所（`joins`）。`spaces.rs` の `chars().take(3)` の決め打ち。
  - 「整数か浮動小数か」で負のパターンに入るかを、パーサの `foreign_integer` でなく表の側の一か所で決める。今は `-(017)`・`-(0o17)`・`-(1u8)` と `-0b11f32` のパターンが「expected a pattern, found `-`」の一般の E0002 のまま（式の `-(017)` は E0020）。
  - 字句解析器の接する形を、名前の側とリテラルの側の二つにする（S-473 の決定しだい）。
- 経緯: 単位 1・単位 2・直しの往復 1 の再確認。報告は 17 回目の scratchpad の `w305b1/`・`w305b2/`・`w305b3/handback_b.md`
- 判断（2026-10-19、親）: X-6 の手順 1（44 回目）: (a3)・(d1) は済んでいた。(e2) は S-456、(f) は S-473・S-469 を待つので X-6 の外。(c) の主は S-466 の `prefixed` で、X-6 で行う（FAUST の `prime_note` は動かすだけで残す、RF-11）。(e1) は出力を変える組で行う。`issues/X/X-6/step1/B.md`
- 反映（2026-10-19、親）: X-6 で (a2)（S0、`e370484`。`chars.rs`）、(c)（S2、`16e7185`。`Hit` の報告した範囲の欄）、(a1)・(b)・(d2)（S3、`0be038e`。`Form` の三つの層と `Number::foreign`、`ForeignNumber`・`ForeignString`、数の候補の「合わさるか」を `edits::joining` に）を行った。
  前後の `compare.py diags`・`fmt`・`core` と (d2) の格子 2550 件が差 0。残りは (e1)（X-6 の変える組 V）、(e2)（S-456）、(f)（S-473・S-469）。

# M0〜M4 のコードレビューの再現の入力

[`docs/review-impl-phase1.md`](../../docs/review-impl-phase1.md)（R-01〜R-130）の指摘を再現した入力を、資料として残したもの。2026-10-02〜03。

- **自動では実行しない。** `onsa_tests` のランナーは `tests/spec`、`tests/conformance`、`tests/golden` だけを読む。パッケージの収集も `tests/` を除く（§15.1）。
- 多くは「今の実装が誤る」入力で、期待値は各ファイルのコメントか `assert` に書いてある。修正の段階（レビュー §7）で、直した項目の入力を `tests/spec` などの回帰テストへ移す。
- 除いたもの: ビルドの生成物（`target/`）、実行ファイル、golden の写し、ファズが生成した約 830 個の入力。

## ディレクトリ

| ディレクトリ | 内容 | 担当した領域 |
|---|---|---|
| `syntax/` | 字句・構文・fmt・診断 | R-01、R-42〜R-46、R-58、R-59、R-62、R-69〜R-73、R-78、R-101、R-102 |
| `types/` | モジュール・名前解決・型・シグネチャ | R-02、R-30、R-35〜R-40、R-44、R-46、R-47、R-50、R-51、R-56、R-57、R-61、R-68、R-103〜R-105 |
| `body/` | 関数本体の型検査・引数モード・効果・rt | R-03、R-25〜R-34、R-51〜R-55、R-74、R-94〜R-96 |
| `flow/` | flow の検査・降下・状態の配置 | R-03、R-13〜R-17、R-22、R-41、R-48、R-99、R-100 |
| `core/` | Core IR・インタプリタ | R-04〜R-08、R-19、R-20、R-45、R-48、R-60、R-93 |
| `cback/` | C バックエンド・`onsa.h`・`onsa build` | R-09〜R-12、R-15、R-21、R-47、R-48、R-64〜R-67、R-93、R-109 |
| `parent/` | 親（まとめ役）が自分で再現したもの | 下の表 |

## 主な対応

担当の報告にファイル名が出ているものは、その対応を書いた。`syntax/` と、名前の後に「（推定）」と書いたものは、ファイル名から対応付けた。

| ファイル | R |
|---|---|
| `body/r1_rt_fnvalue.onsa` | R-26 |
| `body/r2_effect_fnvalue.onsa`、`body/ev1.onsa` | R-27 |
| `body/m1_continue.onsa`〜`body/m4_while_cond.onsa` | R-28 |
| `body/m5_for_move.onsa`、`body/m5b_for_move_once.onsa` | R-29 |
| `body/q1_qdup.onsa`、`body/q2_qdup_copy.onsa`、`types/kindfb*.onsa` | R-30 |
| `body/x1_slice_alias.onsa`、`body/s1_planar.onsa`、`body/s2_slice_inout.onsa` | R-31 |
| `body/g1_generic_drop.onsa`、`body/r3_rt_temp_drop.onsa`、`body/r4_branch_drop.onsa`、`body/e1_temp_drop_nonrt.onsa` | R-32 |
| `body/m6_closure_local.onsa` | R-33 |
| `body/a1_tuple_arg.onsa` | R-34 |
| `body/c1_capture_assign.onsa` | R-25 |
| `body/t2_neg_generic.onsa` | R-03、R-94 |
| `body/p1_pat_range.onsa`、`body/l1_strpat.onsa`、`body/u1_unresolved.onsa` | R-03 |
| `body/i1_generic_lit.onsa` | R-53 |
| `body/b1_let_borrow_affine.onsa` | R-54 |
| `body/t1_cmp_lit.onsa` | R-55 |
| `body/n1_newtype.onsa`、`types/newtype*.onsa` | R-51 |
| `body/d1_while_true.onsa` | R-52 |
| `body/pm1_partial.onsa` | R-74、R-95 |
| `body/b2_builtin_methods.onsa` | R-96 |
| `flow/e1/` | R-13 |
| `flow/e2/`、`flow/e17/` | R-14（`e2` は R-06 の `match` も） |
| `flow/e4/` | R-17 |
| `flow/e5/` | R-03（`par` の中の look-back） |
| `flow/e8/`、`flow/e9/`、`flow/e18/` | R-15 |
| `flow/e10/` | R-03（自分をインスタンスにする flow） |
| `flow/e11/` | R-22 |
| `flow/e12/` | R-41 |
| `flow/e13/` | R-100、R-03 |
| `flow/e6/`、`flow/e14/` | R-48 |
| `flow/e16/` | R-99 |
| `flow/pkg1/` | R-16 |
| `core/u64b.onsa`、`core/u64c.onsa` | R-04 |
| `core/deep_*.onsa` | R-05 |
| `core/guard*.onsa`、`core/match3.onsa`（推定） | R-06 |
| `core/ret.onsa` | R-07 |
| `core/try1.onsa`、`core/try2.onsa` | R-08 |
| `core/euclid.onsa` | R-19 |
| `core/constf.onsa` | R-20 |
| `core/order*.onsa`、`core/cpkg/` | R-93 |
| `core/fnmangle.onsa`、`core/mangle/` | R-48 |
| `core/derive*.onsa`（推定） | R-60 |
| `cback/p1/` | R-10、R-11、R-48、R-93 |
| `cback/p2/` | R-09、R-48 |
| `cback/p3/` | R-47、R-64 |
| `cback/p4/` | R-12、R-21 |
| `cback/p5/`、`cback/p13/` | R-48 |
| `cback/p6/` | R-66 |
| `cback/p8/` | R-09、R-109 |
| `cback/p10/` | R-11 |
| `cback/p11/` | R-15、R-48 |
| `cback/p12/` | R-93 |
| `cback/p14/` | R-10 |
| `cback/fma.c` | R-67 |
| `cback/voice_host/host.cpp` | R-65 |
| `types/rec*.onsa`、`types/constcyc*.onsa` | R-02 |
| `types/derive2.onsa` | R-35 |
| `types/attrs.onsa` | R-36 |
| `types/bounds.onsa`、`types/bufelem.onsa`、`types/span*.onsa`、`types/nestrate.onsa`、`types/ratefn.onsa`、`types/tyb*.onsa`（推定） | R-37 |
| `types/fieldvis/` | R-38 |
| `types/cyc2/`、`types/cyc3/`、`types/reexp/` | R-39 |
| `types/dups.onsa` | R-40 |
| `types/implitems.onsa`、`types/flowimpl.onsa` | R-44 |
| `types/dupmod/`、`types/itemmod/`、`types/stdname/`、`types/stdmod/`、`types/upname/`（推定） | R-46 |
| `types/single/`、`types/pkguse/`（推定） | R-47 |
| `types/flowimp/`、`types/useorder*.onsa`（推定） | R-50 |
| `types/tzero.onsa` | R-56 |
| `types/qlen/`、`types/constlen.onsa` | R-57、R-61 |
| `types/testmod/`（推定） | R-68 |
| `types/localshadow.onsa`、`types/shadow.onsa` | R-103 |
| `types/orphan/`、`types/implspec.onsa` | R-104（`orphan/` の期待値は `main.onsa` の先頭のコメント。S-70） |
| `types/alias.onsa` | R-105 |
| `syntax/esc_utf8.onsa`、`syntax/interp_utf8.onsa` | R-01 |
| `syntax/fmt_drop*.onsa` | R-69 |
| `syntax/fmt_comments.onsa`、`syntax/fmt2.onsa`（fmt の前の原本は `.orig`） | R-70 |
| `syntax/cascade.onsa`、`syntax/impl_errs.onsa`、`syntax/impl_sema.onsa` | R-71 |
| `syntax/groups.onsa` | R-72 |
| `syntax/lit.onsa` | R-73 |
| `syntax/tup1.onsa`、`syntax/tuples.onsa` | R-43 |
| `syntax/moveargs.onsa`、`syntax/paren_move.onsa` | R-42 |
| `syntax/nested*.onsa` | R-44 |
| `syntax/bigfloat.onsa` | R-45 |
| `syntax/my-mod.onsa`、`syntax/MyMod.onsa`、`syntax/naming.onsa`、`syntax/modpkg/` | R-46 |
| `syntax/arrow.onsa` | R-58 |
| `syntax/faust.onsa` | R-59 |
| `syntax/else_paren.onsa` | R-62 |
| `syntax/unit*.onsa`、`syntax/emptyrow.onsa` | R-78 |
| `syntax/ret_arm.onsa`、`syntax/space_idx.onsa` | R-101 |
| `syntax/interp.onsa` | R-102 |
| `syntax/fuzz.py`、`syntax/fuzz2.py` | 変異入力の簡易ファズ（R-01 の確認、Q-06 の参考） |
| `parent/r1.onsa` | R-01 |
| `parent/t2.onsa` | R-02 |
| `parent/r2.onsa` | R-69 |
| `parent/r4.onsa` | R-72 |
| `parent/t1.onsa` | R-30 |
| `parent/p2/` | R-09 |
| `parent/r13*.onsa` | R-13（`prev(prev(x))` を含む） |
| `parent/r15*.onsa` | R-15 |
| `parent/r17.onsa` | R-17 |
| `parent/r18.onsa` | R-18 |
| `parent/r19.onsa` | R-19 |
| `parent/r54.onsa`、`parent/r54_for.onsa` | R-54（S-41） |
| `parent/r117.onsa` | R-117 |
| `parent/r118.onsa` | R-118 |
| `parent/r55.onsa` | R-55（範囲を広げた再現） |
| `parent/r119.onsa` | R-119 |
| `parent/r120.onsa` | R-120 |
| `parent/r61.onsa` | R-61（計算で決まる定数を長さに使う） |
| `parent/r62.onsa` | R-62（括弧・腕の中の `else` と `{` の位置） |
| `parent/r70/` | R-70（コメントの位置の 17 の形。どれも正規形で書いてあり、fmt で変わらないのが期待値。S-58） |
| `parent/r71/` | R-71（回復と診断の単位の 6 つの形。期待値は各ファイルの先頭のコメント。S-59） |
| `parent/r72.onsa` | R-72、R-123（E0010 の修正候補とビットの群の連鎖。期待値は各関数の上のコメント。S-60、S-61） |
| `parent/r73.onsa` | R-73、R-124（数値リテラル。期待値は各関数の上のコメント。S-62、S-63） |
| `parent/r74.onsa` | R-74（modes の失敗の後の rt と効果。期待値は各関数の上のコメント。S-64） |
| `parent/r75/` | R-75（`onsa interface` の大きさと状態のフィールド。仕様の構文で書いたパッケージで、期待値は `dsp.onsa` の先頭のコメント。S-65） |
| `parent/r76.onsa` | R-76（`onsa graph` の `par` の添字の閉路。期待値は先頭のコメント。S-66） |
| `parent/r77.onsa` | R-77（降下の診断の繰り返し、内部エラー、入力名の予約名。期待値は各項目の上のコメント。S-67） |
| `parent/r78.onsa` | R-78（意味を変えない余分な情報。fmt が取り除くのが期待値で、各関数の上のコメントに書いた。S-68） |
| `parent/r79/` | R-79（std の `target` 宣言を変換先が与えないとき。期待値は `m.onsa` の各項目の上のコメント。S-69） |
| `parent/r79_enum.onsa` | R-79、R-53（Option / Result と利用者の総称の enum の推論の食い違い。期待値は先頭のコメント。S-71） |
| `parent/r80/` | R-80（NRVO の判定の食い違い。`onsa build --target host .` の生成コードで確かめる。期待値は `m.onsa` の先頭のコメント） |
| `parent/r83.onsa` | R-83（効果の使用の診断。期待値と今の出力は各関数の上のコメント。S-77） |
| `parent/r84.onsa`、`parent/r84_type.onsa` | R-84、R-103（名前の段と名前の隠蔽。期待値と今の出力は各項目の上のコメント。S-78、S-79） |
| `parent/r85.onsa` | R-85（束縛の状態。期待値と今の出力は各関数の上のコメント。S-80） |
| `parent/r87.onsa` | R-87（修正候補の形と診断を置く位置。`onsa check --json` で確かめる。期待値と今の出力は各関数の上のコメント。S-81、S-82） |
| `parent/r88/` | R-88（std の版の固定。期待値は `onsa.toml` の先頭のコメント。S-83） |
| `parent/r93.onsa` | R-93、R-81（評価順。S-75 の期待値で書いたテストで、今の結果は各テストの上のコメント） |
| `parent/r94/` | R-94、R-131（数の trait の形。`check.onsa` は `onsa check`、`run.onsa` は `onsa test` で確かめる。期待値と今の出力は各項目の上のコメント。S-84） |
| `parent/r95.onsa` | R-95（Affine のフィールドの取り出し。期待値と今の出力は各項目の上のコメント。S-85） |
| `parent/r98.onsa` | R-98（名前の無いノードの名前と配置。今の実装の構文で書いた。`onsa interface` と `onsa graph` で確かめる。期待値と今の出力は先頭のコメント。S-86） |
| `parent/r99.onsa` | R-99（`@param` の値型と値。期待値と今の出力は各 flow の上のコメント。S-87） |
| `parent/r100/` | R-100（`delay.onsa` は `vdelay` の `MAX` と `F32`、`check` と `test` で確かめる。`size.onsa` は大きさの上限、`interface` で確かめる。期待値と今の出力は各項目の上のコメント。S-88） |
| `parent/r101/` | R-101（字句と fmt の細則。形ごとのファイルで、`align.onsa` は `onsa fmt`、他は `onsa check` で確かめる。期待値と今の出力は各ファイルの先頭のコメント。S-89） |
| `parent/r102.onsa` | R-102（補間の範囲。期待値と今の出力は各関数の上のコメント。S-90） |
| `parent/r105/` | R-105（型別名。`alias.onsa`・`generic.onsa`・`cycle.onsa` は `onsa check`、`impl/` は別名を通した孤児規則のパッケージ。期待値と今の出力は各項目の上か `onsa.toml` の先頭のコメント。S-91） |
| `parent/r107/` | R-107（C の生成 API と設定。パッケージで、`onsa build --target host` と `--target bare` の生成物で確かめる。期待値と今の出力は `m.onsa` の先頭のコメント。S-92） |
| `parent/r108/` | R-108（`const` の評価の超越関数。パッケージで、二台の機械で `onsa build --target src` の生成した C の表を比べる。手順と期待値は `m.onsa` の先頭のコメント。S-93） |
| `parent/r109/` | R-109（生成した C の `const` と別名の規則。パッケージで、生成した C を clang の `-Wall -Wextra -Werror` でコンパイルする。手順と期待値は `m.onsa` の先頭のコメント。S-94） |
| `parent/r121/` | R-121（C の API の名前空間と ABI の版。`pa` と `pb` は既定の prefix の二つのパッケージで、`host.c` から両方をリンクする。`onsa` は空の prefix とパッケージ名 `onsa`、`rt` はランタイムの名前と重なる関数。手順・期待値・今の出力は `host.c` と各 `onsa.toml` の先頭のコメント。S-95） |
| `parent/r128.onsa` | R-128（`Num` / `Float` は `Copy` を満たす。期待値は先頭のコメント。S-73） |
| `parent/r129.onsa` | R-129（効果の名前の解決。期待値は各関数の上のコメント。S-74） |
| `parent/r130/` | R-130（マニフェストの未知のキー。期待値は `onsa.toml` の先頭のコメント） |

対応が書かれていないファイル（`body/p01_multi.onsa`、`body/tr1_trait.onsa`、`core/` と `types/` の一部など）は、内容とレビュー文書の項目を見て対応を確かめる。

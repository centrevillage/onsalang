# M0〜M4 のコードレビューの再現の入力

[`docs/review-impl-phase1.md`](../../docs/review-impl-phase1.md)（R-01〜R-133）と `impl-review-0.3.md` の持ち越しの項目の指摘と、決定の点検（`consistency-check-phase1.md`）で見つけた穴を再現した入力を、資料として残したもの。2026-10-02〜06。

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
| `body/l1_strpat.onsa` | R-03。W3-21/t で期待値付きのテストへ移した: `tests/spec/negative/pattern_str.onsa`（補間を含む文字列のパターン E0020。候補の形は `crates/onsa_cli/tests/pattern_guard_candidates.rs`） |
| `body/p1_pat_range.onsa`、`body/u1_unresolved.onsa` | R-03。W2-06 で期待値付きのテストへ移した: `tests/spec/negative/pattern_range.onsa`（パターンのリテラルの範囲 E0408 と符号なしの `-1` の E0401）、`tests/spec/negative/infer_unresolved.onsa`（関数の終わりに残る型変数の E0406。`Buf.zeroed(4)` と `None` は作った式に出す、S-226） |
| `body/i1_generic_lit.onsa` | R-53 |
| `body/b1_let_borrow_affine.onsa` | R-54 |
| `body/t1_cmp_lit.onsa` | R-55 |
| `body/n1_newtype.onsa`、`types/newtype*.onsa` | R-51 |
| `body/d1_while_true.onsa` | R-52 |
| `body/pm1_partial.onsa` | R-74、R-95 |
| `body/b2_builtin_methods.onsa` | R-96 |
| `flow/e1/` | R-13 |
| `flow/e2/`、`flow/e17/` | R-14（`e2` は R-06 の `match` も）。S-110 で規則を改めたので、期待は各ファイルの先頭のコメント |
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
| `core/u64b.onsa`、`core/u64c.onsa` | R-04。W2-03 で期待値付きのテストへ移した: `tests/spec/semantics/u64_mul_contexts.onsa`・`u64_mul_const.onsa`・`wrapping_mul_u64.onsa`、`crates/onsa_interp/src/tests.rs` の `u64_products_beyond_i128` |
| `core/deep_*.onsa` | R-05。W2-04 で期待値付きのテストへ移した: `crates/onsa_tests/tests/interp_stack.rs` の `r05_recursion_below_the_limit_passes_in_onsa_test`（同じ `depth(n)` を `onsa test` の経路で走らせる）、`crates/onsa_cli/tests/deep_recursion.rs`（シグナルでなく終了コード 1）、`tests/spec/semantics/recursion_deep.onsa`・`recursion_limit.onsa`・`recursion_shallow.onsa`。上限は 128（S-222）で、`test` の本体から `depth(n)` は n + 1 段の呼び出しなので、`deep_50.onsa`・`deep_100.onsa` は通り、`deep_200.onsa` から `deep_5000.onsa` と `deep.onsa` の深い `test` は、その `test` の失敗（panic）が期待値 |
| `core/const_chain_cold.onsa` | R-153（`const` の鎖が長く、各初期化式が深く再帰すると、安全網の内部エラーで止まり、合否が読む順で変わる。W9-03） |
| `core/guard*.onsa`、`core/match3.onsa`（推定） | R-06。W2-07 で期待値付きのテストへ移した: `tests/spec/semantics/match_value_forms.onsa`（値の `match` の各形の値。W8-06 まで実装待ち）、`tests/spec/negative/lower_match_general.onsa`（それまでの E0200）、`tests/spec/semantics/match_kept_forms.onsa`（止めない形）。今はどれも E0200 で止まる（`flow/e2/` の `match` も） |
| `core/ret.onsa` | R-07。W2-07 で直し、`tests/spec/semantics/return_unit.onsa` へ移した |
| `core/try1.onsa`、`core/try2.onsa` | R-08。W2-07 で期待値付きのテストへ移した: `tests/spec/semantics/closure_exit_from_fn.onsa`（脱出の値。W8-09 まで実装待ち）、`tests/spec/negative/lower_closure_exit.onsa`（それまでの `?` と `return` の E0200） |
| `core/euclid.onsa` | R-19。W2-03 で期待値付きのテストへ移した: `tests/spec/semantics/min_rem_neg1.onsa`、`crates/onsa_interp/src/tests.rs` の `min_rem_minus_one_is_zero`（仕様 §3.4 では `MIN % -1` と `MIN.rem_euclid(-1)` は 0 で panic しない。ファイルの test の名前の「panics」は決定の前のもの）。元の入力は旧い期待値のまま失敗するので消した（W2-06 のコミット、W2-03/b の F-6） |
| `core/constf.onsa` | R-20 |
| `core/order*.onsa`、`core/cpkg/` | R-93 |
| `core/fnmangle.onsa`、`core/mangle/` | R-48 |
| `core/derive*.onsa`（推定） | R-60 |
| `cback/p1/` | R-10、R-11、R-48、R-93。R-10 と R-11 の部分（`narrow_u32`、`shr_i8` / `shr_i16`、`wmul_u16` / `wmul_i16`、`cmul_u32`、`sat_i64` / `sat_u64`）は W2-05 で期待値付きのテストへ移した: テストベクトル（`tests/vectors/` の `u32.narrow_i32`、`i8.shr`、`i16.shr`、`u16.wmul`、`i16.wmul`、`u32.checked_mul`、`f64.trunc_i64_sat`、`f64.trunc_u64_sat` などを gate の `vectors-c` が全てのツールチェーンで）、`tests/spec/c_runtime/` の `c_narrow_u2s.onsa`・`c_shift.onsa`・`c_mul.onsa`・`c_trunc.onsa`・`c_int_modules/` |
| `cback/p2/` | R-09、R-48 |
| `cback/p3/` | R-47、R-64 |
| `cback/p4/` | R-12、R-21 |
| `cback/p5/`、`cback/p13/` | R-48 |
| `cback/p6/` | R-66 |
| `cback/p8/` | R-09、R-109 |
| `cback/p10/` | R-11。W2-05 で期待値付きのテストへ移した: テストベクトルの `u32.narrow_i8`〜`u64.narrow_i64`（`vectors-c`）、`tests/spec/c_runtime/c_narrow_u2s.onsa`、`crates/onsa_backend_c/src/tests.rs` の `narrow_from_unsigned_compares_the_upper_bound_alone`。符号付きから符号無しへは `c_narrow_s2u.onsa`（-Werror の警告は W2-09） |
| `cback/p11/` | R-15、R-48 |
| `cback/p12/` | R-93 |
| `cback/p14/` | R-10。W2-05 で期待値付きのテストへ移した: テストベクトルの `u32.mul`・`u32.smul`・`u32.checked_mul`（`vectors-c` の `c-gcc` が、gcc の -O2 で消えていた検査を確かめる）、`tests/spec/c_runtime/c_mul.onsa` |
| `cback/fma.c` | R-67。W2-09/t で期待値付きのテストへ移した: `tests/spec/c_runtime/c_fp_contract.onsa`（FMA で値が変わる行。全ての C の検査が -ffp-contract=off の下で）、`c_fp_relaxed.onsa`・`c_fp_flow.onsa`（緩和した関数や flow の前後の厳密な関数）、`crates/onsa_tests/tests/c_fp_flags.rs`（GNU モードの gcc・fast-math・FLT_EVAL_METHOD の `#error`、`ONSA_ALLOW_INEXACT_FP`、STDC のプラグマ、公開と内部のヘッダ、フラグなしの GCC / Clang での結果）。W2-09 で実装し、この再現（`cback/fma.c`）を消した |
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
| `types/testmod/`（推定） | R-68。W2-10 で期待値付きのテストへ移した: `tests/spec/packages/test_module_named_test/`（モジュール `test` の関数はテストとして走らない）、`crates/onsa_cli/tests/test_identity.rs`（モジュールの経路と名前での識別） |
| `types/localshadow.onsa`、`types/shadow.onsa` | R-103 |
| `types/orphan/`、`types/implspec.onsa` | R-104（`orphan/` の期待値は `main.onsa` の先頭のコメント。S-70） |
| `types/alias.onsa` | R-105 |
| `syntax/esc_utf8.onsa`、`syntax/interp_utf8.onsa` | R-01 |
| `syntax/fmt_drop*.onsa` | R-69。`fmt_drop_orig.onsa` は W3-03 で期待値付きのテストへ移して消した（`crates/onsa_cli/tests/syntax_units.rs` の `FMT_DROP`） |
| `syntax/fmt_comments.onsa`、`syntax/fmt2.onsa`（fmt の前の原本は `.orig`） | R-70 |
| `syntax/cascade.onsa`、`syntax/impl_sema.onsa` | R-71。`impl_errs.onsa` は W3-03 で期待値付きのテストへ移して消した（`tests/spec/negative/unit_members.onsa`） |
| `syntax/groups.onsa` | R-72 |
| `syntax/lit.onsa` | R-73 |
| `syntax/tup1.onsa`、`syntax/tuples.onsa` | R-43。W3-20 で期待値付きのテストへ移した: `tests/spec/negative/syntax_one_tuple.onsa`（要素 1 個の後の `,` の E0002）、`tests/spec/semantics/paren_group.onsa`（式・型・パターンの `(e)` はグループ化） |
| `syntax/moveargs.onsa`、`syntax/paren_move.onsa` | R-42。W3-20 で期待値付きのテストへ移した: `tests/spec/negative/syntax_move_operand.onsa` |
| `syntax/nested*.onsa` | R-44 |
| `syntax/bigfloat.onsa` | R-45 |
| `syntax/my-mod.onsa`、`syntax/MyMod.onsa`、`syntax/naming.onsa`、`syntax/modpkg/` | R-46 |
| `syntax/arrow.onsa` | R-58 |
| `syntax/faust.onsa` | R-59 |
| `syntax/else_paren.onsa` | R-62 |
| `syntax/unit*.onsa`、`syntax/emptyrow.onsa` | R-78 |
| `syntax/ret_arm.onsa`、`syntax/space_idx.onsa` | R-101 |
| `syntax/interp.onsa` | R-102 |
| `syntax/fuzz.py`、`syntax/fuzz2.py` | 変異入力の簡易ファズ（R-01 の確認、Q-06 の参考）。`fuzz.py` は W1-04 の `tools/fuzz.py`（gate の項目 `fuzz`）に置き換えた。記録として残す。`fuzz2.py`（fmt の AST の保存）は W1-07 の `tools/fmt_props.py`（gate の項目 `fmt-props`）に置き換えた。どちらも記録として残す |
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
| `parent/r19.onsa` | R-19。W2-03 で期待値付きのテストへ移した: `tests/spec/semantics/trunc_range.onsa`・`trunc64_edges.onsa`・`trunc64_range_contexts.onsa`・`min_rem_neg1.onsa`、`crates/onsa_interp/src/tests.rs` の `trunc_to_64_bits_at_the_powers_of_two`。元の入力は旧い期待値のまま失敗するので消した（W2-06 のコミット、W2-03/b の F-6） |
| `parent/r54.onsa`、`parent/r54_for.onsa` | R-54（S-41） |
| `parent/r117.onsa` | R-117 |
| `parent/r118.onsa` | R-118 |
| `parent/r55.onsa` | R-55（範囲を広げた再現） |
| `parent/r119.onsa` | R-119 |
| `parent/r120.onsa` | R-120 |
| `parent/r61.onsa` | R-61（計算で決まる定数を長さに使う） |
| `parent/r62.onsa` | R-62（括弧・腕の中の `else` と `{` の位置） |
| `parent/r70/` | R-70（コメントの位置の 17 の形。どれも正規形で書いてあり、fmt で変わらないのが期待値。S-58） |
| `parent/r71/` | R-71（回復と診断の単位の 6 つの形。S-59）。W3-03 で期待値付きのテストへ移して消した: `tests/spec/negative/unit_members.onsa`（`a_impl`）、`unit_failed_visible.onsa`（`b_body`、`d_sig`、`f_struct`）、`unit_unclosed_brace.onsa`（`c_brace`）、`unit_syntax_hides_later.onsa` と `unit_stage_order.onsa`（`g_naming_then_syntax`） |
| `parent/r72.onsa` | R-72、R-123（S-60、S-61）。W3-07 で期待値付きのテストへ移した: `tests/spec/fixes/e0010_candidates.onsa`・`e0010_candidates_groups.onsa`・`e0010_candidates_contexts.onsa`・`e0010_layout.onsa`・`e0010_nesting_boundary.onsa`（E0010 の修正候補）、`tests/spec/ops/groups.onsa`・`tests/spec/semantics/precedence_trees.onsa`（ビットの群の同じ演算子の連鎖）、`crates/onsa_cli/tests/operator_groups.rs` の `the_candidates_of_e0010_are_the_readings_in_the_order_of_the_rule` ほか（候補の順と文面） |
| `parent/r73.onsa` | R-73、R-124（数値リテラル。期待値は各関数の上のコメント。S-62、S-63） |
| `parent/r74.onsa` | R-74（modes の失敗の後の rt と効果。期待値は各関数の上のコメント。S-64） |
| `parent/r75/` | R-75（`onsa interface` の大きさと状態のフィールド。仕様の構文で書いたパッケージで、期待値は `dsp.onsa` の先頭のコメント。S-65） |
| `parent/r76.onsa` | R-76（`onsa graph` の `par` の添字の閉路。期待値は先頭のコメント。S-66） |
| `parent/r77.onsa` | R-77（降下の診断の繰り返し、内部エラー、入力名の予約名。期待値は各項目の上のコメント。S-67）。W1-04 で期待値付きの事例へ移した: `tests/spec/negative/lower_unsupported.onsa`、`names_reserved_inputs.onsa`（W7-03 の実装待ち） |
| `parent/r78.onsa` | R-78（意味を変えない余分な情報。fmt が取り除くのが期待値で、各関数の上のコメントに書いた。S-68） |
| `parent/r79/` | R-79（std の `target` 宣言を変換先が与えないとき。期待値は `m.onsa` の各項目の上のコメント。S-69） |
| `parent/r79_enum.onsa` | R-79、R-53（Option / Result と利用者の総称の enum の推論の食い違い。期待値は先頭のコメント。S-71） |
| `parent/r80/` | R-80（NRVO の判定の食い違い。`onsa build --target host .` の生成コードで確かめる。期待値は `m.onsa` の先頭のコメント） |
| `parent/r83.onsa` | R-83（効果の使用の診断。期待値と今の出力は各関数の上のコメント。S-77） |
| `parent/r84.onsa`、`parent/r84_type.onsa` | R-84、R-103（名前の段と名前の隠蔽。期待値と今の出力は各項目の上のコメント。S-78、S-79） |
| `parent/r85.onsa` | R-85（束縛の状態。期待値と今の出力は各関数の上のコメント。S-80） |
| `parent/r87.onsa` | R-87（修正候補の形と診断を置く位置。`onsa check --json` で確かめる。期待値と今の出力は各関数の上のコメント。S-81、S-82）。候補の形（S-81、R-87 (1)(2)）は W3-02 で直した。残りの E0320 の全ての使用箇所は W4-04、E0601 の位置は W6-03 で、期待値は `tests/spec/fixes/e0320_rename.onsa`・`pkg_rename/`・`e0601_alloc_row.onsa`（実装待ち） |
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
| `parent/r109/` | R-109（生成した C の `const` と別名の規則。パッケージで、生成した C を clang の `-Wall -Wextra -Werror` でコンパイルする。手順と期待値は `m.onsa` の先頭のコメント。S-94）。W1-06 で期待値付きの事例 `tests/pipeline/span_const.onsa`（gate の C の項目の実装待ち、W10-04）にした。W10-04 で直したら、この再現の入力を消す |
| `parent/r121/` | R-121（C の API の名前空間と ABI の版。`pa` と `pb` は既定の prefix の二つのパッケージで、`host.c` から両方をリンクする。`onsa` は空の prefix とパッケージ名 `onsa`、`rt` はランタイムの名前と重なる関数。手順・期待値・今の出力は `host.c` と各 `onsa.toml` の先頭のコメント。S-95） |
| `parent/r122/` | R-122（パッケージの `tests/` の役割。`onsa check` と `onsa test` で確かめる。`tests/api.onsa` はルート直下の `tests/`、`dsp/tests/n.onsa` はルート直下でない `tests/`。期待値と今の出力は各ファイルの先頭のコメント。S-96） |
| `parent/r125.onsa` | R-125（std のテスト用の補助を呼べる場所。`onsa check` と `onsa test` で確かめる。期待値と今の出力は各項目の上のコメント。S-97） |
| `parent/r126.onsa` | R-126（組込みのメソッドの一覧。`onsa check` で確かめる。期待値と今の出力は各項目の上のコメント。S-98） |
| `parent/p7.onsa` | `impl-review-0.3.md` の P-7（ブロックの末尾の式の `move`。期待値と今の出力は各関数の上のコメント。S-100）。構文は W3-20 で期待値付きのテストへ移した: `tests/spec/values/move_tail_syntax.onsa`、`crates/onsa_cli/tests/call_forms_syntax.rs`（返り値の位置の `move`）。検査（E0711、E0703、E0704）は W4-09 |
| `parent/t5.onsa` | `impl-review-0.3.md` の T-5（flow だけの構文を flow の外に書いたときの診断。期待値と今の出力は各関数の上のコメント。S-101。レート型の部分は S-102） |
| `parent/t8.onsa` | `impl-review-0.3.md` の T-8 と R-105 の残り（診断コードの流用。期待値と今の出力は各項目の上のコメント。S-103） |
| `parent/param_id/` | `impl-review-0.3.md` の §11.7 `id`（パラメータの ID の作り方。パッケージで、`onsa build --target host` の生成した C の表で確かめる。期待値と今の出力は `m.onsa` の先頭のコメント。S-104） |
| `parent/strict_ftz/` | `impl-review-0.3.md` の §13.4 `strict-ftz`（FTZ / DAZ の設定。パッケージで、`onsa build --target host` の生成した C を確かめる。期待値と今の出力は `m.onsa` の先頭のコメント。S-105） |
| `parent/r133/` | R-133（NaN のビット表現。パッケージで、`onsa test` と、生成した C を arm64 / x86_64 / gcc-15 でコンパイルした `host.c` で確かめる。手順と期待値と今の出力は `m.onsa` の先頭のコメント。S-106）。W2-03（インタプリタ）と W2-05（C）で期待値付きのテストへ移した: テストベクトルの `f32.to_bits`・`f64.to_bits`（`vectors-interp`、`vectors-c` の clang・gcc-15・x86_64）、`tests/spec/c_runtime/c_nan_bits.onsa`、`crates/onsa_interp/src/tests.rs` の `to_bits_of_a_nan_is_the_positive_quiet_nan` |
| `parent/r128.onsa` | R-128（`Num` / `Float` は `Copy` を満たす。期待値は先頭のコメント。S-73） |
| `parent/r129.onsa` | R-129（効果の名前の解決。期待値は各関数の上のコメント。S-74） |
| `parent/r130/` | R-130（マニフェストの未知のキー。期待値と今の出力は `onsa.toml` の先頭のコメント。S-99） |
| （R-132） | 専用の入力は無い。レートを型の形で書いたときの診断は `parent/t5.onsa`（S-102） |
| `parent/c119.onsa` | 点検 C-119 と C-12（行頭の `- b` で関数が `-b` を返す。期待値と今の出力は先頭のコメント。S-127、S-124、S-123） |
| `parent/c120.onsa` | 点検 C-120（行末の `return` の次の行が黙って実行されない。期待値と今の出力は先頭のコメント。S-128） |
| `parent/c121.onsa` | 点検 C-121（flow の使われない `let` と、行頭の `- prev` が黙って出力になる。期待値と今の出力は先頭のコメント。S-129） |

対応が書かれていないファイル（`body/p01_multi.onsa`、`body/tr1_trait.onsa`、`core/` と `types/` の一部など）は、内容とレビュー文書の項目を見て対応を確かめる。

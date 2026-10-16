# Onsa 実装計画: 作業の詳細

- 対象: [`implementation-plan.md`](implementation-plan.md) の M0〜M9 を、着手できる作業の単位に分けたもの。方針（§0）、クレート構成（§1）、中核の設計判断（§2）はそちらに従い、ここでは繰り返さない
- 仕様: [`spec/`](../spec/README.md)（節番号は 0.3 のもの）
- 日付: 2026-10-01
- ID の種類
  - `T<M>-<n>`: 作業。マイルストーン M の n 番目。規模は S（1〜2 日）/ M（3〜5 日）/ L（1〜2 週）の目安
  - `D-nn`: **実装の判断**。仕様が決めていない、実装の側の選択。提案と理由を書く
  - `S-nn`: **仕様の空白**。作業を切り出すときに見つかった小さな未定義。決定後に仕様 0.3 へ反映する

`D` は 2026-10-01 に全て決定した（案の通り）。`S` は 2026-10-02 に全て決定し（S-15 は取り下げ）、仕様へ反映した（[`onsa-0.3-changes.md`](onsa-0.3-changes.md) §4）。新しい空白が見つかれば、続きの番号（今は S-173）から振る。

---

## 0. 見取り図

| M | 成果 | 利用者が確認できること | 規模 |
|---|---|---|---|
| M0 | 基盤 | `onsa check --json empty.onsa` が `[]`、CI が緑 | S |
| M1 | 字句・構文・fmt | 仕様の全ての例が解析でき、`fmt` が冪等 | M |
| M2 | 名前解決・核の型検査 | §17.6 `Poly` を含む核の例が `check` を通り、否定例が所定のコードで落ちる | L |
| M3 | flow の検査・降下、インタプリタ | `onsa test` で §17.3 `resonator decays` が通る。`interface` と `graph` | L |
| M4 | C バックエンドと export | §17.5 の C ホストがビルドでき、`voice` が interp とビット一致 | L |
| M5 | std と適合性テスト | `std.math` の精度、`--backends all`、`--flows` | M |
| M6 | WASM | ブラウザで `voice` が鳴る。3 者一致 | M |
| M7 | IDE の核 | VS Code で診断とホバー、`play`、`probe` | L |
| M8 | JS | 4 者一致 | M |
| M9 | 締め | `explain` 全コード、`audit` | S |

依存: M0 → M1 → M2 → M3 → M4 → M5 → M6 → M7。M8 は M6 の後、M9 は M7 の後。M4 の完了が第 1 期の最初の区切り（計画 §6）。

M3 で `resonator` を動かすには `exp` / `cos` が要るので、`std.math` の **宣言とインタプリタの対応付け** は M3 に入れ、M5 では精度の測定と差し替えだけを行う。

---

## 1. 実装の判断（D）

全て 2026-10-01 に案の通り決定。D-01〜D-16 は `decisions/D/` に移した（[`decisions/D/README.md`](../decisions/D/README.md) から読む）。

---

## 2. 仕様の空白（S）

`decisions/S/` に移した（[`decisions/S/README.md`](../decisions/S/README.md) から読む）。

---

## 3. 共通の設計

`design/` に移した（[`design/README.md`](../design/README.md) から読む）。

---

## 4. 作業

### M0 基盤（S）

| ID | 作業 | 場所 | 規模 |
|---|---|---|---|
| T0-1 | Cargo ワークスペースと全クレートの空の骨格、`rust-toolchain.toml`（stable）、`.gitignore` に `target/` を追加、`Cargo.lock` をコミット | ルート、`crates/*` | S |
| T0-2 | `onsa_diag`: §3.1 の型、D-04 の登録簿（この文書 §5 の全コードを登録。`explain` 本文は空でよい）、JSON と人間向けの出力、`LineIndex` | `onsa_diag` | S |
| T0-3 | `onsa_cli` の骨格: `onsa check [--json] <path...>`、`onsa explain <code>`。終了コード 0（診断なし）/ 1（診断あり）/ 2（使い方・I/O の誤り）。S-56 で全てのコマンドの規約（1 は問題が見つかった、2 は働けなかった、101 は内部エラー）に改めた | `onsa_cli` | S |
| T0-4 | `tests/spec` のランナー（D-05）: ファイルを集め、`//! mode:` とマーカを読み、`check` の結果と `(code, line)` の集合を比較する。`cargo test -p onsa_tests` で走る | `crates/onsa_tests` | S |
| T0-5 | D-06 の同期検査スクリプトと、仕様の 39 ブロックの収録（T1-11 の前倒し） | `tools/`, `tests/spec` | S |
| T0-6 | D-14 の `check` / `wasm` / `spec` ジョブ | `.github/workflows/ci.yml` | S |

受け入れ: `onsa check --json tests/spec/empty.onsa` が `[]` を出し、CI が緑。

### M1 字句・構文解析と fmt（M）

✅ は完了（2026-10-01）。構文解析の実装上の注記: 式の中の `a.b` は `Path` 1 要素 + `Field` の連鎖で表し、複数要素の `Path` は型・`use`・パターン・属性・struct リテラルにだけ現れる（名前解決が `Field(Path(voice), init)` をモジュールのパスに読み替える）。パターンの `-1` は `PatKind::Neg`。
E0320 は構文解析の後の独立した段（`naming.rs`）。`fmt` の実装上の規則（仕様の例から決めた）: 並び（引数・struct リテラル・配列）は、開き括弧の行に全要素が始まれば 1 行、開き括弧の直後で改行していればブロック形（字下げ + 末尾の `,` + 閉じ括弧は独立の行）、それ以外は最初の要素の下に揃える継続形（末尾の `,` なし）。
項目の間の空行は 0 か 1 を保つ（§15.2 の `target` の並びなど）。行末の二項演算子や行頭の `.` による継続行は 1 段深く字下げ。`let` の `=` と行末コメントの整列は常に行い（S-07）、仕様の例 10 ブロックをそれに合わせて直した（コードは不変）。式の途中のコメントは文の後ろに移る（仕様の例には無い。S-58 で、コメントは書いた位置に保つと改めた）。

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T1-1 ✅ | 字句解析器 | §2 の全トークン。キーワード（§2.2）。識別子の種別（`snake_case` / `UpperCamel` / `UPPER_SNAKE` / `_`）を字句の段で分類。整数（10 進・`0x`・`0b`・`_`）、浮動小数（小数点の両側に数字。`1.` / `.5` は E0020 の修正候補）、`'c'`、文字列（`{名前.フィールド}` の補間と `{{` `}}` を字句の段で分解）。`//` と `///`。`名前~(` と `名前!(`（識別子の直後、空白なし、直後が `(`）。`.` 直後の数字列はタプルの添字。改行は `Newline` トークンとして出す | M |
| T1-2 ✅ | AST | §3.2。全ノードにスパン、trivia の保持 | S |
| T1-3 ✅ | 宣言の構文解析 | 下の文法の `Item` 全部。属性（`@derive` `@repr` `@relaxed` `@deprecated` `@param`）、ドキュメントコメントの付属。`@derive` は S-34 で宣言の `: trait` に移し、`@relaxed` は S-57 で `@fp(relaxed)` に改め、`@deprecated` は仕様に無い（§6.5、R-36 の属性の表で検査する） | M |
| T1-4 ✅ | 文とブロック | 文の区切り（§2.5）: ブロックの中では `Newline` で文を終える。行末が二項演算子・`=`・`->`、または次の行が `.` で始まれば継続。括弧・角括弧・struct リテラル・`match` の腕の並びの中では `Newline` を読み飛ばす（文脈のスタック）。`else` の位置 E0003。ブロックの値（最後の式）。`let` のパターン、`var`、代入、`for ... in [move]`、`while`、`break` / `continue` / `return`、`assert` | M |
| T1-5 ✅ | 式 | 後置 > 前置 > `as` > 二項の結合。二項は平らな列として保持し、独立した段で群の検査 E0010（修正候補: 括弧の挿入）、E0011、E0012。struct リテラル（S-08 の制限）、配列 `[a, b]` / `[e; N]`、タプル、`if` / `else if`、`match` と腕、無名 `fn`、`handle { } with ...`、`unsafe { }`、`par i in a..b { }`、引数のモード（`inout x`、`move x`、`inout [a, b]`）、`?`、`_` | M |
| T1-6 ✅ | パターン | §7 の一覧。`\|` は パターンの文脈でだけ選択 | S |
| T1-7 ✅ | エラー回復 | 項目単位: エラーの後は次の行頭の項目キーワードまで読み飛ばす。関数の中では次の文まで。関数ごとに最初のエラーだけを報告（P-01）。S-59 で改めた: 回復と報告の単位は宣言（impl / trait のメンバを含む）、閉じていない `{` は字下げで回復点を推定、文の単位の回復は M7（T7-1） | S |
| T1-8 ✅ | 既存言語の書き方（E0020、S-02） | 検出する形と修正候補: `&mut x` / `&x` → `inout x` / `x`、`<T>` → `[T]`、`::` → `.`、行末の `;` → 削除、`i32 i64 u8 u32 u64 f32 f64 bool usize isize` → `I32 ...`（`usize` → `U32`）、`let mut` → `var`、`loop {` → `while true {`、`proc` → `flow`、`fn f<T>` / `impl<T>` → `[T]`、`mut self` → `inout self`、`#[derive(...)]` → `@derive(...)`、`..=` → 無い（`a..b + 1`）、`+ ~ _`（FAUST）→ `prev` の説明、`1.` / `.5` → `1.0` / `0.5`、`x = e` を flow の本体で → `let x = e`。後の決定で改めた（2026-10-06、点検 C-80）: `#[derive(X)]` と `@derive(X)` の候補は宣言の頭の `: X`（S-34）、`~ _` の候補は `prev~(^y)`（S-44、仕様 §18.1）、flow の本体の代入は E0806 で、`let` の候補は代入先が未定義のときだけ（定義済みなら note で `prev~(^y)` の形、仕様 §18.1）。E0020 の全体の一覧は R-87 (4) の規則の表に置く | M |
| T1-9 ✅ | `onsa fmt` | 正規化の規則: 2 空白の字下げ、二項演算子の両側に 1 空白、`,` の後に 1 空白、括弧の内側に空白なし、ブロック形の並びには末尾の `,`、`else` は `}` と同じ行、末尾の `return` を除去、項目の間は 1 空白行、ファイル末尾は改行 1 つ、S-07 の整列、書き手の改行は保つ（自動折り返しなし）。コメントはトークンの trivia から再現。`--check`。正規形は S-122 で仕様 §18.2 に書いた（項目の間の空行は 0 か 1 を保つ） | M |
| T1-10 ✅ | `onsa diff --ast` | 2 つのファイルの AST を trivia を無視して比較し、変わった項目の一覧（追加・削除・変更）と、変更された項目の中の最初の差の位置を出す | S |
| T1-11 ✅ | 仕様の例の収録 | §6 の表の全ブロックを `tests/spec/` に置く（第 1 期で未対応のものは `mode: parse`）。否定例（E0003 / E0010 / E0011 / E0012 / E0020 / E0320）を各 3 つ以上 | S |

文法（EBNF。`NL` は改行トークン、`{}` は繰り返し、`[]` は省略可。2026-10-06 の点検 C-64 で今の仕様に合わせた）:

```
File       = { Item }
Item       = { DocComment } { Attr } [ Vis ] ( Fn | Flow | Struct | Enum | TypeAlias | Trait | Impl
           | Effect | Handler | Const | Use | Extern | Target | Test )
Vis        = "pub" | "priv"                                       // S-36
Use        = "use" Path [ "." "{" Ident { "," Ident } [ "," ] "}" ]
Fn         = [ "rt" ] "fn" Ident [ Generics ] "(" Params ")" [ "->" Type ] [ "uses" EffectRow ] Block
FnSig      = [ "rt" ] "fn" Ident [ Generics ] "(" Params ")" [ "->" Type ] [ "uses" EffectRow ]
Generics   = "[" GenParam { "," GenParam } "]"
GenParam   = TypeName [ ":" Bound { "+" Bound } ] | "const" Ident ":" Type | Ident      // Ident は効果行変数
Bound      = [ "?" ] Path
Params     = [ Param { "," Param } [ "," ] ]
Param      = { Attr } [ "inout" | "move" ] ( "self" | Ident | "_" ) [ ":" Type ]        // self に型なし。型の省略は無名 fn だけ
Flow       = "flow" Ident "(" FlowParams ")" "->" Type [ "at" Clock ] Block   // 出力の at の要否は点検の C-07
FlowParams = [ FlowParam { "," FlowParam } [ "," ] ]
FlowParam  = { DocComment } { Attr } Ident ":" Type "at" Clock                // 入力の at は必須（E0810、S-102）
Clock      = Ident                                                    // クロックの名前空間（§11.3）
Derives    = ":" Bound { "+" Bound }                                  // 宣言の頭の trait（S-34、S-72）
Struct     = "struct" TypeName [ Generics ] [ Derives ] "{" Fields "}"   // タプル形は E0020（S-39）
Fields     = [ Field { "," Field } [ "," ] ]        Field = { DocComment } [ Vis ] Ident ":" Type   // pub は E0020（S-35）
Enum       = "enum" TypeName [ Generics ] [ Derives ] "{" Variant { "," Variant } [ "," ] "}"
Variant    = TypeName [ "(" Type { "," Type } ")" ]
TypeAlias  = "type" TypeName "=" Type
Trait      = "trait" TypeName [ Generics ] [ Derives ] "{" { FnSig | Fn | Const } "}"   // 上位の trait（S-72）
Impl       = "impl" [ Generics ] Type [ "for" Type ] "{" { [ Vis ] ( Fn | Const ) } "}"
Effect     = [ "blocking" ] "effect" TypeName "{" { FnSig } "}"
Handler    = "handler" Ident [ "(" Params ")" ] ":" Path "{" { Fn } "}"
Const      = "const" ConstName ":" Type "=" Expr
Extern     = "extern" Str "lib" Str "{" { "type" TypeName | FnSig } "}"
Target     = "target" ( "type" TypeName | FnSig )
Test       = "test" Str Block
EffectRow  = "{" [ Path { "," Path } ] "}"
Attr       = "@" Ident [ "(" AttrArg { "," AttrArg } ")" ]      AttrArg = Ident ":" Expr | Path | Str
Type       = Path [ "[" Type { "," Type } "]" ]                 // F32, Array[T], voice.State
           | "[" Type ";" Expr "]" | "(" ")" | "(" Type "," Type { "," Type } ")"
           | [ "rt" ] "fn" "(" [ ParamType { "," ParamType } ] ")" [ "->" Type ] [ "uses" EffectRow ]
ParamType  = [ "inout" | "move" ] Type

Block      = "{" { Stmt NL } [ Expr ] "}"
Stmt       = { Attr } "let" Pattern [ ":" Type ] "=" Expr | "var" Ident [ ":" Type ] "=" Expr | Expr "=" Expr   // let の属性は @mem(bulk)（S-43）
           | "for" Pattern "in" [ "move" ] Expr Block | "while" Expr Block
           | "break" | "continue" | "return" [ Expr ] | "assert" Expr | Expr
Expr       = Cast { BinOp Cast }                     // 群の検査は後段
Cast       = Prefix [ "as" Type | "at" Clock ]          // e at k（S-102）。連鎖は不可で E0011（S-118）
Prefix     = ( "-" | "!" ) Postfix | Postfix
Postfix    = Primary { "(" Args ")" | "~(" Args ")" | "!(" Args ")" | "." Ident | "." Int | "[" Expr "]" | "?" }
Primary    = Literal | Path | "_" | "^" Ident | "(" Expr ")" | "(" Expr "," Expr { "," Expr } ")"   // ^名前 は帰還の参照（S-44）
           | "[" Args "]" | "[" Expr ";" Expr "]" | Path "{" FieldInits "}"    // S-08: 見出しの式では不可
           | Block | "if" Expr Block { "else" "if" Expr Block } [ "else" Block ]
           | "if" "~" Expr Block { "else" "if" Expr Block } "else" Block   // if~ は連鎖の全体に掛かり、else は省けない（S-110、S-355）
           | "match" [ "~" ] Expr "{" { Pattern [ "if" Expr ] "=>" Expr "," } "}"    // if~ / match~ の ~ はキーワードの直後に空白なし
           | "fn" "(" Params ")" [ "->" Type ] [ "uses" EffectRow ] Block
           | "handle" Block "with" ( Path [ "(" Args ")" ] | Path "{" { Fn } "}" )
           | "unsafe" Block | "par" Ident "in" Expr ".." Expr Block
Args       = [ Arg { "," Arg } [ "," ] ]            Arg = [ "inout" | "move" ] Expr
Pattern    = PatAlt { "|" PatAlt }
PatAlt     = "_" | Ident | Literal | Path [ "(" Pattern { "," Pattern } ")" ]
           | "(" Pattern "," Pattern { "," Pattern } ")" | Path "{" Ident ":" Pattern { "," Ident ":" Pattern } "}"
```

遅延の組込みは `prev~(` / `delay~(` / `vdelay~(` の flow の呼び出し、`sample_rate()` は普通の呼び出しとして解析し、意味は M3 で与える（S-44）。`a..b` は `for` と `par` の見出しの中でだけ `Expr ".." Expr` として読む。

受け入れ: 計画 §3 M1 の通り。加えて、否定例が全て所定のコードで落ち、`fmt` が §17 の例を変えない。

### M2 名前解決と核の型検査（L）

✅ は完了。前半（T2-1〜T2-4、2026-10-02）の実装上の注記: `std` は `std/` のソースを `include_str!` で埋め込み、パッケージは自分の名前でも参照できる（`std` の中の `use std.math.{pow}`）。同じモジュールの同名の項目は E0304（flow が絡めば E0305）。
未解決の名前は E0302、可視性の違反は E0303（登録簿に追加）。E0310 は閉路を閉じる `use` の位置に 1 回だけ出す。E0809 は「`@param` が無い・付ける位置が違う・キーや値が不正」をまとめて扱う。`Str` / `Array` / `Buf` はシグネチャに書けるが、その操作は第 2 期（`Buf` は D-08 のとおりインタプリタ限定）。

本体の型検査（T2-5〜T2-7、T2-10、T2-11）の注記: 型の不一致の一般のコードとして E0401、struct リテラルのフィールドの誤りに E0410、`as` の縮小に E0411（変換メソッドの修正候補付き）、引数の数に E0412、未知のフィールド・メソッドに E0413、`?` の型に E0414、代入先が場所でないときに E0415、境界の不成立に E0416、型付きホールに E0421、反駁可能な `let` に E0502 を登録した。
シフト量は `U32`。境界の含意は `Ord ⇒ PartialOrd, Eq`、`Eq ⇒ PartialEq`、`Float ⇒ Num`、`Num ⇒ PartialEq, PartialOrd, Copy`。ユーザ定義型の `PartialEq` 系は `@derive` でだけ成立する。
リテラルどうしの比較（`1 == 1`）は型が決まらないので E0405（§2.4 の帰結。テストの例は `assert true` に直した）。
（後の決定で改めた、点検 C-89: 数の trait は S-84、derive は S-34 で宣言の頭の `: trait`、整数のリテラルは S-22 で `I32` に既定化するので `1 == 1` は通る）網羅性は usefulness 法で、反例（`Shape.Rect(_, _)`）をメッセージに出す。

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T2-1 ✅ | パッケージとモジュール | S-11。`onsa.toml` の `[package]` と `[dependencies]`（第 1 期は `std` だけ、D-07 で埋め込み）。ファイルからモジュール木、`use`（グロブなし、`pub use`）、循環 E0310、可視性（`pub` / `pub(pkg)` / 無指定）、prelude | M |
| T2-2 ✅ | 項目の収集とシグネチャ | 全モジュールの項目を集め、型とシグネチャを解決する。組込み型の表、ジェネリックの引数（型、`const N: U32`、効果行変数）、引数モード、`rt`、効果行（D-08: `Alloc` 以外は E0200）、struct / enum / 別名、`const`、`impl`（固有メソッド、関連関数、関連定数）、flow の **シグネチャ**（入出力のレート型、`@param`）と名前空間の項目（§11.6 の型・定数・関数。本体の検査は M3）、`test`。trait の定義と `impl Tr for Ty` は E0200（組込みの trait 名は境界としてだけ使える）。`effect` / `handler` / `extern` / 利用者の `target` は E0200 | L |
| T2-3 ✅ | 名前の規則 | E0320（S-01）、E0305（flow と同名の宣言）、E0306（S-16）、名前の種別の表（§2.3）に基づく解決（`Fs.read` は型の関連関数、`fs.read` はモジュール） | S |
| T2-4 ✅ | 種と配置 | `Kind` の計算、`layout`（§3.3）。`[T; N]`、タプル、struct、enum（タグ + 最大の列挙子、タグは `U8` / `U16` / `U32` のうち最小）、`Option` / `Result` | S |
| T2-5 ✅ | 本体の型検査 | §4.7 の推論。リテラルの制約付き型変数、期待型の下向き伝播、E0405 / E0406 / E0408 / E0420。演算子（群ごとに許す型。`+%` 系は整数だけ、`&& \|\|` は `Bool`、ビット演算は整数）、比較、`as` の許す対の表（§3.3）、変換メソッド（`narrow_*`、`round_f32` / `round_f64`、`trunc_*`、`trunc_*_sat`、`to_bits` / `from_bits`）、`checked_*` / `div_euclid` / `rem_euclid`、フィールド・添字・タプルの添字、struct / 配列 / タプルのリテラルと `[e; N]`、`if` / `match`（網羅性 E0501。enum、`Option`、`Bool`、タプル、リテラルは `_` が要る）、`for`（範囲、配列、`Span` の借用の反復。`move` の反復は E0200）、`while`、`return` / `break` / `continue`、`?`（`Option` / `Result`）、関連定数 `F32.PI` / `T.ZERO`、`assert`、型付きホール `_` | L |
| T2-6 ✅ | ジェネリクス | 呼び出しの引数と期待型からの具体化、組込みの境界（`Num` `Float` `PartialEq` `PartialOrd` `Eq` `Ord` `Copy` `Dup` `?Dup`）の検査、`const N` の等値、E0406。具体化の要求を記録して M3 の単相化に渡す | M |
| T2-7 ✅ | 第二級の値とクロージャ | `Span` を引数の型にだけ許す（E0710）。無名 `fn` は期待型のある引数の位置にだけ書け、捕捉は Copy の値だけ（`inout` 引数と Affine の捕捉はエラー）。`std.array.from_fn` と S-12 の `Span` メソッドを組込みとして解決 | M |
| T2-8 ✅ | 引数モードと排他性 | 場所（place）の解析。`inout` には `var` / `inout` 引数とそのフィールド・要素だけ（借用束縛は不可）。E0702（同じ呼び出しで重なる `inout`。フィールドが異なれば重ならず、配列の添字どうしは重なる）、E0711、E0713 / E0714、§5.4 の借用束縛（`let y = x.f` が借用引数から派生していれば借用）、Affine の移動後の使用（分岐を考慮した定義済み解析。第 1 期の Affine は flow の状態と `Buf` だけ） | L |
| T2-9 ✅ | rt | E0901（rt から非 rt の呼び出し）、E0902（効果行の `Alloc`）、E0903（モジュール内の呼び出しグラフの閉路） | S |
| T2-10 ✅ | スコープ | E0304（見えている束縛と同じ名前）、兄弟スコープの許可 | S |
| T2-11 ✅ | `const` | 初期化式がリテラルと集成体のリテラルだけのものを評価（関数呼び出しは M3 の T3-9）。参照は `ConstId` | S |
| T2-12 ✅ | `onsa check --json` | 関数ごとに最初のエラー、全関数分を一度に。`found` と `fixes` を全コードで埋める | S |

受け入れ: 計画 §3 M2 の通り。§17.6 `Poly` は flow の本体を除いて検査が通る（`voice.State` などは T2-2 の名前空間の項目で解決できる）。

### M3 flow の検査と降下、インタプリタ（L）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T3-1 ✅ | flow の検査 | 本体の制限 E0806、名前の順序と因果性 E0801（`prev` 系の第 1 引数だけが前方参照）、レートの推論（`定数 < Init < Ctl < Sig` の最大値。`let` の注釈による昇格）、E0810（値型は Copy。境界の入れ子の配列）、E0813 / E0814、`delay` の E0807（`N = 1`）/ E0808（長さが定数でない）と `N >= 2` / `MAX >= 1`、呼び出しの形 E0811 / E0812 と E0805（効果を持つ fn）と非 rt fn の `Init` 制限、S-04 の E0815、`par`（`N` は定数、`i` は `Init` の `U32`）、`sample_rate()`、`match` の点ごとの意味 | L |
| T3-2 ✅ | Core IR | §3.4 の定義、`verify`、テキスト出力 `onsa dump --core` | M |
| T3-3 ✅ | fn の降下 | AST → Core。演算子を型付きの命令に（`+` は `Checked`、`+%` は `Wrap`、`+\|` は `Sat`）、添字を検査付きに、`?` を `Switch` に、`for` の範囲を `ForRange` に、配列と `Span` の反復を添字のループに、無名 `fn` の引数（`array.from_fn`）は呼び出し先の組込みに展開（インライン）、集成体を返す関数は `sret` | M |
| T3-4 ✅ | 単相化 | T2-6 の要求から、到達する具体化だけを生成。名前は `clamp[F32]` → `clamp__F32` | S |
| T3-5 ✅ | flow の降下 | §3.5 と D-03。状態の struct（S-05 の順序、S-06 の名前。今の規則は仕様 §11.6 / §12.4、点検 C-92）、`Config` / `Params` / `Out`、`init` / `reset` / `ctl` / `tick` / `process` / `process_inplace` / `render` / `params_default`、`prev` の保存順、`delay` / `vdelay` の §11.4 の演算順の展開、サブインスタンス、`par` | L |
| T3-6 ✅ | 配置と大きさ | `layout` で `SIZE` / `BULK_SIZE` / `ALIGN`。`bulk_threshold`（マニフェストのターゲットから。無指定なら全て fast）で bulk へ分ける。bulk のポインタを fast の先頭に置く | S |
| T3-7 ✅ | インタプリタ | Core を直接実行する木歩き。値は `enum Value`（スカラ、集成体は `Vec<Value>`、`Span` は（バッファの参照、範囲）、`Buf` はヒープ）。検査付きの演算と添字は Rust の `checked_*` で、panic は `Err(Panic { msg, span })`。`Prim` は Rust の `f32` / `f64` のメソッドに対応付ける（`exp` `ln` `sin` ... は Rust が libm を呼ぶ。`fmod` は `%`）。F32 の演算は `f32` のまま（縮約されない） | M |
| T3-8 ✅ | `onsa test` | `test` 項目を実行。`assert` の失敗と panic はそのテストの失敗（S-16 の形）。`render` / `impulse` / `energy` / `assert_near`（D-08、std の宣言は T3-10）。`--json` | S |
| T3-9 ✅ | `const` の評価 | 関数呼び出しを含む初期化式をインタプリタで評価。E0407（第 1 期は Copy だけ） | S |
| T3-10 ✅ | `std` の最初の版 | `std/math.onsa`（D-07、S-09。宣言だけ）、`std/dsp.onsa`（`sum`、`db_to_amp`）、`std/dsp/test.onsa`（`impulse` `energy` `assert_near` `magnitude_at`）、`std/array.onsa`（`from_fn`）。Onsa で書けるものは Onsa で書く | S |
| T3-11 ✅ | `onsa interface <mod>` | 公開シグネチャ、種、大きさ、効果、`rt`、`@param`、flow の生成 API（§11.6 の形で表示）。`--json`。S-65 で `--target`、bulk 無効での大きさ、状態のフィールドの型を足した | S |
| T3-0 ✅ | S-21 / S-22 の反映 | 構文: `move` 式を消費位置に許す。型検査: 整数リテラルの `I32` 既定、`match move`。モード: Affine を `move` 無しで消費位置に置くと E0711 + 修正候補、`match x` は借用。既存の単体テストと否定例を規則に合わせる | S |
| T3-12 ✅ | `onsa graph <flow>` | DOT。ノードは `let` とインスタンス（名前は S-06）、辺は参照、`prev` 系の辺は破線、レートで色分け。`--svg` は `dot` があれば呼ぶ。S-66 で描き方を `spec/tools.md` §1 に書き、`par` を枠にした | S |
| T3-14 ✅ | 型の位置の const 引数（S-24） | 構文解析器で型引数に整数リテラルと定数名を許し（`TypeKind::Path` の引数に const 引数の形を足す）、シグネチャの解決で `const N` に束縛する。`fmt` / `dump` も対応 | S |
| T3-13 ✅ | 効果行の整合（S-23） | E0601 を登録し、効果行に `Alloc` の無い関数（`test` の本体を除く）が `Alloc` を要する操作・関数を呼ぶと E0601。rt 関数は E0902 が先に出る | S |

受け入れ: 計画 §3 M3 の通り。加えて `onsa dump --core` の出力が golden テストにあり、E0601 の否定例がある。

✅ M3 は 2026-10-02 に完了。受け入れの実測: `resonator decays` と `gcd` が `onsa test` で通る、`echo` の `BULK_SIZE` は 384004（`bulk_threshold = 4096`）、`graph` が `voice` に `src` / `f1` / `f2` / `smooth_0` を出す。
`voice.render` の 48000 サンプルはインタプリタで release 0.16 秒、debug 0.67 秒。

### M4 C バックエンドと export（L）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T4-1 ✅ | `runtime/c/onsa.h` | `onsa_param_info`（`name` `id` `min` `max` `default_` `step` `unit` `scale` `label`）、panic の設定マクロ（`ONSA_PANIC_POISON` / `TRAP` / `RESET` / `HALT`）と差し替え可能な `onsa_panic(const char* msg, const char* file, uint32_t line)`、検査付きの整数演算（`__builtin_*_overflow`、MSVC は手書きの比較）、`onsa_span_f32 { float* ptr; uint32_t len; }`、`#pragma STDC FP_CONTRACT OFF`、`_Static_assert(FLT_EVAL_METHOD == 0, ...)` | S |
| T4-2 ✅ | Core → C | 型（struct、enum は `struct { tag; union }`、配列は struct で包む、タプルは struct）、名前（D-10）、関数（`sret`、借用の集成体は `const T*`、`inout` は `T*`、スカラは値）、文、式（F32 の各演算を `(float)` で囲む）、`Checked` / `Wrap` / `Sat`、添字の検査、`Switch`、`Panic`、`Prim` の対応表（libm の `expf` など）、`const` は `static const` | L |
| T4-3 ✅ | flow の API | 内部の 5 関数と、export の wrapper（§14.2 の形）: `_init(s, bulk, cfg の各フィールド, sample_rate)`、`_reset`、`_params_default`、`_process(s, p, 入力..., 出力..., frames)` の戻り値（`poisoned` → 1、部分的な重なりと出力どうしの一致 → 2）、`@param` の範囲への飽和、`param_info` の表、`_new` / `_free`（`provides` に `Alloc` があるとき）、ヘッダ（`SIZE` / `BULK_SIZE` / `ALIGN` と `_Static_assert(sizeof(...) == ...)`） | M |
| T4-4 ✅ | panic の実現 | `poison`: wrapper で `setjmp`、`onsa_panic` が `longjmp`、出力をゼロで埋めて `poisoned = true`。`jmp_buf` は状態の末尾（S-05）。`trap` / `reset` / `halt`: `__builtin_trap()` / ターゲットのフック / `for(;;)`。`reset` で `poisoned` を解く | S |
| T4-5 ✅ | `onsa build --target <name>` | マニフェストの `[targets.*]`（`kind` = `staticlib` / `source`（`lang = "c"`）、`platform`、`numeric`、`provides`、`panic`、`panic_messages`、`memory.bulk_threshold`）、`[export]`（`prefix`、`flows`、`fns`。E0809 と E0610 はここで検査）。`target/<name>/` に `.c` / `.h` を出し、`platform` がホストなら `cc` を呼ぶ（フラグ: `-std=c11 -O2 -ffp-contract=off -fno-fast-math`、x86-32 は `-msse2 -mfpmath=sse`、MSVC は `/fp:strict`）、`ar` で `.a`。クロスは C の出力だけ | M |
| T4-6 ✅ | golden | `tests/golden/<name>.c` と生成物の差分。`UPDATE_GOLDEN=1` で更新 | S |
| T4-7 ✅ | 適合性の基盤 | `tests/conformance/<name>.onsa`（`render` を呼ぶ `test` だけを持つ）。ハーネスは interp で `Out` を得て、同じ入力で C（生成した小さなドライバ）を走らせ、サンプル列をバイト比較する。超越関数を通る flow は S-14 の判定で許容誤差（M5 で確定。M4 では同じ libm なので一致を期待する） | M |
| T4-8 ✅ | §17.5 の例 | `examples/voice_host/`: `daisy` 相当のターゲット定義（ホスト向けに `platform` を変えたもの）で staticlib を作り、C のホストが WAV に書く | S |
| T4-9 ✅ | NRVO と移動 | `sret` の構築先の決定（§12.7 の条件）。閾値以上のコピーの箇所を記録（`audit --memory` は M9） | S |
| T4-10 | S-28 / S-31 の実装（`@mem(bulk)`（S-43。一覧に無い記憶域の名前は E0818、`@mem(fast)` は E0020）、`memory.bulk`、E0818〜E0820、`BULK_ALIGN`。bulk のポインタと領域の分割は Core の型と `init` の文として明示する、レビュー R-90） | ターゲットの pass（D-03 の追記、レビュー R-80）で、`memory.bulk = true` のときに入れ子の状態まで bulk を分け、各状態の先頭に自分の bulk ポインタを置き、親の `init` に子のポインタを設定する文を足す（2026-10-05 のレビュー R-90 で、降下ではなくターゲットの pass で行うと改めた。`memory.bulk = false` では分けずに通す）。E0818 は sema（ターゲットによらない）、E0819 と E0820 はターゲットの pass で出す（ビルドと `onsa interface --target`。`check` では出ない。報告は S-67）。検証器の V-15 で配置の性質を検査し、インタプリタで分割した Core と分割しない Core を動かして出力を比べる差分テストを置く（インタプリタは bulk の領域とポインタを含む Core を実行できるようにする）。C バックエンドは `s->bulk` の形のまま。`voice` の中に `echo` を置いた conformance と golden を追加。R-81 と同じ回で、R-06 の進め方（設計メモ → 最も能力の高いモデル → 別のエージェントの検証）で行う。レビューの反映では W9-05 と W9-06（`rework-phase1.md`） | M〜L |

受け入れ: 計画 §3 M4 の通り。

✅ M4 は 2026-10-02 に完了。
`onsa build --target <name>` はマニフェストの `[targets.*]` / `[export]` を読み、`target/<name>/` に `onsa.h` と `onsa_<pkg>.c` と flow ごとのヘッダと `onsa_build.json` を出し、`platform` がホスト（`"host"` と書ける）で `kind = "staticlib"` なら `cc` + `ar` で `libonsa_<pkg>.a` を作る。
`tests/conformance/*.onsa` の全 flow を interp と C で比較（インパルス・無音・決定的な雑音、2 ブロック）: `echo` / `delay_chain` はビット一致、超越関数に到達する flow は 2 ULP 以内。`examples/voice_host` が §17.5 の C ホストで WAV を書く。
E0809 / E0610 は `build` の export の検査で出す。`Module.moves` に §12.7 のコピーの箇所を記録（`audit --memory` は M9）。

### M5 `std` と適合性テスト（M）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T5-1 | 精度の測定 | D-12 の表と ULP の測定。C（ホストの libm）と D-11 の結果を記録（インタプリタは S-93 で D-11 に結び付けるので、Rust の libm は測らない）。2 ULP を超える関数の一覧を作り、超える環境では D-11 の Onsa 実装に束縛を切り替える。W9-01 の後に行う（`rework-phase1.md`） | M |
| T5-2 | `std.math.soft` | D-11。musl からの移植と、精度表に対する検査。インタプリタと `const` の評価の結び付け（S-93）を含む。時期は点検の C-01 で、定数の評価の段の前提として前倒しする。レビューの反映では W9-01 と W9-02（`rework-phase1.md`） | M |
| T5-3 | `std.dsp` の完成 | S-10。`magnitude_at` と、`sum` の順序の固定を確認する conformance。`sum` の移動と一般化はレビュー §8 の R-23 の作業で行う（点検 C-109） | S |
| T5-4 | `std.test` | `check` と `gen` は普通の std の関数で、呼べる場所は効果行で決まる（S-97、レビュー R-125）。`check` は `Random` を要し、`test` の本体ではテストランナーが与える（種はテスト名から決める。`--seed`）。`Gen[T]` は std の struct で、フィールドは `priv`。無名関数を受け取るので、Core の関数値（R-81 の設計メモに含める、点検 C-01）の後。W8-09（Core の関数値）の後に行う | M |
| T5-5 | `onsa test --flows` | export される各 flow について、`@param` の角と無作為の内点（既定 8 点）× 入力（無音・インパルス・一様雑音）を interp で走らせ、出力が有限で panic しないことを検査。`--backends` と組み合わせ可 | S |
| T5-6 | `onsa test --backends all` | T4-7 のハーネスを `tests/conformance` 全体と `--flows` の掃引に適用。S-14 の判定 | S |
| T5-7 | `onsa primer --std` | 言語の要約（仕様 §2〜§11 の圧縮版を `docs/primer.md` に手で書き、埋め込む）と `std` の `interface`（doc コメントとモジュールの `//!` を含む、S-51） | S |
| T5-8 | 生成テスト | Q-03 の型の付いたプログラムの生成に置き換える（`process-improvement-phase1.md`、点検 C-111）。小さな flow を生成し、interp と C を比較する。gate では短時間だけ | S |
| T5-9 | gate | D-14 の `conformance` と `precision` を gate（Q-08）の項目にする（CI は用意しない）。gate の骨格は W1-01（`rework-phase1.md`） | S |

### M6 WASM バックエンド（M）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T6-1 | Core → WASM | `wasm-encoder`。線形メモリに状態（export する flow ごとに固定のオフセット。`SIZE + BULK_SIZE` に加え、`process` 用の入出力バッファ領域）、`init` / `reset` / `process` / `params_default` を export、`f32` 命令は IEEE のまま、検査付き演算はトラップ（`unreachable`）、`@param` の表は JSON の custom section `onsa.params`、D-11 の libm。状態のオフセットと大きさはターゲットの pass と export の計画（R-80、R-89）を読み、計算し直さない。`@param` の数値の ID（S-104）を表に入れる。`strict-ftz` は E0200（S-105） | L |
| T6-2 | `wasm-worklet` | `kind = "wasm-worklet"`: `.wasm` と glue（`AudioWorkletProcessor` の JS。パラメータの書き込み、トラップを捕まえて `poisoned`、`reset` の呼び出し）、最小の HTML | M |
| T6-3 | 適合性 | T4-7 のハーネスに Node（`WebAssembly.instantiate`）を追加 | S |

### M7 IDE の核（L）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T7-1 | `onsa_lsp` | `lsp-server`。開いているファイルの診断（保存ではなく変更時）、ホバー（型・クロック（S-102）・種・大きさ（`--target` の設定、S-65）・効果・`rt`・doc コメント（S-51））、文の単位の回復（S-59）、保存時の整形の要否（S-56）、定義へジャンプ、`fmt`（`textDocument/formatting`）、flow の状態の一覧（独自の要求 `onsa/interface`） | L |
| T7-2 | `onsa_web` | `wasm-bindgen` で `check(json) -> json`、`build_wasm(package) -> bytes`、`interface`、`graph`、`fmt` を公開。ブラウザの IDE はこれと T6-2 の glue で動く | M |
| T7-3 | `onsa play <flow>` | D-13 | M |
| T7-4 | `onsa probe <flow>.<name>` | 降下の段で `let` 名を追加の出力に昇格させる（`process` に `inout probe_<name>: Span[T]` を足す）。点検 C-96: S-30 で生成 API の引数を固定し、S-86 でプローブの宛先は構造で照合すると決めたので、生成 API を変えずに flow の計画を使うデバッグ用の入口でタップする形を M7 の着手のときに設計する（名前は R-48 / R-91 の規則）。CLI は WAV / CSV に書く。`play --probe` で端末に波形の概形 | M |
| T7-5 | ホットリロード | `play` の中で、再コンパイルの後に旧新の flow の計画を構造で照合し（`spec/tools.md` §2。生成する名前は使わない）、型が同じノードの状態を旧状態からコピーし、それ以外は `init` の値。サブインスタンスは中まで照合する。プローブの付け替えも同じ照合。§19 の「型の変わったフィールド」は `init` で初期化（S-86） | S |
| T7-6 | VS Code 拡張 | 構文の色分け（TextMate）と LSP クライアントの最小構成 | S |

### M8 JavaScript への変換（M）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T8-1 | Core → JS | flow ごとに 1 クラス。状態は `Float32Array` / `Int32Array` などの型付き配列を、ターゲットの pass が記録した配置のオフセット（R-80。sema の `layout` は消す）で共有する 1 つの `ArrayBuffer`。F32 の各演算の後に `Math.fround`。`I64` / `U64` は E0200。`@param` の表は定数のオブジェクト。`kind = "source"`, `lang = "js"` | M |
| T8-2 | 適合性 | Node で実行し、4 者で比較 | S |

### M9 第 1 期の締め（S）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T9-1 | `explain` | 全コードの本文（原因、例、直し方）。D-04 の検査を有効にする | M |
| T9-2 | `onsa audit` | `--memory`（状態の内訳、Core の移動とコピーの記録（R-81））、`--stack`（rt の呼び出しグラフの最大深さ × フレームの推定）、`--panics`（export の rt の経路にある検査付きの演算・添字・`unwrap`・非飽和の変換。到達は Core の `reach`、R-80 (3)）。R-10 の範囲の解析（証明できる検査の除去）を含む（`rework-phase1.md` §4） | M |
| T9-3 | 仕様への反映 | `D` と `S` の決定、`primer`、`README` | S |

---

## 5. 診断コードの実装表

| コード | 内容 | 検出する段 | M |
|---|---|---|---|
| E0001 / E0002 | 不正な文字・リテラル（空白と改行の文字の閉じた一覧と、解釈の分かれる制御文字、S-201） / 予期しないトークン（S-18。候補を作れない `@` 束縛、S-186。`test` の名前の規則に合わない名前（空、補間、制御文字など）で、候補なしと note、S-244） | 字句・構文 | M1 |
| E0003 | `else` と、ブロックの `{` の位置。括弧や腕の中も含む（S-47、R-62）。主の位置は置き場所を誤ったトークンで、候補は前の行のコメントの前へ移す（S-216） | 構文 | M1 |
| E0004 | 付ける宣言の無い `///`、ファイルの先頭以外の `//!`（S-51） | 構文 | M1 |
| E0005 | 一覧に無い属性、その構文の場所に付けられない属性、`@repr` / `@fp` の値（S-103、S-133。場所の中の意味の条件と、`@param` / `@mem` の値は各属性のコード） | 構文 | M1 |
| E0006 | 構文の入れ子の深さが上限（256）を超えた（S-183）。数え方は §2.5 の規則（式・型・パターンの形とブロックが一段、S-221。`::[…]` も一段、S-239）。note は型を名前付きの struct に分ける形（S-264） | 構文 | M1 |
| E0010 | 強弱の無い群の混在（S-45 の部分順序。比較の連鎖、`&&` と `\|\|`、ビットと他の群・違うビット演算子（S-61）、剰余と加法・乗法。修正候補は S-60） | 構文（後段） | M1 |
| E0011 | `as` と `at` を二項の中に（S-102）、`as` / `at` の連鎖（S-118） | 構文（後段） | M1 |
| E0012 | 前置の重ね | 構文（後段） | M1 |
| E0013 | ブロックに似た式（`if`・`if~`・`match`・`match~`・ブロック式・無名関数・`unsafe`・`handle`・`par`）を括弧なしで演算子の被演算子に（二項の左右、前置、後置の受け手、`as` / `at` の左）。式の単位で一つで、主の範囲は最初の括弧の無い被演算子、候補は全てを括弧で囲む一つの形。他の診断の候補もこの形を作らない（S-537） | 構文（後段） | M1 |
| E0020 | 既存言語と旧版の書き方、誤解を示す冗長な印（S-114）。修正候補を 1 つ以上作れるときだけで、note で正しい規則を示す（S-02、S-48）。行頭の二項演算子（S-124）、名前に付く印と前置の記号の後の空白（S-123）、見えている名前への `^`（S-116）、旧形の属性（S-133）、`Copy` / `Dup` の `impl` と宣言の `: Copy`（S-140）、`.` の前後と `?` の前の空白（S-203）、値の呼び出しの形と `s.f(x)`（S-191。呼び先が名前の経路でないものは構文の段、名前の経路は名前の段、`s.f(x)` は型の段）、ガードに書き換えられる `@` 束縛（S-186）、書けない型の定数のパターンと `-LIMIT`（S-185、型の段）、他言語の形の型引数（候補は `::[…]`）と型の位置の `Buf::[F32]` の `::`（S-239、S-256、S-277）を含む | 字句・構文（`Sig[F32]` は名前解決、S-120。`^` は名前解決、S-267。型引数は S-256 の段） | M1 |
| E0200 | この版のコンパイラが扱えない機能や形（S-224: 仕様がこの版で未対応と定めたもの、変換先が与えないもの、仕様にあってまだ扱えないもの。S-03。第 1 期の手書きの `impl Hash`、S-138。予約語 `clock` / `when` / `reset_if` の構文、S-169。マニフェストの未対応の値の閉じた一覧（S-154）: `kind` の `exe` `clap` `vst3` `au` `wasm-worklet`、`lang` の `js`、std 以外の依存、`main_frame`、クロスの `platform` で外部のツールチェーンを要する `kind`（S-161））。全ての E0200 は一か所の閉じた一覧 `onsa_diag::unsupported::Feature` から作り、`onsa explain E0200` が同じ一覧を示す（W2-07。自己テストが一覧の外での直書きを禁じる） | 名前解決・型・ビルド（ターゲットの値、`strict-ftz` など） | M2 |
| E0302 / E0303 | 未解決の名前 / 可視性の違反（公開の宣言に、それより狭い可視性の型を書く、S-144。`pub` でない項目の export、S-165） | 名前解決 | M2 |
| E0308 | 名前の種類が位置に合わない（値・型・モジュール・関数・flow・trait・列挙子・定数。S-103。パターンの列挙子でも定数でもない名前、S-185。値の位置のメソッドと効果の操作、S-205。マニフェストの `flows` / `fns` の種類の誤り、S-165） | 名前解決 | M2 |
| E0309 | 使われないローカルの束縛（`let` / `var`、分解、`match` の腕、`for`。flow は出力と `let _` から辿れない `let`。S-129） | 名前解決（flow は flow の計画） | M2 |
| E0304 | シャドーイング、同名の項目、二重の `use`、derive と手書きの `impl` の重なり（S-34）、trait の重複実装と同じ型の `impl` の同名のメンバ（S-134）、flow の名前 `hoist`（S-149）、状態の予約の名前（仕様 §11.6、R-48） | 名前解決 | M2 |
| E0305 | flow と同名の宣言 | 項目の収集 | M2 |
| E0306 | 同名の `test`（S-16。名前は値で比べ、正規化しない、S-244） | 項目の収集 | M2 |
| E0307 | `impl` を書ける場所と対象の書き方の規則（S-139）: 孤児規則（S-70）、対象に書いた型別名（S-91）、対象の型引数が `impl` の型パラメータでない（S-137）、組込み型だけが実装する `Float`（S-108）、derive だけの `Ordinal`（S-145） | 名前解決 | M2 |
| E0310 | モジュールの循環 | モジュール | M2 |
| E0311 | 型が値として自分自身を含む（レビュー R-02）。型別名の循環も含む（R-105、S-91） | シグネチャ | M2 |
| E0312 | `const` の初期化式の循環（レビュー R-02） | `const` の評価 | M3 |
| E0320 | 命名規則（S-01）。識別子の `__`（S-149）。規則に揃えた名前が予約語になるときの候補は末尾に `_`（S-243） | 名前解決 | M1 |
| E0401 | 型の不一致 | 型 | M2 |
| E0405 | リテラルの型が決まらない | 型 | M2 |
| E0406 | 型パラメータが決まらない。関数の終わりに残る型変数も含む（レビュー R-03。総称の呼び出しの型パラメータも関数の終わりまで待つ、S-174）。位置は型変数を作った式（S-226） | 型 | M2 |
| E0407 | `const` の結果の種 | `const` の評価 | M3 |
| E0408 | リテラルが範囲外（前置の `-` を含めた値で検査する、S-184、S-227。0 でない浮動小数の字面が 0 に丸まるときも、S-211）。どの整数型にも収まらない整数リテラルと `U32` に収まらないタプルの添字は構文の段（S-214） | 構文・型 | M2 |
| E0409 | 型の大きさか flow の状態の領域が `U32` で表せない（`2^32 - 1` バイトを超える。レビュー R-100、S-88。S-142 で E0313 から移した） | ターゲットの pass（配置） | M4 |
| E0410〜E0416 | struct リテラルとパターンのフィールドの過不足と重複（S-179） / `as` で書けない組（縮小を含む） / 引数の数（型引数と const 引数を含む、S-103） / 未知のメンバ（メソッドを値として取る `p.norm`、S-205） / `?` の全ての誤り（S-175） / 代入先が場所でない（`const`、`inout` に渡す場所でないもの、タプルの左辺、S-178、S-180） / 境界（derive の一覧に無い trait、上位の trait の違反、`Buf` / `Span` の要素の `Copy`、`[e; N]` の Dup、補間の `Show`、`vdelay` の `Float`、中身のある enum の `Ordinal`（S-145）、種の制約の不成立（S-140）を含む、S-103、S-72、S-109） | 型 | M2 |
| E0417 | 定数式の規則の違反: 配列の長さ、const 引数、遅延線の長さ、`par` の回数に（位置によらず、S-132）、定数式でないもの（関数の呼び出しなど、S-103）や const の型パラメータを含む式（S-50）。`panic` の引数が補間を含まない文字列リテラルでない（S-109） | 型 | M3 |
| E0418 | ブロックの途中の文の値が `()` でない（S-127） | 型 | M2 |
| E0419 | コンパイル時の評価の panic（定数式の溢れとゼロ除算、`const` の初期化式、`@param` の値。S-131） | `const` の評価 | M3 |
| E0420 | 対象の型が未解決 | 型 | M2 |
| E0421 | 型付きホール | 型 | M2 |
| E0422 | 検査が作る型（別名を展開し型引数を当てた後の型。書いた型、推論した型、具体化の型）が深さ 256 か大きさ 4096 を超えた。位置は上限を初めて超えた型を作った所で、note は途中の型を名前付きの struct にする形（S-264。降下の具体化の分の段は S-290） | 名前解決（別名と書いた型）・型 | M2 |
| E0501 / E0502 | 網羅性（`Bool`、enum、それらのタプルと struct だけで数え、リテラル・定数・ガードの付いた腕は数えない、S-187、S-185） / 反駁可能な `let`（列挙子が一つの enum も、S-177） | 型 | M2 |
| E0503 | 発散の後の到達しない文（S-128）と、前の腕で覆われる `match` の腕（S-187） | 型 | M2 |
| E0601 | 効果行に無い効果を使った（S-23、S-77。暗黙の確保と破棄、`rt` の関数の中の確保を含む。第 1 期は `Alloc`） | 効果 | M3 |
| E0610 | export の効果が `provides` に無い | `build` | M4 |
| E0612〜E0614, E0620, E0630, E0640〜E0642, E0650 | 効果・handler・ポリシー・並行（E0611 は S-77 で E0601 にまとめて欠番。E0615 は仕様 §19.2 で `spawn` ごと外したので欠番） | — | 第 2 期 |
| E0701 / E0703 / E0704 | 変更できない場所（場所でないものは E0415、S-178） / 呼び出し位置のモードの不一致（`for i in move 0..n` を含む） / 移動後の使用 | モード | M2 |
| E0702 | `inout` の重なり（借用と `inout` の重なりと、他の引数の中の変更を含む、S-193） | モード | M2 |
| E0710 | 第二級の値の位置（既定のモードの関数型の引数を持ち出すこと、`move` の関数型の引数に捕捉する無名関数を渡すことを含む、S-190） | 型 | M2 |
| E0711 | 借用の Affine を `move` | モード | M2 |
| E0712 | クロージャが捕捉できない値 | モード | M2 |
| E0713 / E0714 | `!` の有無 | 型 | M2 |
| E0801 | 前方参照（印 `^` の無い前方参照、遅延の組込みの第 1 引数の外の `^名前`、その中の利用者の flow の引数の `^名前`。S-44、S-116。`^` の挿入の候補は遅延の第 1 引数の中だけ、S-117） | 名前解決（S-267） | M3 |
| E0805 | 効果を持つ fn の呼び出し | flow | M3 |
| E0806 | 本体の制限（仕様 §11.2 の使える式の閉じた一覧の外、S-125。入れ子のブロックの `let`、S-151。`&&` / `\|\|` の右辺の状態を持つもの、S-110 を含む） | 名前解決（代入の形を含む、S-267） | M3 |
| E0807 / E0808 | `delay` の長さ（`N = 1` は E0807。`N = 0`、`vdelay` の `MAX = 0` と `MAX > 2^24` は E0808、S-109。`par` の空の範囲も E0808、S-151。定数式でないものは E0417、S-132） | flow | M3 |
| E0809 | `@param` の誤り（export の `block` の入力に無い、位置、キーや値、`id` の文字・重複・数値の衝突。S-104） | `build`（`id` の検査は検査の段） | M4 |
| E0810 | flow の入力と出力のクロック（`at`）が無い、出力のクロックが `sample` でない（S-119）、値型が Copy でない、境界の入れ子（S-102） | flow | M3 |
| E0715 | 借用の `for` の本体で反復元を変更した（レビュー R-24） | 引数モード | M2 |
| E0811 / E0812 | `~` の有無（遅延の組込み `prev~` / `delay~` / `vdelay~` を含む。S-44）。`if` / `match` の枝の状態を持つもの（E0811）と、状態を持つものの無い `if~` / `match~`（E0812）も含む（S-110） | 名前解決（分岐は flow の検査。S-267） | M2 |
| E0813 | `prev` 系の第 1 引数が `sample` でない（修正候補は `prev~(p at sample)`、S-102。`init` 引数のクロックは S-147 で E0815 にまとめ、E0814 は欠番） | flow | M3 |
| E0815 | 値のクロックが置く位置より速い（引数が入力より速い、S-04。`e at k` で遅くする、S-102。遅延の `init` 引数と非 rt の fn の引数、S-147） | flow | M3 |
| E0816 | `prev` 系の `init` を省いたが、値型が `Default` を満たさない（S-29） | flow | M3 |
| E0817 | flow が自分自身をインスタンスにする（レビュー R-03） | flow | M3 |
| E0818 | `@mem` の位置か値が不正（値が `delay` / `vdelay` でない `let` に付けた、一覧に無い記憶域の名前。S-31 / S-43） | flow | M4 |
| E0819 | `memory.bulk = true` のターゲットで、bulk を持つ状態を普通の値に置いた（S-31） | `build` | M4 |
| E0820 | export する flow の領域が `fast_budget` / `bulk_budget` を超えた（S-31） | `build` | M4 |
| E0821 | flow の外に flow だけの構文（`f~(...)`、`~` 無しの flow の呼び出し、`^名前`、`par`、レートの `at`。S-101、S-102。修正候補は付けず、`at` だけは外すことを候補にする） | 名前解決（S-267） | M3 |
| E0901 | `rt` の関数の中での、`rt` でない関数・関数値の呼び出し（S-77。関数型の位置の互換の違反は E0401） | rt | M2 |
| E0902 | rt の効果行に `Alloc` | rt | M2 |
| E0903 | rt の再帰 | rt | M2 |
| E0904 / E0905 | rt と blocking / rt 効果 | — | 第 2 期 |
| E1010 | 核から `extern` に到達 | — | 第 2 期 |
| E1011 | export の C の名前の重なり（仕様 §14.2 の表から作る全ての名前、export した関数の名前、インクルードガード。S-52、S-112） | build | M4 |
| E1101 | マニフェストを TOML として読めない（S-99） | マニフェスト（ソースより先） | M4 |
| E1102 | マニフェストの未知の表・キー（S-99） | マニフェスト（ソースより先） | M4 |
| E1103 | マニフェストの値の型や形が規則に合わない（閉じた一覧に無い値、`prefix`・パッケージ名の形、std の版の不一致、`flows` / `fns` の重複。S-99、S-95、S-83、S-165） | マニフェスト（ソースより先） | M4 |
| E1104 | マニフェストの必須のキーが無い（`name`、`edition`、export するときの `prefix`、`kind`、`lang`、ビルドするターゲットの `platform`。S-99） | マニフェスト（ソースより先） | M4 |

第 1 期で実装するのは 82 コード（2026-10-08 に登録簿の第 2 期でないコードで数え直した。S-264 で E0422 を足した。S-147 で E0814 を E0815 にまとめた。M1〜M4 の行。2026-10-06 の点検 C-86 で数え直し、点検 C-119〜C-121 の E0418、E0503、E0309 と、C-18 の E0419 を足した。C-30 で E0313 を E0409 に移した。M2 の型検査で E041x が増えた）。

欠番: E0611（S-77 で E0601 にまとめた）、E0615（仕様 §19.2 で `spawn` ごと外した）、E0313（S-142 で E0409 に移した）、E0814（S-147 で E0815 にまとめた）。gate の網羅性の照合（S-109）は、この一覧を除いて、登録簿の全てのコードが仕様の本文に現れ、仕様の本文の全てのコードが登録簿にあることを確かめる。この行と、上の表の M の欄が「第 2 期」の行は gate が読む（`tools/repo.py` の `retired_codes` と `phase2_codes`。W1-02）。行頭の「欠番:」、最初の「。」までに欠番を並べる形、M の欄の「第 2 期」の書き方を保つ。

---

## 6. 仕様の例の対応表

仕様の ```` ```onsa ```` ブロック（開始行）と、`tests/spec/` の置き場所、検査の深さ（D-05）、通るマイルストーン。断片は関数か `test` で包み、包んだ部分はブロックの外に置く（D-06 の照合は逐語の部分一致）。

| 行 | 節 | 内容 | ファイル | mode | M |
|---|---|---|---|---|---|
| 84 | §2.1 | コメント | `lex/comments.onsa` | check | M2 |
| 190 | §3.1 | 群（E0010 の否定例を含む。S-45 で例を改め、写しは実装待ち） | `ops/groups.onsa` | check | M2 |
| 215 | §3.3 | 変換 | `ops/convert.onsa` | check | M2 |
| 361 | §4.4 | ユーザ定義型 | `types/user.onsa` | check | M2 |
| 388 | §4.5 | ジェネリクス | `types/generics.onsa` | check | M2 |
| 435 | §5.1 | 束縛（S-89 の整列。写しは実装待ち） | `values/bind.onsa` | check | M2 |
| 507 | §5.4 | `total_len`（`Array[Str]`） | `values/borrow_for.onsa` | parse | 第 2 期 |
| 521 | §6.1 | `mean`（R-115 で `[F64; N]` と `std.math.sum` に改めた。`sum` の移動は R-23） | `fn/mean.onsa` | parse | 第 2 期 |
| 540 | §6.2 | `Point` のメソッド（S-45 の括弧。写しは実装待ち） | `fn/methods.onsa` | check | M2 |
| 557 | §6.3 | `Show` | `fn/trait_show.onsa` | parse | 第 2 期 |
| 608 | §6.4 | derive（`Hash` `Show` は E0200 のマーカ。S-34 の宣言の `: trait` の形。写しは実装待ち） | `fn/derive.onsa` | check | M2 |
| 629 | §6.6 | `const`（`make_sine_table` を補う） | `fn/const.onsa` | check | M3 |
| 653 | §7 | 制御（断片。`...` を含む） | `control/forms.onsa` | none | — |
| 691 | §8.1 | 効果 | `effects/decl.onsa` | parse | 第 2 期 |
| 720 | §8.1 | `map`（`...`） | `effects/map.onsa` | none | — |
| 746, 766, 791 | §8.3〜8.5 | handler（最上位の `let`）、arena、main（`...`） | `effects/{handler,arena,main}.onsa` | none | — |
| 807 | §9.1 | `line_count`（`...`） | `effects/result.onsa` | none | — |
| 857 | §10 | `soft_clip` | `rt/soft_clip.onsa` | check | M2 |
| 905 | §11.2 | `one_pole`（S-102、S-44、S-29、S-45。写しは実装待ち） | `flow/one_pole.onsa` | check | M3 |
| 1000 | §11.5 | `unison`（`saw` を補う。R-23、S-102、S-45。写しは実装待ち） | `flow/unison.onsa` | check | M3 |
| 1024 | §11.6 | 生成 API（擬似） | `flow/generated_api.onsa` | none | — |
| 1070 | §11.7 | `gain`（S-102。写しは実装待ち） | `flow/gain.onsa` | check | M3 |
| 1106 | §11.8 | `check`（S-45。写しは実装待ち） | `test/check.onsa` | parse → test | M5 |
| 1309, 1326 | §14.1 | `extern` と `Conv` | `ffi/extern.onsa` | parse | 第 2 期 |
| 1354 | §14.2 | `onsa_version` | `ffi/export_fn.onsa` | check | M2 |
| 1482 | §15.2 | `target` | `module/target.onsa` | parse | 第 2 期 |
| 1626 | §16 | `main` と文脈の登録（2026-10-02 の書き直し後） | `concurrency/main.onsa` | parse | 第 2 期 |
| 1645 | §16 | `device.run` の `target` 宣言 | `concurrency/device_run.onsa` | parse | 第 2 期 |
| 1682 | §17.1 | `gcd` | `examples/gcd.onsa` | test | M3 |
| 1702 | §17.2 | `line_count` のテスト（S-34。写しは実装待ち） | `examples/line_count.onsa` | parse | 第 2 期 |
| 1734, 1766, 1808 | §17.3〜17.4 | `resonator`、`saw` / `smooth` / `voice`、`echo`（同じモジュール。S-102、S-44、S-29、S-45、S-43。写しは実装待ち） | `examples/voice.onsa` | test | M3 |
| 1829 | §17.4 | `render_vowel`（S-89 の整列。写しは実装待ち） | `examples/render_vowel.onsa` | parse | 第 2 期 |
| 1878 | §17.6 | `Poly`（`voice.onsa` と同じファイル） | `examples/voice.onsa` | check | M3 |

行は 2026-10-06 の点検の直しの後のもの（点検 C-62）で、その後の仕様の編集で今の行とずれている。今の行は `tools/check_spec_examples.py` が表示する。「写しは実装待ち」の行は、`tests/spec` の写しが古い形のままで、gate の実装待ちの一覧（Q-08、点検の C-63）`tests/pending.toml` に置く。
一覧はブロックを行番号ではなく「節・内容のハッシュ・先頭の行」の名前で指す（W1-01）。one_pole の理由は、W1-01 で写しと比べて S-29 と S-45 を足した。

M1 では `none` 以外の全てのファイルが `parse` として通ることを確認する（`mode` の指定は M2 以降の検査の深さ）。断片を包むためのコード（`fn groups(...) {`、`Point` の定義、`make_sine_table`、`saw`）はブロックの外に置いてある。M0 でこの収録を済ませた（T1-11 の前倒し）。否定例のマーカは、その診断を実装するマイルストーンで足す。

---

## 7. 着手の順

レビューの反映（2026-10-07 以降）は、[`rework-phase1.md`](rework-phase1.md) の段（W1〜W10）の順で行い、その後に §4 の M5〜M9 を続ける。以下は M0 に着手したときの記録である。

最初の 10 作業。T0-5 と S-15 以外は仕様の決定を待たない。

1. T0-1 ワークスペース
2. T0-2 `onsa_diag`（§5 の全コードを登録）
3. T0-3 `onsa_cli` の骨格
4. T0-4 `tests/spec` のランナー（D-05 を仮採用）
5. T0-6 CI
6. T1-1 字句解析器
7. T1-2 AST
8. T1-3 宣言の構文解析
9. T1-4 文とブロック（文の区切り）
10. T1-5 式（群の検査）

S-01 / S-02 / S-07 / S-08 / S-15 は M1 の中で要るので、6 の前に決める。D-01 / D-02 / D-05 / D-06 はこの 10 作業の形を決めるので、最初に決める。

### 3.2 AST（`onsa_syntax`）

- `Token { kind, span }` の列。空白・改行・コメント・doc コメントも独立したトークン（trivia）で、トークンの列はソースの全てのバイトを重ならずに覆う（W3-01）。あるトークンの前が「何も無い・空白・改行」のどれかは、一つの関数 `gap_before` で全体の列から読む（トークンに印を持たない）。
- 構文解析器は CST（全てのトークンを持つ損失の無い構文木）を作り、AST は CST から一つの段で作る（D-02 の改定、レビュー R-86）。CST を出力すると、元のソースと 1 バイトも違わない（性質テストで確かめる）。
- `Item { kind: ItemKind, … }`（`ItemKind` は `Fn` / `Flow` / `Struct` / `Enum` / `TypeAlias` / `OpaqueType` / `Trait` / `Impl` / `Effect` / `Handler` / `Const` / `Use` / `Extern` / `Target` / `Test`。誤りで止まった宣言は、どこまで読んだかを `failed` に持つ）、`Type`、`Pattern`、`Expr`、`Stmt`、`Attr`。
  全てのノードが `Span` を持つ。
- 式の二項演算は、CST では平らな列で、AST は CST から一度だけ `Chain` の木 `Binary { op, op_span, lhs, rhs }` に読む。群の検査（E0010、E0011、E0012）は AST を作った後の独立の段（`groups.rs`）で、E0010 の修正候補（括弧の挿入位置）は列に一時の強さを置いた読みから作る。
- `Call { callee, kind: Plain | Flow (~) | Bang (!) | Value (v.(x)), args: Vec<Arg> }`、`Arg { mode: Borrow | Inout | Move, expr, span }`。
- `Attr { name, args: Vec<AttrArg> }`（`@param(min: …)` は `AttrArg::Named { key, value }`）。付けられる場所と値は `onsa_syntax::attrs` の表が決める（E0005）。
- flow の入出力の宣言は値の型とクロック（`at`）を持ち、式は `At { expr, clock }`（`e at k`）と帰還の参照 `Feedback(name)`（`^名前`）を持つ（S-44、S-102）。`let` は属性（`@mem(bulk)`、S-43）を持つ。クロックの名前は型ではなく、クロックの名前空間の名前（§11.3）。
- 構文の段の置き場所: 字句（`lexer.rs`）→ 構文解析（`parser.rs`、`parser/*`。宣言の表は `declarations.rs`、ガードの読みは `guard_reading.rs`、閉じ括弧が閉じる開きは `scan::pair` 一つ）→ CST（`cst.rs`）→ AST への変換（`lower.rs`、`lower/*`。見出しの降下は `lower/decls.rs`）→ 変換の後の検査（`docs.rs`、`groups.rs`、`naming.rs`、`foreign.rs`、`nesting.rs`）。
  診断の単位は `units.rs`、候補は `operands.rs`・`edits.rs`、トークンの事実は `starts.rs`・`scan.rs`・`layout.rs`。整形は `fmt/*`。

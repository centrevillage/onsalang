### 3.2 AST（`onsa_syntax`）

- `Token { kind, span }` の列。空白・改行・コメント・doc コメントも独立したトークン（trivia）で、トークンの列はソースの全てのバイトを重ならずに覆う（W3-01）。あるトークンの前が「何も無い・空白・改行」のどれかは、一つの関数 `gap_before` で全体の列から読む（トークンに印を持たない）。
- 構文解析器は CST（全てのトークンを持つ損失の無い構文木）を作り、AST は CST から一つの段で作る（D-02 の改定、レビュー R-86）。CST を出力すると、元のソースと 1 バイトも違わない（性質テストで確かめる）。
- `Item`（`Fn` / `Flow` / `Struct` / `Enum` / `TypeAlias` / `Trait` / `Impl` / `Effect` / `Handler` / `Const` / `Use` / `Extern` / `Target` / `Test`）、`Type`、`Pattern`、`Expr`、`Stmt`、`Attr`。全てのノードが `Span` を持つ。
- 式の二項演算は構文解析では **平らな列** `Binary { operands: Vec<ExprId>, ops: Vec<(BinOp, Span)> }` として保持し、群の検査（E0010）は構文解析の直後の独立した段で行う。これにより E0010 の修正候補（括弧の挿入位置）を列全体から作れる。
- `Call { callee, kind: Plain | Flow (~) | Bang (!) , args: Vec<Arg> }`、`Arg { mode: Borrow | Inout | Move, expr }`。
- `Attr::Param { keys: Vec<(key, const expr)> }` は flow の入力にだけ付く。
- flow の入出力の宣言は値の型とクロック（`at`）を持ち、式は `At { expr, clock }`（`e at k`）と帰還の参照 `Feedback(name)`（`^名前`）を持つ（S-44、S-102）。`let` は属性（`@mem(bulk)`、S-43）を持つ。クロックの名前は型ではなく、クロックの名前空間の名前（§11.3）。

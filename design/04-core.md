### 3.4 Core IR（`onsa_core`）

```rust
pub struct Module { types: Vec<TypeDef>, consts: Vec<ConstDef>, fns: Vec<FnDef>, flows: Vec<FlowMeta> }
pub struct FnDef {
    name: QualName,                       // dsp.voice.tick の形。C では __ 区切り
    params: Vec<Param>,                   // Param { local, mode: Borrow|Inout|Move, ty }
    ret: Ty, sret: bool,                  // 集成体を返すなら sret = true（§12.7）
    rt: bool, locals: Vec<Local>, body: Block,
}
pub enum Stmt { Let(LocalId, Expr), Assign(Place, Expr), Expr(Expr),
                If(Expr, Block, Block), While(Expr, Block), ForRange(LocalId, Expr, Expr, Block),
                Break, Continue, Return(Option<Expr>) }
pub enum Expr { Lit(Lit, Ty), Local(LocalId), Const(ConstId),
                Unary(UnOp, Ty, Box<Expr>), Binary(BinOp, NumTy, Overflow, Box<Expr>, Box<Expr>),  // Overflow: Checked|Wrap|Sat
                Cmp(CmpOp, Ty, ..), Cast(Ty, Ty, ..), Call(FnId, Vec<Arg>), Prim(PrimId, Vec<Expr>),
                Field(Box<Expr>, u32), Index(Box<Expr>, Box<Expr>),  // Index は常に境界検査付き
                Struct(Ty, Vec<Expr>), Array(Vec<Expr>), Repeat(Box<Expr>, u32), Tuple(Vec<Expr>),
                IfExpr(..), Switch(Box<Expr>, Vec<(Tag, Block)>),  // enum のタグで分岐。束縛は Field で取り出す
                Panic(MsgId) }
pub enum Place { Local(LocalId), Field(Box<Place>, u32), Index(Box<Place>, Expr) }
```

- 全ての式に型が付く。ジェネリクスは無い（単相化済み）。レートは無い（flow は降下済み）。
- `Prim` は `std.math` の `target` 宣言と組込みメソッド（`trunc_i32_sat`、`to_bits`、`Span.len` など）。`PrimId` の一覧を `onsa_core::prim` に置き、各バックエンドはこの一覧に対して対応表を持つ（表の欠けはテストで検出）。
- `verify(Module)` は、常に（release も）段の境目ごとに走らせる（降下と正規化の後、ターゲットの pass の後）。失敗は内部エラー（終了コード 101、診断コード無し。S-67）で、破った規則の番号、関数名、Core の位置を報告し、その関数の Core のダンプを不具合の報告用に残す（レビュー R-82）。検証器は D-15 に従い、Core の構造から性質を確かめる。
  規則は次の一覧で全てである。規則ごとに、その規則だけを破った Core を手で作って検証器が拒むことを確かめる否定のテストを置く。Core の形を変えるときは、一覧・検証器・テストを一緒に直す。

| 番号 | 規則 | 出典 |
|---|---|---|
| V-01 | 式の型が、式の種類ごとの規則と一致する（定数の初期化式を含む） | T3-2 |
| V-02 | プリミティブの引数の数・モード・型と結果の型が、`Prim` の表のシグネチャと一致する | R-82、R-79 |
| V-03 | `Cast` は §3.3 の表で許される変換だけ（表は sema と共有する） | R-82 |
| V-04 | ローカルは、スコープの中で定義してから使う。分岐やブロックの中で定義したものは外で使えない。代入では定義にならない | R-82、R-06 |
| V-05 | 代入先と `inout` の引数は、書き込める場所である（借用で受け取った引数には書けない） | R-82 |
| V-06 | `rt` の関数から呼べるのは、`rt` の関数と、表で rt とされたプリミティブだけ | R-82、R-79 |
| V-07 | `break` / `continue` はループの中だけにある | T3-2 |
| V-08 | `Switch` は網羅的である | T3-2 |
| V-09 | 書き込みを持つ式と、文を含む式は、文の位置にだけある（正規形の R1） | R-81 |
| V-10 | 文の位置の式の木に含まれる、効果を持つ演算は一つまで（正規形の R2） | R-81 |
| V-11 | 所有する値は、全ての経路でちょうど一度、移動か破棄される。移動・破棄の後は使わない | R-81 |
| V-12 | 破棄の種類は、型の破棄の種類と一致する | R-81 |
| V-13 | 集成体を作る式は宛先を持ち、宛先は構築に使う値と重ならない（判定は §5.2 と同じ関数） | R-81、S-76 |
| V-14 | `sret` の印は返り値の型と一致し、`sret` の関数は返り値の置き場所のローカルを持ち、NRVO の記録はそれと一致する | R-81、R-80 |
| V-15 | ターゲットの pass の後: 記録した配置の性質（オフセットはアラインメントの倍数、フィールドは重ならない、大きさは最後のフィールドの終わり以上でアラインメントの倍数、bulk 領域には `@mem(bulk)` のフィールドだけ） | R-80、R-82 |
| V-16 | ターゲットの pass の後: flow のメタデータ（入力、出力、パラメータ）が、`State` / `Params` の型と生成した関数のシグネチャと一致する | R-82 |
| V-17 | flow の `init` は、状態の全てのフィールドを設定する。設定しないのは、flow の計画（§3.5）が「段の順で読む前に必ず書かれる」と記録したフィールドだけ | R-92 |

正規形の R3（評価順に並べる）と R4（条件の内側に出す）は、Core から元の順序が分からないので検証器では確かめない。評価順の再現の期待値付きテストと、インタプリタと C の差分テストで押さえる（R-81）。
- テキスト形式 `onsa dump --core`（隠しコマンド）を持ち、golden テストにも使う。
- 追記（2026-10-05、レビュー R-92）: Core は「任意の型の、全てのビットが 0 の値」（`Zeroed`）を持たない。役割ごとに明示の形にする。
  (1) 後で全てを書く配列（`array.from_fn`、`par` の複製の結果）は、長さと「添字から要素を作る本体」を持つ「添字で配列を作る式」で表し、各要素を宛先に一度だけ作る（R-81 の結果の置き場所と所有の規則に合う。Affine の要素でも仮の値を上書きしない）。
  (2) flow の状態の初期値は、`init` が全てのフィールドを意味のある値で設定する（遅延と `prev` の初期値、省略時は `T.default()`（S-29、S-49）、書き込みの位置は 0、`poisoned` は `false`、`sample_rate` は引数）。
  段の順で読む前に必ず書かれるフィールド（`sample` から読まれる `block` の `let`、巻き上げた部分式）は flow の計画にその性質を記録し、Core では設定しないと明示する（言語からは観測できないので、バックエンドは決定的にするために 0 のビットで埋めてよい）。
  「型の既定値（`T.default()`）が全て 0 のビットか」は Core の型の情報として一度だけ決め（組込みの数・`Bool` と、それらだけを並べた derive の既定値は「全て 0」、手書きの `impl Default` は明示の値で設定する）、バックエンドは `memset` にまとめてよい。`T.ZERO`（`Num` の加法の単位元）とは別のもので、初期値には使わない。
  インタプリタは、型の合わない値を黙って 0 として扱わず、内部エラーにする（検証器の V-02 をすり抜けたときの備え）。

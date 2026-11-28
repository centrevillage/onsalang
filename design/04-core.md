### 3.4 Core IR（`onsa_core`）

```rust
pub struct Module { types: Vec<TypeDef>, consts: Vec<ConstDef>, fns: Vec<FnDef>, flows: Vec<FlowMeta> }
pub struct FnDef {
    name: QualName,                       // dsp.voice.tick の形。C では __ 区切り
    params: Vec<Param>,                   // Param { local, mode: Borrow|Inout|Move, ty }
    ret: Ty, sret: bool,                  // 集成体を返すなら sret = true（§12.7）
    rt: bool, locals: Vec<Local>, body: Block,
    decl: Option<DefId>,                  // 元の宣言。`__eq` と flow の生成する関数は None（S-911）
    hoisted: Vec<LocalId>,                // 記憶域を関数の高さに置く局所変数（R-481。下の注）
}
pub enum Stmt { Let(LocalId, Expr), Assign(Place, Expr), Expr(Expr),
                If(Expr, Block, Block), While(Expr, Block), ForRange { local: LocalId, lo: Expr, hi: Expr, body: Block, inclusive: bool },
                Break, Continue, Return(Option<Expr>) }
pub enum Expr { Lit(Lit, Ty), Local(LocalId), Const(ConstId),
                Unary(UnOp, Ty, Box<Expr>), Binary(BinOp, NumTy, Overflow, Box<Expr>, Box<Expr>),  // Overflow: Checked|Wrap|Sat
                Cmp(CmpOp, Ty, ..), Cast(Ty, Ty, ..), Call(FnId, Vec<Arg>), Prim(PrimId, Vec<Expr>),
                Field(Box<Expr>, u32), Index(Box<Expr>, Box<Expr>, Bounds),  // Bounds: Checked は境界検査付き、Known は process のサンプルループの入出力（S-196。dump は `xs[known i]`）
                Struct(Ty, Vec<(u32, Expr)>), Array(Vec<Expr>),  // Struct: （欄の番号, 式）を書いた順に（§3.5）
                Repeat(Box<Expr>, u32), Tuple(Vec<Expr>),
                IfExpr(..), Switch(Box<Expr>, Vec<(Tag, Block)>),  // enum のタグで分岐。束縛は Field で取り出す
                Panic(MsgId) }
pub enum Place { Local(LocalId), Field(Box<Place>, u32), Index(Box<Place>, Expr, Bounds) }
```

（略記。今の定義は `crates/onsa_core/src/ir.rs`）

- 型は `Module.tys`（`Types`）の id の `CTy` で引く。`Types` は一段の `TyKind` を一度ずつ intern し、組込みの型は固定の id、struct と enum は `Module.types` を指す（W8-14 A1a）。型ごとの大きさ・並び・ビューを持つかは `Module.facts`（`design/03-types.md` の「大きさと配置」の項）。
  降下は降ろせない型（この版の `Str`・Shared を含む型など）の代わりの型を作らない: そういう型を束縛か式の型に持つ単位は降下せず、E0200 を出す（束縛の段 `lower/body/mod.rs::bind_tys`、S-67 の判断、W8-16 B1）。

- 全ての式に型が付く。ジェネリクスは無い（単相化済み）。レートは無い（flow は降下済み）。
- `hoisted` は局所変数の記憶域の高さ（R-481、R-484、S-1118 (2)）。スコープ（`IfExpr`・`Switch` の腕と、`If`・`While`・`ForRange` のブロック）の外へ出る値（腕の値と、外の場所への代入）が届くビューの根のうち、そのスコープが宣言した局所変数を、`LocalId` の昇順で並べる。
  ブロック式は中の局所変数の寿命を閉じない。`Let` は腕の中のままで、バックエンドは記憶域を関数の頭に置き、`Let` を代入にする。判定は `lower/storage.rs` の一か所で、降下の `fold` の後に関数ごとに一度行う。
- `Prim` は `std.math` の `target` 宣言と組込みのメンバ（`trunc_sat_from`、`to_bits`、`Span.len` など）。`Prim` の一覧は `onsa_sema::prim` に置き（`onsa_core::prim` が再輸出する）、各バックエンドはこの一覧に対して対応表（`supports`）を持つ（表の欠けはテストで検出、`design/06-placement.md` の「`Prim` の表」の行）。
- `verify(Module)` は、常に（release も）段の境目ごとに走らせる（降下と正規化の後、ターゲットの pass の後）。失敗は内部エラー（終了コード 101、診断コード無し。S-67）で、破った規則の番号、関数名、Core の位置を報告し、その関数の Core のダンプを不具合の報告用に残す（レビュー R-82）。検証器は D-15 に従い、Core の構造から性質を確かめる。
  規則は次の一覧で全てである。規則ごとに、その規則だけを破った Core を手で作って検証器が拒むことを確かめる否定のテストを置く。Core の形を変えるときは、一覧・検証器・テストを一緒に直す。

| 番号 | 規則 | 出典 |
|---|---|---|
| V-01 | 式の型が、式の種類ごとの規則と一致する（定数の初期化式を含む）。テストの関数は引数が無く値が `()`（§11.8） | T3-2、W8-02 |
| V-02 | プリミティブの引数の数・モード・型と結果の型が、`Prim` の表のシグネチャ（`onsa_core::prim::sig`。std の `target` 宣言と数とモードを単体テストで突き合わせる）と一致する | R-82、R-79 |
| V-03 | `Cast` は §3.3 の表で許される変換だけ（表は sema と共有する） | R-82 |
| V-04 | ローカルは、スコープの中で定義してから使う。分岐の腕と `If`・`While`・`ForRange` のブロック、`Logic` の右辺と `While` の条件と `Panic` の表示する値の中で定義したものは外で使えない（ブロック式は寿命と同じく名前のスコープも閉じない）。代入では定義にならない | R-82、R-06、W8-02 |
| V-05 | 代入先と `inout` の引数は、書き込める場所である（借用で受け取った引数には書けない。見るのは場所の根で、ビューの局所変数を通した書き込みは sema の検査に頼る） | R-82 |
| V-06 | `rt` の関数から呼べるのは、`rt` の関数と、表で rt とされたプリミティブだけ（`rt` は std の宣言の行から引く） | R-82、R-79 |
| V-07 | `break` / `continue` はループの本体の中だけにある（ループの条件と `for` の反復元は本体の外で、外のループのもの。§7） | T3-2 |
| V-08 | `Switch` は網羅的で、腕のタグは範囲の内で重ならない | T3-2 |
| V-09 | 書き込みを持つ式と、文を含む式は、文の位置にだけある（正規形の R1） | R-81 |
| V-10 | 文の位置の式の木に含まれる、効果を持つ演算は一つまで（正規形の R2） | R-81 |
| V-11 | 所有する値は、全ての経路でちょうど一度、移動か破棄される。移動・破棄の後は使わない | R-81 |
| V-12 | 破棄の種類は、型の破棄の種類と一致する | R-81 |
| V-13 | 集成体を作る式は宛先を持ち、宛先は構築に使う値と重ならない（判定は §5.2 と同じ関数） | R-81、S-76 |
| V-14 | `sret` の印は返り値の型と一致し、`sret` の関数は返り値の置き場所のローカルを持ち、NRVO の記録はそれと一致する | R-81、R-80 |
| V-15 | ターゲットの pass の後: 記録した配置の性質（オフセットはアラインメントの倍数、フィールドは重ならない、大きさは最後のフィールドの終わり以上でアラインメントの倍数、bulk 領域には `@mem(bulk)` のフィールドだけ） | R-80、R-82 |
| V-16 | ターゲットの pass の後: flow のメタデータ（入力、出力、パラメータ）が、`State` / `Params` の型と生成した関数のシグネチャと一致する | R-82 |
| V-17 | flow の `init` は、状態の全てのフィールドを設定する。設定しないのは、flow の計画（§3.5）が「段の順で読む前に必ず書かれる」と記録したフィールドだけ | R-92 |
| V-18 | `hoisted` の局所変数は、本体のどこかの `Let` で定義し、本体の一番上の `Let` では定義しない（引数と `ForRange` の変数は `Let` を持たず、NRVO の局所変数は一番上の `Let`） | R-481 |
| V-19 | 範囲の内と決まった添字（`Bounds::Known`）は、flow に生成した `process`（`FlowFns::process`、名前で比べない）のサンプルループ（`ForRange`）の中にだけある | S-196 |
| V-20 | ID（`FnId`・`ConstId`・`TypeId`・`LocalId`・`MsgId`・`CTy`）と、欄・組の要素・列挙子・`Payload` の番号が範囲の内で（`Switch` の腕のタグは V-08）、型の表の部分の `CTy` は自分より前にあり、型の事実の表（`Module.facts`）が型の表の全ての型を覆い、フィールドを読む型と構造体のリテラルの型が `Opaque` でない | R-82、W8-02 |
| V-22 | 式と文の入れ子の深さ（節点は `Block`・文・式・`Place`、関数の本体と定数の初期化式が 1）が `CORE_DEPTH_LIMIT`（1400）以下。降下の直後と各段の検証の頭で、明示のスタックで数える。§2.5 の深さの内の正しいプログラムは、定数の値の入れ子（宣言の鎖に比例、R-319 の残り）が上限を超えない限り通る（超えれば内部エラー。利用者の判断） | R-319、W8-02 |

正規形の R3（評価順に並べる）と R4（条件の内側に出す）は、Core から元の順序が分からないので検証器では確かめない。評価順の再現の期待値付きテストと、インタプリタと C の差分テストで押さえる（R-81）。
- テキスト形式 `onsa dump --core`（隠しコマンド）を持ち、golden テストにも使う。
- 追記（2026-10-05、レビュー R-92）: Core は「任意の型の、全てのビットが 0 の値」（`Zeroed`）を持たない。役割ごとに明示の形にする。
  (1) 後で全てを書く配列（`array.from_fn`、`par` の複製の結果）は、長さと「添字から要素を作る本体」を持つ「添字で配列を作る式」で表し、各要素を宛先に一度だけ作る（R-81 の結果の置き場所と所有の規則に合う。Affine の要素でも仮の値を上書きしない）。
  (2) flow の状態の初期値は、`init` が全てのフィールドを意味のある値で設定する（遅延と `prev` の初期値、省略時は `T.default()`（S-29、S-49）、書き込みの位置は 0、`_poisoned` は `false`、`_sample_rate` は引数）。
  段の順で読む前に必ず書かれるフィールド（`sample` から読まれる `block` の `let`、巻き上げた部分式）は flow の計画にその性質を記録し、Core では設定しないと明示する（言語からは観測できないので、バックエンドは決定的にするために 0 のビットで埋めてよい）。
  「型の既定値（`T.default()`）が全て 0 のビットか」は Core の型の情報として一度だけ決め（組込みの数・`Bool` と、それらだけを並べた derive の既定値は「全て 0」、手書きの `impl Default` は明示の値で設定する）、バックエンドは `memset` にまとめてよい。`T.ZERO`（`AnyNum` の加法の単位元）とは別のもので、初期値には使わない。
  インタプリタは、型の合わない値を黙って 0 として扱わず、内部エラーにする（検証器の V-02 をすり抜けたときの備え）。

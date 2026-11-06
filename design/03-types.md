### 3.3 型と種（`onsa_sema`）

- `Ty` はインターン（`TyId(u32)`）: `Int`・`Float`・`Bool`・`Char`・`Unit`・`Array(TyId, Len)`・`Tuple`・`Named(DefId, Vec<TyId>)`・`Builtin(BuiltinTy, Vec<TyId>)`（`Str`・`Bytes`・`Array`・`Map`・`Set`・`Buf`・`Span`・`Ptr`）・`Fn(FnTy)`・`Param`・`ConstVal`・`Var`（推論中）・`Error`。
  intern は深さと大きさと「open か」を一度だけ計算して持つ（上限は `TYPE_DEPTH_LIMIT` 256・`TYPE_SIZE_LIMIT` 4096、§4.4、S-264）。型引数の代入は `Types::subst` の一つ（R-30）。
  クロックは型ではなく、flow の計画（§3.5）の属性である（S-102 で `Rate(Rate, TyId)` を取り除いた）。
- 種（`Kind::{Copy, Shared, Affine}`）・配置・`rt` の破棄は、`walk.rs` の宣言を辿る一つの歩きが読み、宣言と閉じた引数の組ごとに一度だけ答える（`Known`、R-30）。
- 大きさと配置は、Core の降下の後のターゲットの pass が計算して Module に記録する（レビュー R-80、D-03 の追記）。`onsa interface`、`SIZE`、`_Static_assert`、プローブ、ホットリロードは記録を読む。sema は大きさを計算しない。
  W9-04 までは、`onsa interface` が型の宣言の大きさと配置を sema の `layout.rs`（`layout_of_def`）から、enum の tag の型を `layout::tag_kind` から読む（`sema` の `layout.rs` を消すのは W9-04）。
- 推論の状態は `Infer`（`infer.rs`。変数は束縛か、整数・浮動小数のリテラルの制約を持つ未束縛）。文の順に進め、型が決まってから確かめる検査は `Deferred`（`deferred.rs`）に並べて、文ごと（`check_deferred_now`）と本体の終わり（`check_deferred_end`。整数リテラルを `I32` にした後、S-22、仕様 §4.7）に確かめる（未解決の浮動小数リテラルは E0405）。
  `const` の宣言の型は、置ける所を `kind.rs::placed` が決める（置けない型は E0407、この版で置けない型は E0200。`body/entry.rs::const_type`、S-773）。
- 名前の解決（レビュー R-84、S-78、D-15）: 型付けの前に一つの段を置き、本体の全ての経路と呼び出し先を一度だけ解決して `BodyNames`（`names/body/mod.rs`）に記録する（式は `PathRes`、パターンは `PatRes`、構造体リテラルは `StructRes`）。
  この段が決めるのは、経路の先頭（ローカル、`self`、型と定数のパラメータ、モジュールの項目、`use` の名前、prelude、組込み型）、モジュールと flow の名前空間の経路、列挙子、型の関連項目（`Point.new`、`F32.PI`、`T.ZERO`、`Fs.read`）、flow の予約名（`prev`、`delay`、`vdelay`、`sample_rate`）。
  値の後のフィールドとメソッドの呼び出しは、値の型が要るので型付けに残す。型別名は、この段で一度だけ元の型（型引数を含む）に解決する（S-91）。型付けは解決の記録を読み、解決をやり直さない。名前の隠蔽は全て E0304（S-79）なので、ある位置の名前が指すものは一つで、優先順位の規則は要らない。
  名前の段は `names/`（木・項目・`use`・衝突・閉路・`typed`・`rename`）と `names/body/`（本体の歩き。`scope`・`exprs`・`calls`・`flow`・`paths`・`kinds`・`cycles`）に分かれる。
- パッケージのモデル（レビュー R-88、S-83、D-15）: パッケージは ID で識別し、パッケージごとに「見える依存の表（キー → パッケージ ID）」を持つ。同じパッケージ（同じ名前と版）は一度だけ解析し、同じ DefId を共有する（菱形の依存で二重に解析しない）。名前で見えるのは、そのパッケージが宣言した依存と暗黙の `std` だけ（§15.1）。
  std は名前ではなく役割（driver が読み込んだ埋め込みの std に付ける印）で見分け、std の特権（`target` 宣言、組込み型への `impl`、効果の宣言、lang item）は全てこの役割を読む。依存の図は driver が一度だけ作り、sema は受け取る。
  今の依存は std だけだが、作りは std 以外の依存を受けられる形にする（取得元と版の解決は第 2 期、計画 §5）。`std = "x.y.z"` は埋め込みの std の版と比べる。
- 束縛の状態（`binding/`。レビュー R-85、R-54、S-80、D-15）: 一つの列挙（所有・不変／所有・可変／借用／`inout`）で表し、借用で書き換えられるような仕様に無い組み合わせを作れなくする。状態は一度だけ決めて記録し、modes、使用の記録（R-83）、Core への降下（R-81 の移動・コピー・破棄）は記録を読む。
  §5.4 の表は、初期化の元の形（名前の段で分かる）と、破棄の要らないリテラルの要素の種（本体の型の推論の後に分かる）で決まる（S-613）。要素が束縛の名前なら、先に確定したその束縛の状態を引く（S-613 の補い L4）。確定は本体の推論が解けた後、modes の前に一度だけ行う。型付けは束縛の状態を判定に使わない。静的な値と破棄の要らないリテラルの判定も確定の中で一度だけ行い、名前の段の印は置かない（W4-16 の設計メモ、84 回目）。
  判定は表を写す一つの関数で、AST の束縛の場所の種類で `_` 無しに分岐する（文法に束縛の場所を足すと、分類するまでコンパイルが通らない）。表の行ごとにテストを置く。無名関数が Shared 型の値を捕捉する行は未決定なので、E0200 にする（計画 §5 の持ち越し。捕捉を見る modes が出す、W4-07）。
- 本体の段の順（S-267、S-64）: `stages::check_bodies` の一か所に、名前（`names::body::walk_bodies`）→ 型付け（flow の本体の型付けと flow の検査は一度の歩き）→ 束縛の状態（`binding::settle_all`、診断なし）→ modes → `rt` → 効果の順を書く。
  ある単位で前の段が誤りを出したら、後の段はその本体を飛ばす。印は診断の段から `Failures::of` が単位ごとに作り（`Failures::skips`）、読む本体は `Analysis::body_checked(def, 段)` の一つの問いで決める。署名は本体の前に全ての単位で検査する。未使用の束縛（E0309）は最後の段で、他の誤りのある単位では選ばれない（S-726）。
- 名前の段と署名の段（レビュー R-84、R-50、D-15）: 名前の段（`names::collect_names`）が、モジュール木、prelude、項目の def と表、各 `use` の解決（`names/imports.rs`、S-37）、名前の衝突と `use` の閉路を作る。
  署名の段（`sig::collect_and_lower`）は、(1) 型の宣言の順と閉路（`sig/decls.rs::order_declarations`。`impl` のメンバの表は `name_members` が一度の環で埋め、別名の `impl` の鍵は別名の右辺の頭を下ろさずに辿る）、(2) 署名の型の降下（`lower_signatures`。部品は `sig/heading.rs`・`derives.rs`・`impls.rs`・`types.rs`）、(3) flow の生成項目の型（`lower_generated`）、(4) 型の整形性（`sig/wellformed.rs`: E0710、E0416）、(5) `@param` と生成項目の検査（`check_generated`）の順で、各段は前の段が作った表を読む。
  本体の型付けは署名の表を読み取り専用で参照し、`Analysis` を `mem::take` で取り出さない。
- 効果と `rt` の判定（レビュー R-83、S-77、D-15）: 型付けと modes（経路を見た破棄の点、R-32）の後に、「使用の記録」を作る段を一つ置く。記録は本体（関数、無名関数、`test`、定数の初期化式）ごとに、使う効果とその位置と理由（呼び出し、関数値の呼び出し、効果の操作、補間などの暗黙の確保、破棄）と、呼ぶ関数（`rt` かどうか）を持つ。
  E0601、E0901、E0903、第 2 期の E0642 などは、この記録を読む判定にする（E0902、E0904、E0905、E0610 は署名だけで決まる）。効果の判定は全ての関数で同じで、`rt` は効果行の制限と呼び出しの規則を足すだけにする。無名関数の使用は外の関数に数えず、期待する関数型の効果行と照合する（§8.1、R-27）。
  `test` の本体と定数の初期化式は `Alloc` を与えられる（D-08、§6.6）。報告は 1 つの本体につき最初の 1 件（`rt.rs::body_rules`、`effects.rs::first_use`）で、単位の中の選び方は driver の `reduce::per_unit`（S-59、S-64）。
  E0903 の辺は `rt_checked` な関数の呼び出しだけで、辺が欠ける関数を通る閉路は報告しない（`unread.rs` の `rt_unread`・`rt_held`）。具体化で決まる循環（`T.default()`、derive が作る関数を経る形）は `rt.rs` に見えないので、`onsa_core` の `rt_cycles.rs` が降下の後の `Call` の辺で調べる（S-911）。E0601 の形は S-77。今は `rt.rs` と `effects.rs` が別々に使用を集める（使用の記録の段は W6-03）。
  効果行は「効果の宣言の ID の集合 + 効果行の変数」で表し（S-74 で名前を解決するため）、`Alloc` は lang item の一つにする。
- lang item の表（2026-10-06、点検 C-84）: コンパイラが std の項目について知るのは、この表（std の経路 → 役割）だけで、他の文書はここを指す。std は役割の印で見分ける（R-88）。
  - 演算子の脱糖: 演算子 trait（§3.2、§6.3 の表）
  - 補間: `Show`
  - 既定値: `Default`（`T.default()`、遅延の省略した `init`、S-29）
  - 破棄: `Drop`
  - derive: 宣言の頭に並べられる trait の閉じた一覧（§6.4）
  - 反復: `IntoIter`（消費する反復）と `Iter`
  - （S-140 で外した: `Copy` と `Dup` は trait ではなく種の制約で、std に宣言しない。名前はコンパイラが prelude に与え、境界の判定は §4.6 の種の計算を直接使う。型パラメータの暗黙の要求 `Escape`（§4.5、S-862）も同じくコンパイラが与える）
  - 数: `AnyNum`、`Num`、`Float`、`Int`、`Unsigned`（E0401 の修正候補と E0416 の note、`vdelay` の `T: Float`、S-84）。`Float` は組込みの浮動小数だけが実装する（S-108）
  - `Option` / `Result` とその列挙子（prelude と `?`、S-71）
  - `Alloc`（prelude と効果の判定、S-74）

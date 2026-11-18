### 3.5 flow の降下の形

- 追記（2026-10-05、レビュー R-92）: flow の計画は、状態のフィールドごとに「`init` で設定する値（遅延の初期値、`T.default()`、0、`false` など）」か「段の順で読む前に必ず書かれる（`init` では設定しない）」かを記録する。`init` の降下はこれを読み、状態を `Zeroed` で作ってから一部だけ代入する作りをやめる（§3.4 の追記、検証器の V-17）。
- 追記（2026-10-05、レビュー R-91、D-15）: sema の flow の検査が、flow ごとに「flow の計画」を一つ作って記録する。
  計画は、ノードの一覧（`let`、巻き上げた部分式（S-33）、インスタンス、遅延の組込み、`par`）、各ノードのレートと評価の段（`init` / `ctl` / `tick`）、状態のフィールドの一覧（§11.6 / S-65 の名前。名前を作る処理は一つの関数）、ノードの所属（スパンの包含ではなく木の構造で）、依存と帰還（`^`）の辺を持つ。
  `let` と入力を状態に入れる判断は、計画を作るときに一度だけ行う（今は sema の一度の走査（`onsa_sema/src/flow/reads.rs` の `mark_all`）が読む段の集合 `FlowInfo.read_at` と `let` の状態を出し、入力を状態に入れる判断と定数の `let` の相は Core の降下が `read_at` から決める。X-6 の RF-8 (B)、2026-10-19）。
  Core の降下、`onsa graph`、`onsa interface` は計画を読むだけにする。子の列挙は一つの関数にする（`onsa_syntax` の `Ast::sub_exprs` を sema の `mark` と `onsa graph` が呼ぶ。X-6 の RF-8 (A)、2026-10-19）。
  クロックは不動点の反復をやめ、一つの歩き（`onsa_sema/src/flow/clocks.rs`、W7-02）で決める（追記 2026-11-18、W7-02 U2b-2）。段 1 は、各 `let` が読む `let` の辺（結果のクロックが被演算子によらない位置、つまり利用者の flow の引数・`at` の被演算子・遅延の `d` と `init` は切る）から輪の成分を求め（`flow/loops.rs`）、成分ごとに一度解く（輪の `let` は一つのクロック、§11.3、S-567）。段 2 は `let` を字面の順に歩いて全ての式と局所のクロックを記録し、flow の規則の検査を当てる（本体を歩き切り、§18.1 の並べ方で最初の診断を残す。誤りの部分のクロックを使う検査は出さない、S-1133）。歩きは本体の大きさに線形で、反復の上限を持たない。
  追記（2026-10-05、R-98、S-86）: 計画は、各ノードの構造上の位置（含む `let` か出力と、式の中の経路）も持ち、LSP の拡張と `onsa interface` に出す。ホットリロードとプローブの付け替えは、生成する名前ではなくこれで旧新を照合する（§18.3）。
  名前は §11.6 の規則（含む `let` で修飾、`let` ごと・種類ごとに字面の順）で、計画を作る一つの関数が付ける。

D-03 の 5 関数。§17.3 の `resonator` なら次の形になる（擬似 Onsa）。

```
struct resonator.State {
  _sample_rate: F32  // block の値の計算に使う（§12.4）
  b1: F32            // sample から読まれる block の let。r と w は block の中でしか使わないので置かない
  b2: F32
  y._hoist_0: F32    // 巻き上げた部分式 1.0 - r（S-33。sample の式の中の block の部分式）
  y1: prev[F32]      // prev~(^y) の保存値
  y2: prev[F32]      // prev~(y1) の保存値
  _poisoned: Bool
  _initialized: Bool // export の境界（S-27）
}
fn resonator.init(cfg: resonator.Config, sr: F32) -> State {
  // b1、b2、y._hoist_0 は ctl が読む前に必ず書くので設定しない（R-92）
  State { _sample_rate: sr, y1: 0.0, y2: 0.0, _poisoned: false, _initialized: true }
}
rt fn resonator.reset(inout s) { s.y1 = 0.0; s.y2 = 0.0; s._poisoned = false }
rt fn resonator.ctl(inout s, params: Params) {
  let r = exp(-(F32.PI * params.bw) / s._sample_rate)   // 状態に置かないローカル
  let w = (2.0 * F32.PI * params.fc) / s._sample_rate
  s.b1 = 2.0 * r * cos(w)
  s.b2 = r * r
  s.y._hoist_0 = 1.0 - r
}
rt fn resonator.tick(inout s, x: F32) -> F32 {
  let y1 = s.y1                       // 遅延の出力（保存値）を先に読む
  let y2 = s.y2
  let y = s.y._hoist_0 * x + s.b1 * y1 - s.b2 * y2
  s.y1 = y                            // 保存はまとめて最後に（R-13）。prev~(^y): y を保存
  s.y2 = y1                           // prev~(y1): y1 を保存
  y
}
rt fn resonator.process(inout s, params, input: Span[F32], inout output: Span[F32]) {
  // 長さの検査（違えば panic）
  resonator.ctl(inout s, params)
  for i in 0..<input.len() { let xi = input[i]; let yi = resonator.tick(inout s, xi); output[i] = yi }
}
```

- 遅延の保存は、全ての遅延の出力を読み、保存する値を全て評価した後に、`tick` の末尾でまとめて行う（仕様 §11.4、R-13 の二相化）。遅延の値の式の中の遅延（`prev~(prev~(x))`）は保存の前の出力を読む。複数の `prev~` が同じ信号を参照しても、保存は各ノードが独立に持つ。
- `delay` / `vdelay` は §11.4 の演算順をそのまま `tick` の中に展開する（関数にしない。順序を固定したいため）。
- 分岐（S-110）: 普通の `if` / `match` の枝と `&&` / `||` の右辺は、条件の内側に降下する（取られた枝だけを評価する。枝に状態を持つものは無い）。`if~` / `match~` は全ての枝を評価してから選ぶ（評価済みの値の選択）。
  flow の計画は、普通の `if` の枝と評価されないことがある右辺から、panic しうる部分式を巻き上げない（演算の分類は R-81 / R-79 の `Prim` の表。利用者の関数の呼び出しは、panic しないと分からなければ panic しうるとみなす）。
- 親の `tick` は子の `tick` を `Call` で呼ぶ。子の `block` の入力に渡す親の値は、親の `ctl` で子の `Params` を組み立てて子の `ctl` を呼ぶ。
- `par` は `[sub.State; N]` と `ForRange` に落とし、`i` はループ変数（`init` のクロックの値）。
- （2026-10-06、点検 C-66: 例を S-27、S-30、S-33、S-44、S-86、S-102、R-13、R-92 に合わせた。名前と巻き上げの細部は点検の C-36。）

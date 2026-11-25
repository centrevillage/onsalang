### 3.5 flow の降下の形

- 追記（2026-10-05、レビュー R-92）: flow の計画は、状態のフィールドごとに「`init` で設定する値（遅延の初期値、`T.default()`、0、`false` など）」か「段の順で読む前に必ず書かれる（`init` では設定しない）」かを記録する。`init` の降下はこれを読み、状態を `Zeroed` で作ってから一部だけ代入する作りをやめる（§3.4 の追記、検証器の V-17）。
- 追記（2026-10-05、レビュー R-91、D-15）: sema の flow の検査が、flow ごとに「flow の計画」を一つ作って記録する。
  計画は、ノードの一覧（`let`、巻き上げた部分式（S-33）、インスタンス、遅延の組込み、`par`）、各ノードのレートと評価の段（`init` / `ctl` / `tick`）、状態のフィールドの一覧（§11.6 / S-65 の名前。名前を作る処理は一つの関数）、ノードの所属（スパンの包含ではなく木の構造で）、依存と帰還（`^`）の辺を持つ。
  `let` と入力を状態に入れる判断は、計画を作るときに一度だけ行う（追記 2026-11-18、W7-03 U1b `ba630624`: sema の走査（`onsa_sema/src/flow/reads.rs` の `mark_all`）が読む段の集合 `FlowInfo.read_at` を出し、状態に入れる判断は `FlowInfo::stored` の一か所（`FlowLet.state`、入力の欄、`sample_rate` の欄。`onsa_sema/src/flow/plan.rs`）で行い、欄の一覧は計画が struct ごとに作る（`plan/fields.rs`）。定数の `let` の相は、W7-08 U1（`7958c63f`）から Core の降下が計画の問い合わせ `FlowInfo::consts_at`・`lets_at`（`onsa_sema/src/flow/plan/stage.rs`）で読む。X-6 の RF-8 (B)、2026-10-19）。
  Core の降下、`onsa graph`、`onsa interface` は計画を読むだけにする。子の列挙は一つの関数にする（`onsa_syntax` の `Ast::sub_exprs` を sema の `mark` が呼ぶ。X-6 の RF-8 (A)、2026-10-19）。
  追記（2026-11-20、W7-15 U2 `a2fddcc9`・U3 `5208cbd2`）: 計画は依存と帰還の辺（`FlowInfo::edges`、`Vertex`・`Edge`）を段 2 のクロックの歩きで `NodeBuilder` が記録して持ち、`par~` の上端の形（`RangeEnd`）も持つ。`onsa graph` は節点と辺を計画から読み、AST を歩かない。
  クロックは不動点の反復をやめ、一つの歩き（`onsa_sema/src/flow/clocks.rs`、W7-02）で決める（追記 2026-11-18、W7-02 U2b-2）。
  段 1 は、各 `let` が読む `let` の辺（結果のクロックが被演算子によらない位置、つまり利用者の flow の引数・`at` の被演算子・遅延の `d` と `init` は切る）から輪の成分を求め（`flow/loops.rs`）、成分ごとに一度解く（輪の `let` は一つのクロック、§11.3、S-567）。
  段 2 は `let` を字面の順に歩いて全ての式と局所のクロックを記録し、flow の規則の検査を当てる（本体を歩き切り、§18.1 の並べ方で最初の診断を残す。誤りの部分のクロックを使う検査は出さない、S-1133）。歩きは本体の大きさに線形で、反復の上限を持たない。
  追記（2026-11-21、W7-09 U2s `74f47cae`・U3b `5ea62044`・U4b `bc26c389`）: 式の評価の段は、歩きが一度だけ作る表（`onsa_sema/src/flow/clocks/stages.rs`、`ClockInfo::stage`）を引く（`at` を透かす、S-1196）。
  修飾子の連鎖は頭ごとに `FlowCx::chains` に置き、計画の `PlanNode::frame`・`chain` が枠の比と修飾子の並びを持つ（S-1088）。誤りのクロックを作る判定は段 1 でも走らせ、報告だけを段 2 に残す（R-496）。
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
  flow の計画は、条件の位置（`if` / `match` の枝、`match` のガード、`&&` / `||` の右辺）の中の `init`・`block` の式を、その位置を選ぶ条件が全て `init`・`block` の段で決まるときだけ、条件を守りにした欄として巻き上げる。条件のどれかがサンプルごとに決まるなら、届いたときに評価する（S-1157。panic しうる部分式の分類は要らない、S-1080）。
  追記（2026-11-25、W7-11 U2c）: 名前のフィールド・組の要素の読み（`s.vel at sample`）は守り無しの欄（`Hoist::guarded` が偽）で、一番外の条件の手前に一度だけ書く（`hoist::placed`。条件の位置の仕事を、守り無しの欄だけの歩きと、守り付きの欄の歩きの二度に分ける。S-1197）。
- 親の `tick` は子の `tick` を `Call` で呼ぶ。子の `block` の入力に渡す親の値は、親の `ctl` で子の `Params` を組み立てて子の `ctl` を呼ぶ。
  追記（2026-11-23、W7-16）: 子の遅い刻みの段（`tick_<N>`）も、呼び出し側のその段（`Entry::caller`）の関数の中で呼ぶ。子の段の関数を呼ぶ口は `phases::call_stage` の一か所で、時間の語は段が取る数に切って渡す。
- `par~` は `[sub.State; N]` と `ForRange` に落とし、`i` はループ変数（`init` のクロックの値）。状態を持つものの無い `par` は状態のフィールドを作らない（S-1177）。
- 追記（2026-11-23、W7-16 U5a〜U7）: 遅い刻みの段・時間・連鎖の降下。
  - 段は sema の `ClockStage`（`Init`・`Block`・`Tick(k)`。`Tick(0)` が本体の `sample`）。`sample / N` の段（`FlowInfo::stages`。呼び先の遅い段も含む）は段ごとの関数 `tick_<N>(inout s, [t], <その段の入力>)` に降ろし、`tick` は `sample` の段の関数である。一つの生成器 `phases::gen_stage` が段を引数に取る。
    段の中の順は、保存する入力、`let` を上から、出力、段の終わり（遅延の保存と、`FlowInfo::late` のもの。`phases::end`、`StageCx::saving`）（§11.3、S-1233）。
    `let` と出力の式の中のその段の仕事（巻き上げた欄、検査、呼び先の段、遅延の `init`）は、書いた位置で `hoist::work` の一つの歩きが行う（インスタンスは `nodes::instance`、遅延は `nodes::delay_work`。一つの呼び出しは一つの関数で一度、`StageCx::done`）。
    `process` は遅い段を、位相のカウンタが N の倍数のときに `phases::drive` で呼ぶ（最初の刻みで動き、ホストの区切りに依らない、§11.9）。
  - `sample_tick()` は一番外の `process` のカウンタ `_tick`（`.down~` の先で読む flow だけが上の桁の欄 `_tick_hi` も持つ、S-1217・S-1211）から、段の関数の引数 `t`（と `t_hi`）で渡す。引数を取るのは時間を読む段の関数だけ（`FlowInfo::time_words`）で、時間を読まない flow に時間の欄・引数・演算は無い。
    カウンタを進める所は `FlowInfo::counter()`（遅い段を持つ flow は `tick` の末尾、時間だけの flow は `process` の `phases::advance`）。子へ渡す時間は連鎖の境界ごとに畳む（`chain::fold`、`child_time`）。子の `sample_rate()` も境界ごとに割る・掛ける（`child_rate`）。
  - 連鎖の降下は sema の手順の表を読む。`PlanNode::entries`（呼び出し側の段ごとの `Entry { caller, read, ops }`）の `Op`（`Ring`・`Run`・`Deal`・`Each`・`When`・`Reset`・`Hold`）と `Read`（`plan/steps.rs`: 内の修飾子から外へ一つの歩きで、境界・`when~`・`reset_if~` ごとに一つの腕）、`PlanBound`（`at`・`ratio`・`ins`・`out`・`conds`・`gathers`・`deals`）と `PlanGuard`（`at`・`cond`・`w`・`out`）が入出力と条件を読むクロックを持ち（どちらも `plan/bounds.rs` の一度の歩き）、Core は比から数え直さない。
    表の歩き（`plan/entries.rs`: 呼び先から先に、明示のスタックと `Open`・`Done` の印で循環を守る）が S-1089 の積（E0808）と段ごとの時間の語も決め、Core は表を読むだけにする（R-91 (1)）。
  - Core の `chain::entry` が一つの `Entry` の `ops` を歩く（`Walk`。`.up~` の走り j は `Walk::js`）。位置の算術は `counter`（位相の畳み込み）と `at`（窓の中の位置）に一つ、輪と配る配列への書き読みは `copy`（全体・要素一つ・`ForRange`）、頭の入力の切り出しは `window`。
    `Each` の腕は `for j` の本体に組ごとの `drive`、引数と条件は ops の前に字面の順に一度（`chain::ports`。読まないものは中のその段の仕事だけ）。集める輪と配る配列の欄の名前は S-1208（`<ノードの名前>._gather_<境界>_<入力>`・`._deal_<境界>`）。
  - 呼び出し側の `sample * N` の値と引数（束）は `[T; N]` で、型は `burst_ty` の一か所、束でない引数の N 個の複製は `spread` の一か所（頭の入力と輪の両方）。
  - 段の入口の表ができたので、Core の門（`multirate_at`・`lowered_chain`、`Feature::MultirateFlows`）は無い。
    Core が作れない形は `check` の段で止まる: `sample_tick()` を呼び出し側の `sample * N` になる引数に置く形は E0815（S-1218、`clocks/checks.rs` の `check_arg`）、連鎖と合成したクロックの N が `U32` を超える形は E0808（S-1216、`plan/entries.rs` の表の歩き。判定は `Ratio::made_n` の一か所を Core の `chain::len`・`Clock::burst_len`・`phases::drive` も読む）。
- 追記（2026-11-24、W7-10）: `when~`・`reset_if~` の降下。
  - 手順の表の `Op::When { guard, cond, due, ops, advance }` は、守りが包む部分の仕事である。条件は W で読み（`CondRead::Read`。`Part::On` に残すのは、表に `Kept` の読みがあるときだけ）、W より遅い段は W へ寄せて、動いた刻みの数 `Part::Count` の格子で動かし、W より速い段は `Part::On` に残した条件で守る。
  - `Op::Hold` は、束でない部分の保持した出力 `Part::Held` を出す。束では、動いた刻みの配列の最後の要素を保って N 回読む（S-1222）。
  - `Op::Reset { at }` は `reset_if~` で、条件の刻み R の段の仕事の並びの先頭に置く（S-1228 の (P)）。刻み R は `PlanModifier::reset`、条件のポートは `PlanModifier::port`（書き手は歩きの一か所）。
    Core は、頭を `<flow>._reset_kept`（`phases::ensure_reset_kept`、`reset_node` の `Keep::Kept`。`reset` からカウンタ・`_poisoned`・守りの条件と数を除いたもので、使うときだけ作る）で戻し、内の輪・配る配列・保持を `T.default()` に戻す。
  - 条件の `sample_tick()` だけの式は、W の `at` を付けた式と同じに扱う（S-1230。`guard_cond` の `ArgRead::at` が W、`settle` が根を W に落とし、外の `when~` で読む段が速くなる所だけ `Choose::place` が W の段の隠れた欄に置く）。
  - 境界の内に書いた条件は頭の入力と同じに集める（`Port::Cond`、`bounds::cond_ring`）。欄は `Part::On`・`Count`・`Held` と、`when~` で止まる遅延の `Part::Ran`（名前と並びは S-1220 の仮、`plan/names.rs`）。
  - 組込みの遅延の受け手は `Ports::delay`（P = W = 第 1 引数のクロック K）で、表は段 K 一つ。保存は `store_node` が `Part::Ran` で守り、止まっている間も保存する値と `vdelay~` の `d` は評価する。
  - 修飾子の門（`ModifierChain::gate`・`check::gated`・`Feature::InstanceModifiers`）は無い。修飾子で E0200 にするのは `Feature::ResetTicksPastU32`（S-1225）だけで、イベントのクロックの条件は、`reset_if~` が下の U2r、`when~` が下の U3、他は E0200（W7-17）。
- 追記（2026-11-25、W7-11 U2）: イベントの段の降下（§11.11）。
  - 源（イベントの入力と、イベントを出す呼び出し）ごとの段 `ClockStage::Event(src)` を、関数 `ev_<k>(inout s, [t], [<複製の添字>], <イベント>)` に降ろす（`k` は `FlowInfo::events` の番号、`FlowFns::events`）。
    生成器は `phases::gen_stage` の一つで、段の中の順も遅い刻みの段と同じである。呼び出しの源の関数だけの枝は `StageCx` の二つで、`source`（引数のイベント）と `gave`（出力のイベントの受け）。
  - 計画の表（`plan/events.rs`、`plan/entries.rs` の `close`）: イベントの入力に結び付いた源ごとの `Entry`（同じ源の二つの入力は `Run` を二つ、宣言の順、S-1236）と、
    `EventPlan { src, from, parent, gives }`。`parent` は、作り手の出す段（`Op::Run { out: Out::Event }`）を呼ぶこの flow の段で、源は `parent` の森になる。
  - 呼ぶ所: `ev_<k>` を呼ぶのは、`chain::give`（作り手の `Run` の直後の `Switch` の `Some` の腕。式の途中のその場所、S-1234・S-1235）と、入力の源を刻む呼び出し側の `Run` だけである。
    時間は呼ぶ段の引数から取る（表が `parent` の語の数まで閉じてある）。
  - 作り手のノードは、自分のイベントの段では「引数と条件 → その段の ops → 値は `source`」（`nodes::instance`。周期の段で済んだ仕事は `done` が段の関数ごとなので混ざらない）。
  - 出力が呼び出しのイベントの flow は、出す段から `FlowInfo::emit` までの関数（`FlowInfo::gives`）が `Option` を返し、途中の関数は頭の局所 `__out`（初めは `None`）で受けて、保存の後に返す。
    見出しにイベントのある flow は `process`・`render` を作らない（`FlowDef::awaits_events`、W10-07）。
  - 場所の持ち直し: 書いた位置の値を後の文で読むもの（`chain::hold`。引数、段の終わりに読む条件）は、イベントのある flow では状態の欄も `let` に写す。間にイベントの段が走って欄を書くためである。イベントの無い flow の C は変わらない。
  - 段の終わりに評価する式の中のイベントの読み（S-1240・S-1249）: `^` を付けない読み（イベントの名前と、`^` を自分で読まないイベントの段の巻き上げ）は、書いた位置の値である。
    sema が、周期の遅延ごと（`PlanNode::saved`）と、段の終わりに回る遅い刻みの巻き上げごと（`Hoist::saved`）に、読む式の列を一つの関数 `events::saved` で作る。「`^` を自分で読む」（`^` で選ぶ `match`・`match~` の束縛も）は `FlowInfo::back`、道の条件も数える「段の終わりに回る」は `FlowInfo::late`。
    Core は、書いた位置の歩き（`lower_flow_expr`・`delay_work`・`hoist::work`）で第 1 引数か巻き上げの中の仕事の後に、`nodes::saved_reads` が列の値を局所に取り、`expr_override` に置く（条件によらず一度。欄の読みは panic しない）。
    イベントの段の遅延と巻き上げには要らない（読むのはその段の値だけで、段の間に変わらない）。
  - `reset_if~` だけの連鎖（U2r）: 条件が戻す段は `PlanModifier::reset`（`Tick` かイベント。書くのは `guard_cond` と、イベントの遅延の `event_delay_modifier`。イベントの遅延のパラメータの種類・定数・`sample_tick()` だけの条件は、遅延のイベント）。
    イベントの戻しは枠の段の表（`steps` の `Level`）に入れず、`events::entries` がその源の `Entry` の先頭に置く（外の修飾子が先。`Entry` は段ごとに一つで、S-1236 の二つの刻みの前に一度だけ戻す）。呼び出しにも遅延にも同じ関数を使う。Core は `Op::Reset` の今の道のままである。
  - 書いた位置から保存までの間に来る戻し（S-1250）: その段と違う段のイベントの戻しを持つ組込みの遅延だけが、欄 `Part::Open` と、戻しごとの `Part::Back(at)` を持つ（`PlanNode::late_flags`）。
    `Open` は書いた位置で立てる（`chain::opened`。読む所か、他の遅延の第 1 引数の中なら `delay_work` の終わり）。イベントの段の `Op::Reset` は、`Open` が立っていれば `Back(at)` を立てるだけにし、`store_node` が保存の後に `chain::stored` で両方を下ろして戻す。
    遅延の状態は書いた位置から保存まで変わらないので、段の終わりに読む入れ子と、`d` に `^名前` のある `vdelay~` も同じ規則で揃い、評価と panic の順は変わらない。遅延と同じ段の戻しは読みの前なので旗を見ない。
    `reset`（`Keep::Hard`）は旗も下ろす（間で panic した後）。`reset_if~`（`_reset_kept`）は、旗が下りている所でしか呼ばれないので触れない。旗は戻しの位置ごとなので、W7-17 で境界・守りと重ねても `reset_parts(at)` のまま使える。
  - イベントの値の条件の `when~`（U3、水準）: 条件を読む口（`guard_cond`）は W の刻みで、`Op::When` は周期の条件と同じに、書いた位置で読んだ値（欄なら `hold` の `let`）を使う。イベントの段では条件の欄を書くだけで、受け手は動かない。Core と計画の表に専用の枝は無い。
  - 段ごとの歩き: `let`（と出力）がその段の `let` でなくても段の仕事（呼び出しの仕事、遅延の保存）を持つかは `FlowInfo::work`（`work_in`）が持ち、段の関数はその `let` を書いた位置で歩く（S-1233）。
  - 複製と腕（W7-17 U6a）: `if~`・`match~` の腕・条件・対象・ガードと、外のイベントを読む `par~`・`par` は、周期の段と同じ歩き（`tilde_if_work`・`tilde_match_work`・複製の輪）で、専用の枝は無い。
    `par~` の中の呼び出しの源の段は、出した複製の本体だけを歩く（§11.11）。`ev_<k>` は、源のノードの `owner` の鎖の `par~` の添字（外から）を `ev` の前の引数で受け、`StageCx::pinned` に持つ。渡すのは `chain::give`（輪の中か、固定した関数の中で、どちらも添字は局所）である。
    複製の輪を作る口は `generated::replicas` の一つで、固定した `par~` は輪を作らず本体を一度だけ置き（`Replicas::each`。添字は `var - from`）、関数の頭の置き場所（`replicas_place`）もその次元を持たない。
    固定するのは `owner` の鎖だけで、内側の `par~`（`match~` の束縛を読む形）は輪のままである。入力の源の署名と計画の表は変わらない（複製の値がそのイベントのクロックになる形は E0815 なので、源の段の仕事はその複製の本体の外に無い）。
    遅延（か段の終わりに回る巻き上げ）が保存する式の中の `par` の計算した部分式は、`nodes::saved_reads` が、`Hoist::owner` から遅延の `owner` までの `par` の輪を書いた位置で開き、複製ごとの値を関数の頭の配列に取る（S-1240）。
  - 動かない形（`.when~`・`.up~`・`.down~` を含む連鎖の、イベントで動く受け手とイベントの `reset_if~`、`.up~`・`.down~` を含む連鎖のイベントの `when~`（どれも複製と腕の中でも）、自分の出力だけで刻む源。W7-17）は `FlowInfo::event_form` が持ち、`lower_flow` と `graph` が E0200 を出す（`FlowInfo::event_gate`）。
- （2026-10-06、点検 C-66: 例を S-27、S-30、S-33、S-44、S-86、S-102、R-13、R-92 に合わせた。名前と巻き上げの細部は点検の C-36。）

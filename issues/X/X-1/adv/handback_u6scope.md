# U6 の基の選び方を作業ツリーの回にどう当てるか、への独立の助言（39 回目、2026-10-18）

親の票は scratchpad の `x1/adv3/ticket_u6scope.md`。案は (a) U6 のまま、(b) 作業ツリーでは HEAD 自身の基、(c) 作業ツリーでは U6 の前に戻す。票の事実の誤り 2 点（テストの担当は gate を回さない、W3 の 9 件の種の出所は記録に無い）は、親が途中で訂正した。利用者の外出中に、暫定の判断の前に聞いた。

## 結論（推奨）

**(b) を採るが、分ける条件は「作業ツリーか主のツリーか」（`repo.tree_kind`）ではなく「回の形」（`Selection.narrowed`）にする**（以下 (b')）。

- 絞った回（`--work`。`--changed-since`/`--sample` あり）で `same` なら、merge base（= HEAD）自身の基（無ければ同じコードの祖先の基、今の `elif` の経路）と比べる。`before_head=False`。= M-3 の元の設計。
- 全体の回と shard（絞っていない回）で `same` なら、U6 のまま「the code before HEAD」と比べる。
- (c) は採らない。

### 根拠

1. **基は「その回が立てる問い」に従うべき**で、問いは回の形で決まり、木の種類では決まらない。
   - 絞った回の問い（M-3、`issues/X/X-1/step3_measures.md` M-3、`rules/checks.md` 4.4）: 「作業（merge base からの差分）がこの類を入れたか」。`same` とは「差分にコードが無い」ことなので、HEAD のバイナリが出す修正候補の類は定義により全て作業の外。merge base 自身の基と比べれば、必然的に全て `pre-existing` になり、これは正しい答え。
   - 全体と shard の問い（X1-3、`issues/X/X-1.md` 42〜49 行）: 「HEAD のコードがこの類を入れたか」。ここだけ「the code before HEAD」が要る。U6 はこの場面のために利用者が採った。
2. **票の (b)（木の種類で分ける）は、訂正後に最も多い場面を取り落とす。** 訂正 2 の場面（親が主のツリーでテストの担当のコード無しのパッチを写した直後の `--work`）は `tree_kind == "main"` なので、(b) でも U6 のまま「the code before HEAD」と比べる。
   すると、dev の直前のコードのコミット（親が既に判定し、網羅の検査が印を付けて FAIL にしているもの）で入った類が、新しい事例を種にして見つかると、パッチと無関係に親の `--work` を落とす。これは W3 で止めたかった「作業の差分と関係の無い前からの形で止まる」（`step1_eval.md`）の再来で、しかも最頻の経路。(b') ならこの回は `pre-existing` に並ぶ。
3. **(b') で情報は失われない。** 同じ類は、パッチをコミットした後の網羅の検査が「the code before HEAD」と比べて印付きの FAIL にする（U6、`after_commit.py` の help）。絞った回で落とすのは同じ合図の二重化で、親の仕分けの回数だけ増える。
4. **(c) は W3 の問題そのもの。** `same` で基不明にすると、前からの類を全て落とす。M-3 の目的に反し、(a)・(b) のどちらより悪い。
5. D-15（決める場所は一つ）: `narrowing.resolve_base` に `narrowed` を渡すだけで済み、`fuzz.py` の分岐は変わらない。

### 場面ごとの振る舞い（(b')）

| 場面 | 形 | 基 |
|---|---|---|
| 1. 主のツリーの網羅の検査・全体の回 | 全体/shard | the code before HEAD（U6） |
| 2. 主のツリーで、コミットした後に `--work` | 絞った回 | HEAD 自身 → 修正候補の類は全て `pre-existing`。「HEAD のコードが入れたか」を手で見たいなら `--only fuzz`（`--work` 無し = 全体の形）か網羅の検査が答える |
| 2'. 主のツリーで、コード無しのパッチを写した直後の `--work`（訂正 2） | 絞った回 | HEAD 自身 → 全て `pre-existing`。入力は主の `target/fuzz/new/` に残る |
| 3. 作業ツリーで、コードを変えない実装の作業の `--work` | 絞った回 | HEAD 自身 → 全て `pre-existing` |
| WIP があるがコードを変えない作業ツリー | 絞った回 | `same` でないので今のまま merge base の基（= 同じコード）。(b') と同じ答えになり、整合する |

場面 2 が (a) より弱くなる点は認めるが、`--work` を コミットの後に回すのは通常の流れではなく（親はコミットの前に回す）、全体の形と網羅の検査が同じ問いに答えるので、形ごとの一貫性を優先する。

### 親の案との一致と相違

- 一致: (c) を採らない。主のツリーの網羅の検査と全体の回は U6 のまま。作業がコードを変えていない絞った回では merge base 自身の基（M-3 の元の設計）に戻す。
- 相違: 分ける条件。親の (b) は木の種類、(b') は回の形。(b) を選ぶと場面 2' が U6 のままになり、親の `--work` がパッチと無関係に落ちる回が残る。(b') を選ぶと場面 2 が「全て `pre-existing`」になるが、網羅の検査と `--only fuzz` が補う。

## 手戻りの大きさと、暫定で進めてよいか

- 変更の量（(a) → (b')）: `tools/narrowing.py` の `resolve_base` に引数 `narrowed` を足し、`if same and not narrowed:` にする（約 5 行、docstring 数行）。`tools/fuzz.py` 910 行で `selection.narrowed` を渡す（1 行）。`tools/test_gate.py` の U6 の試験（1462〜1491、2962〜2966、3654 行）に絞った回の場合を 1 つ足す（約 20 行）。
  文書は `step3_measures.md` M-3 の U6 の行、`X-1.md` の U6 の記述、`narrowing.py` の冒頭（各 1〜2 行）。
- 逆方向（(b') → (a) に戻す）も同じ量。データの不可逆性は無い（基のバイナリや保存の形は変わらない）。
- 判断: **暫定で (b') に進めてよい。** (b') は利用者が既に了承した M-3 の設計を絞った回に戻すもので、新しい決定を足すというより、U6 が利用者の決めた範囲（主のツリーの網羅の検査と全体の回）を越えた分を戻す。待つ間 (a) のままだと、テストの担当のパッチを写すたびに親の `--work` が無関係な類で落ちうる。確信: 中〜高。

## (b) の危険と補う手

- 危険: 絞った回で `same` のとき、修正候補の段の類では一切落ちなくなる。ただし内部エラー・異常終了・時間切れは `fuzz.py` 807〜808 行のとおり基によらず落ちる（GF-3）ので、落ちなくなるのは修正候補の約束の違反だけ。コードを変えていない作業がそれを入れることは無いので、見逃しではなく帰属の正しさ。
- 補い:
  1. `rules/checks.md` 4.4 が既に「`pre-existing` の行を報告に並べる」ことを求めている。
  2. コミットの後の網羅の検査が同じ種（新しい事例）で「the code before HEAD」と比べ、印付きの FAIL で `auto sweep:` の行に残す（U5・U6）。
  3. 保存した入力は `work / "new"` = その木の `target/fuzz/new/`（`fuzz.py` 688・804 行）。主のツリー（場面 2'）では残るが、**作業ツリー（場面 3）の分は作業ツリーを消すと失われる**。出力には経路と `detail` と登録の雛形は出るが入力の本文は出ない。
     これは (a) でも同じで (b) 固有ではないが、親が区切りで仕分ける前に作業ツリーの `target/fuzz/new/` を主へ写す一行を親の手順（`take.py patch` に並べる、または leader 規則）に足すとよい。
  4. 任意の改良: `same` かつ絞った回では基のバイナリを回さず（同じコードなので必ず出る、数秒の無駄）、「no change of the code since the merge base」の理由で `pre-existing` に並べる形もある。基が未保存のとき（網羅の検査がまだ基を書いていない瞬間）の `base unknown` を避けられる。+10 行ほど。まずは単純な (b') で足り、`base unknown` が実際に出たら足せばよい。

## 範囲の外で気付いたこと

- `narrowing.code_changes` は `git diff HEAD` なので、`BUILT_FROM` の下の**未追跡の新しいファイル**（新しい crate のファイルなど）を「コードの変更」に数えない。追跡していない新しいコードだけの作業ツリーが `same` と判定されうる。実装の担当は通常 WIP のコミットの前に `git add` するとは限らないので、`_untracked` を足す小さな直しの余地がある（確信: 中。実験はしていない）。

## 確信

- (b') の推奨: 高。分ける条件を回の形にする点: 高（場面 2' の存在は訂正 2 と `rules/checks.md` 4 章の表で確認）。
- 手戻りの見積り: 高（該当のコードと試験を読んだ。`tools/narrowing.py` 218〜257 行、`tools/fuzz.py` 795〜822・910 行、`tools/test_gate.py` 1426〜1491・2962〜2966・3654 行）。
- 暫定で進めてよい: 中〜高。

参照: `/Users/centrevillage/projects/onsalang/tools/narrowing.py`、`/Users/centrevillage/projects/onsalang/tools/fuzz.py`、`/Users/centrevillage/projects/onsalang/tools/test_gate.py`、`/Users/centrevillage/projects/onsalang/issues/X/X-1/step3_measures.md`（M-3）、`/Users/centrevillage/projects/onsalang/issues/X/X-1.md`（42〜49 行）、`/Users/centrevillage/projects/onsalang/issues/X/X-1/effect_x3.md`（6 章 X1-3）、`/Users/centrevillage/projects/onsalang/rules/checks.md`（4 章の表、4.4）、`/Users/centrevillage/projects/onsalang/tools/gate_steps.py`（28〜45 行）。
ファイルの編集、gate・cargo の実行はしていない。
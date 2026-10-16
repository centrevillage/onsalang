## 作業 X-1/U2 の直しの報告

依頼の直しを入れました。merge-base が HEAD と同じで、コードの経路に追跡しているファイルの未コミットの変更が無いときは、`narrowing.resolve_base` が基を使わずに理由を返します。自己テストは 230 件が通っています。gate の全体は、指示どおり回し直していません。

- 状態: WIP のコミット `1e8ac56`（`WIP: X-1 U2 (no base when the merge base is HEAD with no change of the code)`）。未コミットの変更は無い。
- 作り直したパッチ: `/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/0ed8f9b9-db30-4d49-bb2b-cb3f68df27e6/scratchpad/x1/u2/u2_all.patch`
  - `take.py patch` の表示は「10 file(s), +1613 -88; without the tests and the data: +911 -85」。

### したこと（+28 −7。テストを含む）

- `tools/narrowing.py`
  - コードの経路 `BUILT_FROM`（`crates`・`tools`・`std`・`runtime`・`Cargo.*`）と、未コミットの変更を返す `code_changes(root)` を `gate_runs` から移した。git の出力は `-z` で読む形にし、空白を含む名前も扱える。
  - `resolve_base` は、`COMMIT` の確かめが通った後に判定する。merge-base が HEAD と同じで `code_changes` が空なら、`same as HEAD (<7 字>, no change of the code): nothing to tell apart` を返す。
  - fuzz の要約は `; base unknown (same as HEAD …)` になる（表示は U1 の形のまま）。
  - 絞った回では見分けをせずに全て落とす。全体の回と分割の回では、「pre-existing」の印が付かなくなる。
- `tools/gate_runs.py`: `save_base` の未コミットの確かめは `narrowing.code_changes` を使う。判断は一か所になった。
- 判定を置いた位置について:
  - `COMMIT` の確かめの後に置いたのは、基が無いときに今の理由（`no …/COMMIT`）を保つためです。U1 の `Narrowing.test_resolve_base` は変えずに通りました。
  - `--base DIR` で基を名指ししたときは、今のまま判定しない。

### 主張と証拠

- `python3 -B tools/test_gate.py` → `Ran 230 tests in 74.162s` / `OK`。
- 足した確かめは `SaveBase.test_saves_what_the_reader_finds` にある。HEAD の基を保存した直後の主のツリーで、次のとおりになる。
  - 変更が無いとき → `same as HEAD`
  - `crates/` の追跡しているファイルに変更があるとき → 基を使う
  - `docs/` だけの変更 → `same as HEAD`
  - dev の上に作業のコミットを足したとき（担当の作業ツリーと同じ形）→ 基を使う
- `python3 -B tools/gap_marks.py` → `48 SPEC-GAP mark(s) in crates, std, runtime, tools; all registered`。`tools/__pycache__` は作っていない。

### 次の担当へ（U3 の文書に足すこと）

- `--sweep` の後と主のツリーの全体の回では、fuzz の要約に `base unknown (same as HEAD …)` が出る。誤りではない。
- 前からの類の見分けが働くのは、担当の作業ツリーで、dev の上に差分があるときだけ。
# X-1/U1 設計メモ: 重い検査の入力の絞り方と、前からある誤りの見分け（道具の側）

基: 628f8ec（作業ツリーで `git log --oneline -1` を確かめた）。
読んだもの: 作業票、`step3_measures.md`、`step2_criteria.md`、advisor の第 1 段の Q2・Q4 と第 2 段の 2.1・2.4・2.6、`tools/fuzz.py`、`tools/fmt_props.py`（`inputs_of`、`sources`、`run`、`main`）、`tools/test_gate.py`（`Fuzz`、`FmtProps`、`TempRepo`、`FAKE_ONSA`、`FAKE_CASES`）、`tools/gate.py`（`lock_path`）、`tools/repo.py`、`docs/agent-rules.md`、計画 §8.2〜§8.5。

## 0. 先に判断がほしい点（実測から）

今の木（628f8ec、fuzz の種 1,422 件）で、作業票の選び方を純 Python で数えた（`P32/x1/u1/count.py`・`count2.py`。コンパイラは回していない）。

| 数えたもの | 値 |
|---|---|
| 種の直上のディレクトリ | 163 個（うち種が 1〜2 件のもの 123 個） |
| 抜き取り 0.1、塩 `X-1`、ディレクトリごとの最低 1 件なし | 156 件（11%） |
| 同、直上のディレクトリごとに最低 1 件（作業票のとおり） | **270 件（19%）** |
| 同、経路の先頭 3 段（`tests/spec/ops` など、37 個）ごとに最低 1 件 | 166 件 |
| `--changed-since 6e26c4c`（W3-13 の差分）の差分の種 | 36 件 |
| 同、コードの差分に出る診断コード | 8 個（E0002、E0006、E0010、E0011、E0013、E0020、E0200、E0412） |
| その本文を含む種（差分の種を除く） | **402 件**（上限 200 を超え、作業票のとおりだと全て使わない） |
| コードごとの種の数 | E0011 7、E0010 14、E0013 16、E0412 20、E0006 21、E0200 88、E0002 139、E0020 232 |

- **A. 最低 1 件の単位**: 直上のディレクトリは小さいものが多く、最低 1 件で抜き取りがほぼ倍（156 → 270）になる。案 (a) 作業票のまま直上（270 件、fuzz の変異体は約 2,700）、(b) 経路の先頭 3 段（166 件）。どちらも 1 行の違い。私は (b) を推す（割合の 1 割がほぼ保たれ、領域ごとの最低 1 件という目的も満たす）。指示が無ければ (a) で作る。
- **B. 診断コードの上限の当て方**: W3-13 の差分では、主に変えたコード（E0013）が 16 件しか無いのに、ありふれたコード（E0020 232 件）に引かれて全体が上限を超え、診断コードの分が丸ごと使われない。案 (a) 作業票のまま（合計が上限を超えたら全て使わない）、(b) 種の少ないコードから順に足し、合計が上限を超える手前で止める（今の例では E0011・E0010・E0013・E0412・E0006・E0200 の 6 個、和で約 160 件。E0002・E0020 は使わず、そのことを出力に書く）。(b) は約 5 行増え、止まり方は (a) と同じ（コードの数に線形、ソート 1 回）。私は (b) を推す。指示が無ければ (a) で作る。

## 1. 引数の形（U2 が使う）

fuzz と fmt_props で同じ名前・同じ意味にする（`narrowing.add_arguments(ap)` が両方に足す。判断と検証は一か所）。

| 引数 | 意味 | 既定 |
|---|---|---|
| `--changed-since REV\|auto` | 差分に関わる種と、診断コードで選ぶ種を足す。`REV` はコミット。`auto` は `git merge-base HEAD dev`（基のバイナリの解決と同じ関数） | 無し |
| `--code-cap N` | 診断コードで選ぶ種の上限。`--changed-since` と一緒のときだけ意味を持つ（単独は使い方の誤り） | 200（`narrowing.CODE_CAP`。U2 は `gate_steps.py` に別の定数を置かずこれを読むか、明示で渡す） |
| `--sample F` | 抜き取りの割合（0 < F ≤ 1） | 無し |
| `--salt ID` | 抜き取りの塩（作業 ID）。`--sample` には必須、`--sample` 無しでは使い方の誤り | 無し |
| `--shard I/K` | 種を `sha256(経路) % K == I` で分けた一つ（0 ≤ I < K）。上の 4 つとは同時に使えない（使い方の誤り、終了 2） | 無し |
| `--base auto\|none\|DIR` | fuzz だけ。前からある誤りを見分ける基のバイナリ。`auto` は §4 の解決、`DIR` は `onsa` と `onsa_cases` のあるディレクトリ、`none` は見分けない | `auto` |

- 回の種類:
  - **全体の回**: 選び方の引数が一つも無い（今と同じ。U2 までは gate はこれで動く）。
  - **絞った回**: `--changed-since` か `--sample` がある。fmt_props は `tests/spec/fmt/` の全てを常に入れる。前からの類は落とさない（§3）。
  - **分割の回**: `--shard`。全体の一部で、前からの類も落とす。常に入れるディレクトリも使わない（K 個の和を全体にするため）。
- U2 の作業の検査の呼び方の例: `tools/fuzz.py --changed-since auto --sample 0.1 --salt W4-01`（`--code-cap` は既定）。網羅の検査: `tools/fuzz.py --shard 0/2`。fmt_props も同じ（`--base` を除く）。
- `--changed-since` で git が読めない（git の木でない、コミットが無い、`auto` で merge-base が無い）ときは、終了 2（回せない。全体に倒さない。gate は `CANNOT_RUN` として落とす）。

## 2. モジュールの関数の形（`tools/narrowing.py`、新規）

```python
DEV = "dev"            # 基の枝
CODE_CAP = 200
SHORT = 7              # target/base/<SHA の先頭 7 字>

class NarrowError(Exception)                      # git が読めない、など（main が終了 2 にする）

@dataclass(frozen=True)
class Selection:       # 引数から作る。None は全体の回
    changed_since: str | None   # 解決済みのコミット
    code_cap: int
    sample: float | None
    salt: str | None
    shard: tuple[int, int] | None
    @property narrowed -> bool  # changed_since か sample がある（前からの類を落とさない回）

def add_arguments(ap, base=False)                 # 上の表の引数を足す（base=True で --base も）
def selection(ap, args, root) -> Selection | None # 検証（ap.error）と `auto` の解決
def merge_base(root) -> str                       # git merge-base HEAD dev（無ければ NarrowError）
def changed_paths(root, since) -> set[str]        # git diff --name-only -z --no-renames since
                                                  #   ∪ git ls-files --others --exclude-standard -z
def diff_codes(root, since) -> set[str]           # git diff --unified=0 since -- . :(exclude)tests :(exclude)docs
                                                  #   の +/- 行（+++ / --- を除く）の repo.CODE、
                                                  #   と未追跡のファイル（tests/ docs/ の外）の本文の repo.CODE

@dataclass(frozen=True)
class Picked:
    paths: frozenset[str]
    counts: dict       # {"diff": a, "codes": b, "always": c, "sample": d}（重なりは前の分に数える）
    note: str          # 「codes 0 (402 over the cap 200: left to the sample)」など。無ければ ""

def pick(seeds, sel, root, always=()) -> Picked   # seeds: [(経路, 本文)]（呼ぶ側の全体の種の一覧）
def in_shard(path, shard) -> bool                 # sha256(経路) % K == I
def sampled(paths, fraction, salt) -> set[str]    # 下の抜き取り

@dataclass(frozen=True)
class Base:
    commit: str        # 表示に使う（COMMIT の中身か、DIR の名前）
    onsa: Path
    onsa_cases: Path

def resolve_base(root, spec) -> Base | str | None # Base、解決できない理由（str、「基は不明」）、none は None
```

- `pick` の中身:
  - 差分の種 D = 種の経路 ∩ `changed_paths`。
  - 診断コードの種 C = 本文に `diff_codes` のどれかを含む種 − D。|C| が上限を超えたら C = ∅ とし、`note` に書く（0. の B で (b) なら、少ないコードから足す）。
  - 常に入れる A = 経路が `always` のどれかの下にある種 − D − C。
  - 抜き取り S = `sampled(全ての種の経路, F, 塩)` − D − C − A。`sampled` は差分に依らない（同じ塩・同じ種の一覧なら同じ集合）:
    `h(p) = int(sha256(塩 + "|" + p) の先頭 16 桁の 16 進) / 2^64`、`h(p) < F` の種、それに加えて、それで 1 件も選ばれないディレクトリ（0. の A）から `h` が最小の 1 件。
  - 分割の回は `in_shard` で絞るだけ（D・C・A・S は使わない）。
- 道具の側の使い方: fuzz は `seeds(root)` の全体、fmt_props は `sources(...)` の全体を `pick` に渡し、返った経路の集合で絞る。経路の比べ方は根からの `/` 区切り（`git ... -z` で引用符の付け方に左右されない）。

## 3. 部分集合を保つ仕組み（fuzz、fmt_props）

**全体から出すもの**（今のまま）: `seeds(root)` の一覧、変異の `corpus` と `tokens`（`mutants`）、切り詰めの記号の数え `counts`（`truncations` の `cut_sites` は全ての種で回す）、保存した入力の再生、実装待ちの一覧と許可の一覧の照合。

**絞るもの**: 変異・切り詰め・掃引を作る種だけ。

- `mutants(seed_files, per_seed, version, deep, only=None)`: `corpus`・`tokens` は `seed_files` の全体から出し、`only` に無い種は乱数を作らずに飛ばす。各種の乱数は `seeded_random(version, path, text)` で種ごとに独立なので、残った種の変異体は全体の回と一文字も違わない（advisor の実験の順。種の一覧を先に絞ると 918/2,720 しか一致しない）。
- `truncations(..., only=None)`、`sweep(..., only=None)`: 同じ。切り詰めの乱数も種ごと（`"truncation", path, text`）、重みの数えは全体。掃引は乱数を使わない（同じ切り口の重複を除く `setdefault` は、全体の回で先の種の名前になることがあるが、本文の集合は部分になる）。
- **修正候補の段**: 今の `chosen = [i for i in range(len(inputs)) if i % FIX_EVERY == 0]`（回の中の番号）を、全体の回での番号 `seed_index[path] * per_seed + k`（`seed_index` は全体の `seed_files` の中の位置、`k` は変異体の番号。どちらも `mutants` の組にある）で選ぶ形に変える。全体の回では回の中の番号と同じ値なので、全体の回の選び方は変わらない。
- 確かめやすくするため、`run` から「回す入力を決める」部分を `plan(seed_files, only, per_seed, version, deep, truncated, swept)`（変異体、切り詰め、掃引、修正候補の段に回す変異体を返す）に切り出す。自己テストは `plan(全体) ⊇ plan(絞った)` を本文の多重集合で比べる。
- 新しい類の最小化の元は、回の中で最初にその類を出した入力なので、絞った回と全体の回で最小化の結果が違うことはある（入力の集合の部分の性質とは別。判定は類で行うので影響しない）。
- fmt_props: `inputs_of` の乱数は `seeded_random(version, path, text, kind, k)` で源ごとに独立、`load_symbols` は源に依らない。なので `sources(...)` の全体を作った後で源を絞るだけで部分集合になる（`only` を `run` に渡し、`files` を絞る）。自己テストで `inputs_of` が他の源に依らないこと（源を足しても既にある源の入力が変わらない）を確かめる。
- `--time-budget` の既定（fuzz 600 秒、fmt_props 300 秒）は変えない。

## 4. 見分けの仕組み（fuzz だけ、M-3）

- **何を基で回すか**: 新しい類（`known` にも許可の一覧にも無いもの）のうち、**修正候補の約束の違反の類**（`fix|…`）の、最小化した入力だけを、基の `onsa_cases --fix-same-place` で回す（今の `FixRunner` を基の argv で作る。1 類につき 1 回、時間は `min(TIMEOUT, 残りの予算)`。予算が尽きていれば回さず「基は回せない」）。
- **何を比べて「同じ類」とするか**: 基の違反のどれかが、今の木の違反と同じ `signature`（`fix|<code>|<候補の題>|<残ったコード>`）で、かつ同じ `left`（残った診断の文面、数字 `#`・引用 `…` にした形）を持つこと。最小化は `left` を保って行っている（今の `minimize(..., left=c.left)`）。
- **内部エラー・異常終了・時間切れ・その他の終了コード**: 基では回さず、前からでも落とす（GF-3、leader-rules 4.5）。回さない理由: 結果に依らず落とすので情報が要らないことと、異常終了の入力を基でも回すとクラッシュの報告をもう一つ作る（agent-rules 3 章）こと。
- **判定**:
  - 絞った回: 前からの類は `failures` に入れず、`pre-existing (the base 628f8ec shows it): fix-same-place: <類> (seed …, mutant k)` の行で並べる。最小化した入力は今のとおり `target/fuzz/new/` に書き、足す項目の雛形も出す（親が区切りで登録する）。基で出なければ今のとおり落とす。
  - 全体の回・分割の回: 落とす行の末尾に ` (pre-existing: the base 628f8ec shows it)` を付けるだけ。
  - 基が不明・`none`・基の道具が失敗した（`RuntimeError`）: 全て今のとおり落とす。基が不明のときは要約に理由を出す。
- **基の解決**（`resolve_base(root, "auto")`）:
  - 主のツリー = `git rev-parse --path-format=absolute --git-common-dir` の親（`gate.py` の `lock_path` と同じ手。作業ツリーでも主のツリーでも主の `.git` を指す）。
  - 基のコミット = `git merge-base HEAD dev`。無い（`dev` が無い、共通の祖先が無い、git の木でない）→「基は不明: <理由>」。
  - ディレクトリ = `<主のツリー>/target/base/<SHA の先頭 7 字>/`。**短い SHA の長さは 7 字に固定し、`git rev-parse --short` は使わない**（自動の長さは物の数で 8 字以上に伸び、写す側（U2）と読む側で食い違いうる。`core.abbrev` は今は未設定）。先頭 7 字の取り違えに備え、ディレクトリの `COMMIT` の中身（前後の空白を除く、7 字以上）が基の完全な SHA の先頭と一致することを確かめる（今の `628f8ec/COMMIT` は `628f8ec` で一致する。U2 には完全な SHA を書くことを勧める）。
  - `onsa` と `onsa_cases` が実行できる通常のファイルであること。どれかが欠ければ「基は不明: <経路> が無い」。
  - `DIR` を渡したときは、上の 2 つのファイルだけを確かめ、表示の名前は `COMMIT` の中身か、無ければディレクトリの名前。
- 費用: 新しい修正候補の類 1 つにつき `onsa_cases` 1 回（数十ミリ秒〜数秒）。git の呼び出しが 2〜3 回。

## 5. 出力（行の中の数は形を示す例で、測った値ではない）

- 要約の行（今の `fuzz: …` の行）に足す:
  - 絞った回: `from 143 of 1422 seeds (diff 36, codes 0, sample 107; codes over the cap: 402 > 200, left to the sample)`。分割の回: `from 711 of 1422 seeds (shard 0/2)`。全体の回は今のまま。
  - 見分け: `; base 628f8ec: 1 pre-existing` / `; base unknown (no merge base of HEAD and dev)` / `; base none`。
- fmt_props の要約の行: `from 210 sources (picked 230 of 1100: diff 5, codes 40, always 50, sample 135)` の形。分割の回も fuzz と同じ。
- 0 件の扱い: 絞った回で種が 0 件でも、fuzz は保存した入力の再生があるので回の意味はある（要約に 0 と出る）。fmt_props は今の「no source ran」で落ちる（`tests/spec/fmt` を常に入れるので実際の木では起きない）。

## 6. 処理の費用と停止

- `pick`: 種の数 N、本文の総量 B、差分の量 Δ として O(N + B + Δ)。ハッシュは種ごとに 1 回、本文は正規表現で 1 回なめる、差分は git が出す行を 1 回なめる。0. の B の (b) を採るとコードの数 c で O(c log c) が足される。
- git の呼び出し: `git diff`（Δ に比例）、`git ls-files --others`（木のファイルの数に比例）、`git merge-base`、`git rev-parse`。各 `subprocess.run(..., timeout=60)` で包み、切れたら `NarrowError`（終了 2）。
- 変異体の生成は今より少ない（選んだ種だけ）。`cut_sites` は今のまま全ての種で回る（今の木で 1 秒未満、advisor の測定で生成 0.4 秒）。
- 繰り返しは有限の一覧の上だけで、止まる。

## 7. 自己テスト（`tools/test_gate.py`）

- 新しい組 `Narrowing`: 作り物の git の木（`git init`、コミット、枝 `dev`）で
  - `changed_paths` が変えた・足した・未追跡のファイルを返す（非 ASCII の名前を含む）。`diff_codes` が `tests/`・`docs/` の行を拾わず、未追跡のファイルの本文を拾う。
  - `pick`: 同じ塩で同じ集合、塩が違えば違う集合、ディレクトリごとに最低 1 件、上限を超えたら診断コードの分を使わず `note` に書く、`always` が入る。
  - `in_shard`: K 個の和が全体で、互いに素。
  - `resolve_base`: 見つかる、`COMMIT` が食い違うと不明、ファイルが欠けると不明、`dev` が無いと不明、git の木でないと不明。
  - 引数の検証（`--salt` 無しの `--sample`、`--shard` と他の同時、範囲の外の値、`--code-cap` 単独）が終了 2。
- `Fuzz` に足す: `plan(全体) ⊇ plan(絞った)`（変異体、切り詰め、掃引、修正候補の段）、全体の回での修正候補の段の番号、未追跡の種が入る（`run` を通す）、見分けの 5 つ（前から → 落とさない、基で出ない → 落とす、内部エラーは前からでも落とす、基が不明 → 落とす、全体の回は前からでも落とすが印が付く）。偽の基は今の `FAKE_CASES`（同じ類を出す）と、違反を出さない偽を使う。
- `FmtProps` に足す: 絞った回が `tests/spec/fmt` を含み、選んだ源だけを回す。`inputs_of` が他の源に依らない。
- 異常終了するプロセスを作らない: 偽のバイナリは終了コードと、今の `FAKE_ONSA` の SIGKILL だけを使う（新しい形は足さない）。

## 8. 行の見積もり（テストを除く）

| 置き場所 | 内容 | 行 |
|---|---|---|
| `tools/narrowing.py`（新規） | 説明 25、引数と検証 30、git の 3 関数 30、`pick`・`sampled`・`in_shard` 30、`resolve_base` 30 | 120〜150 |
| `tools/fuzz.py` | `only` の 3 か所 10、`plan` の切り出しと修正候補の段の番号 20、見分け 25、要約 10、`main` 10、説明 15 | 80〜100 |
| `tools/fmt_props.py` | `run` の `only` と要約 10、`main` 10、説明 5 | 20〜30 |
| 合計 | | 220〜280 |
| 自己テスト | | 150〜200 |

計画 §8.5 の単位の目安（300 行）の内。作業票の U1 の見込み（150〜230 行）より少し多いのは、基の解決と引数の検証をモジュールに置いたため（U2 が同じものを書かずに済む）。

## 9. 決めていないこと・U2 へ

- 0. の A・B（指示を待つ。無ければ作業票のとおり）。
- `COMMIT` に完全な SHA を書くか（読む側は 7 字以上の先頭一致で両方を受ける）。
- `CODE_CAP` の置き場所: `narrowing.CODE_CAP` を U2 の `gate_steps.py` が読むか、`gate_steps.py` に置いて明示で渡すか（一か所に置くことだけ守れば、どちらでもよい）。抜き取りの割合 0.1 は U2 の `gate_steps.py` に置く（道具には既定を置かない）。
- gate が要約から前からの類を拾うなら、行の頭は `pre-existing ` で固定する。

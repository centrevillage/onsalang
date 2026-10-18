# X-9 の候補の整理（40 回目、2026-10-18）

基本方針（利用者）: 小さな道具の集まりにせず、docs.py のように作業の種類ごとに一つの道具にする。

## 道具の種類（名前は仮）
- 文書: docs.py（既存）
- 担当の作業: work.py（新。take.py と handback.py の save を入れる）
- 前後の比べ: compare.py（新。speed.py・moved_only.py を入れる）
- ファズと性質: fuzz.py・fmt_props.py（既存）
- 検査: gate.sh（既存。項目の小さな検査の道具は gate の下のまま）
- 記録の分析: logs.py（新。handback.py の usage を入れる）
- テストの器: onsa_cases（Rust。道具でなく器）

## 0. 済みで閉じる案
- X9-1 決定の記録の置換スクリプト: docs.py set・note・changes で済み（38 回目の計測で 36 個 → 0 個）
- X9-2 表の列の数: docs.py check の tables で済み
- X9-3 文書の整形 (10): docs.py fmt で済み
- X9-4 docs-due: U1 2a1155f で済み
- X9-5 担当の定義の文の案 3 件: 39 回目に済み

## 1. 横断（道具の作り方の枠）
- X9-6 道具の形の指針: 種類ごとに一つの道具、COMMANDS に下位の命令、共通は repo.py、自己テストは test_gate.py。既存は動かすものだけ合わせる。指針の置き場所
- X9-7 役割ごとの help: `<道具> help --role <役割>`。役割と命令の対応は道具の中の一か所。help の言葉
- X9-8 時機と道具の一覧: 規則と定義の、道具の使い方の約 45 行を棚卸し。規則には時機と道具だけ。注意を害の無い形に変える所も同じ回
- X9-9 食い違いの歯止め: 規則と定義に書いた `<道具> <命令> --<引数>` を gate で照らす
- X9-10 フック: SubagentStart・SessionStart で役割の help を足す。PreToolUse で道具を通さない操作を止める（作業ツリーへの cd = (7) の材料 1）

## 2. 文書（docs.py）
- X9-11 文書の編集の命令: 一意の置き換え・スワップの確かめ・fmt・check を一つに。代わりに Edit を残して PreToolUse でスワップを見る形も
- X9-12 既決の照らし: 新しい S を出す前に、同じ節・族の既決と R を並べる（(7) の材料 2、leader 5.6）

## 3. 担当の作業（work.py）
- X9-13 作る: dev から作業ツリーと枝、空の WIP コミット、基の控え（leader 2.4 の日付付きの注意を道具へ）
- X9-14 始めの確かめ: 担当が始めに回す（common 2.1）
- X9-15 写す: take.py の patch・check・apply を移す
- X9-16 片付け: 写ったか・報告を保存したか（leader 3.6）、ファズの入力を写す（壊す側も）、作業ツリーと枝を消す
- X9-17 コミット: 文書とコードを分ける（4.6）、題（4.7）、Docs-Checked（4.10）。post-commit フックの上

## 4. 前後の比べ（compare.py）
- X9-18 診断の比べ: dump_diags.py・cmp2.py（check --json で候補の編集まで）
- X9-19 時間の比べ: speed.py を移し、順を交互に（measure.py・timeit.py）
- X9-20 行数: take.py の test_lines を担当も回せる命令に（count_lines.py の穴は take.py に無い）
- X9-21 分割の確かめ: moved_only.py を移す
- X9-22 字句の突き合わせ（oracle.py・oracle2.py）と道具の出力の比べ（snap.py）: 要るか
- 壊す側の道具のパスの直書きは、バイナリと根を引数で受けることで解ける

## 5. ファズと性質
- X9-23 入力の仕分け: fuzz.py sort（39 回目の形）。手で保存する仕方も help に
- X9-24 許可の一覧の雛形: 新しい類に [[allowed]] の雛形
- X9-25 変異の掃引: alpha_sweep と contract3.py・mut3.py を一つに。器の関数を使うので onsa_cases の側。網羅の検査か段の終わり
- X9-26 fmt の性質の集計を fmt_props.py --verbose に

## 6. 検査（gate）
- X9-27 golden の一覧に写し（.fixK、foreign-forms の fixed）の差
- X9-28 fix-contract の項目を違反の種類で分ける
- X9-29 DROPPED の S を指す SPEC-GAP の印（gap_marks.py）
- X9-30 道具の自己検査: seeds.py を gate-selftest に、mut.py を道具を作るときの確かめに
- X9-31 新しい配置の作り物の木（NEW_LAYOUT）: 移行が済んだので取り下げる案

## 7. 記録の分析（logs.py）
- X9-32 記録を数える道具を一つに: handback.py usage、ctx_breakdown.py、X-1 の gate_runs.py・files_runs.py・cache_miss.py、doc_usage.py・usage38.py。X-10 の (6) と重なる

## 8. テストの器（onsa_cases）
- X9-33 一つのファイルを受ける（今は run_cases.py が写して回す）
- X9-34 正規形でない正例を書く器の形
- X9-35 //~ で note の位置
- X9-36 //~ TESTFAIL に panic の文面
- X9-37 印のある事例の正規形（[test] canonical = true で fmt --check）
- X-9 で扱うか、別の項目へ回すか

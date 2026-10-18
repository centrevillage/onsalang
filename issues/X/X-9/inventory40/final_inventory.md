# X-9 規則を道具に移す最終の案（40 回目、親 PI-1〜46 と advisor V-1〜53 の突き合わせ）

材料: 親 x9/parent_inventory.md、advisor x9/adv/handback_inventory.md（段 1 の控え x9/adv/stage1_frozen.txt）。
番号は X9 の続き（X9-38 から）。既存の X9 の項目は中身を改めた所だけ書く。[ ] は出所。

## 道具の形（利用者の基本方針に合わせる）
- 設定 `.claude/settings.json`（利用者が入れる）: permissions と env とフックの登録だけ。
- フックの道具 `tools/hooks/claude_hook.py`（新、一つ）: 事象と役割（agent_type）で分け、判定は種類ごとの道具の関数を呼ぶ（判断を一か所に）。
- git のフック `tools/hooks/`（post-commit の横に pre-commit・commit-msg）。
- 担当の作業 `work.py`（新、take.py を入れる）、文書 `docs.py`、検査 `gate.sh`・`fuzz.py`、記録 `logs.py`（新、handback.py を入れる）。

## 1. 設定
- X9-38 `git stash` を deny [PI-1・V-4]
- X9-39 `swift test` を deny [PI-2]
- X9-40 `PYTHONDONTWRITEBYTECODE=1` [PI-3・V-6]
- X9-41 定義・設定・CLAUDE.md の編集を deny か ask [PI-4・V-34]。両方の案の `.claude/**` は作業ツリーにも当たるので狭める

## 2. Claude Code のフック（claude_hook.py）
止める（PreToolUse）:
- X9-42 親の作業ツリーへの cd [PI-5・V-3]
- X9-43 Agent の model [PI-6・V-17]
- X9-44 スワップのある文書の編集 [PI-7・V-31]
- X9-45 担当の主のツリーへの書き込み・commit・push、役割ごとの書ける場所 [PI-10・V-1・V-2・V-11・V-38・V-48]
- X9-46 t の crates/ の読みと .fixK の書き [PI-8・V-36]
- X9-47 役割ごとに回さない命令（例外は親が許す命令のファイル）[PI-9・V-43]
- X9-48 pending.toml と #[ignore] の手の編集 [PI-11・V-46]
- X9-49 引用符の無いヒアドキュメント [PI-12・V-5]
- X9-50 fuzz.py --deep [PI-44・V-45]
- X9-51 pgrep・sleep の自前の待ち [V-7]（低）
直す（PreToolUse の updatedInput）:
- X9-52 gate と bg.py wait の timeout を 600000 に [PI-46・V-44]
後で（PostToolUse）:
- X9-53 文書の編集の後に fmt と check（頭の欄を Edit で変えたら知らせる）[PI-13・V-47]
- X9-54 SendMessage の本文を scratchpad に控える [PI-14]
- X9-55 新しい onsa のクラッシュの報告（.ips）を知らせる [PI-21]
始め（SessionStart・SubagentStart）:
- X9-56 状態の要約（compact の後も）[PI-15・V-14]
- X9-57 役割の「時機と道具」の表と日付付きの注意。docs には check の結果 [PI-16・V-52・V-51]
終わり（SubagentStop）:
- X9-58 WIP のコミットの確かめ（一度だけ止める）、t の pending.toml の差 [PI-18・V-12・V-37]
- X9-59 報告の自動保存 [PI-17・V-20]
- X9-60 報告の形の欠けを知らせる [PI-19・V-13]
- X9-61 文脈の大きさと引き継ぎの目安を知らせる [PI-20・V-19]

## 3. git のフック
- X9-62 pre-commit: 文書とコードを分ける、`--only static`（約 9 秒）[V-26・V-32・PI-31・PI-32]
- X9-63 commit-msg: W の題なら status=DONE、題の形は警告だけ [V-27・V-28・PI-33]

## 4. 担当の作業（work.py。X9-13〜17 を改める）
- X9-13 WorktreeCreate から work.py new（dev から、基を控える）[V-9・PI-22]
- X9-14 sync（WIP と merge dev）[PI-23]
- X9-15 take = patch・check・apply。控えた基、pending.toml の作り直し、builtin_names と pending の増分、〔危険〕の経路、見積もりとの比 [PI-24・25・27・29・30・V-22・23・39]
- X9-16 done: 写ったか・報告・ファズの入力（壊す側も）→ 作業ツリーと枝を消す [PI-26・V-10]
- X9-17 commit の組み立て（status=DONE、Docs-Checked）。拒むのは X9-62・63 [V-27・V-29]
- X9-64 close（区切りの確かめ）[V-16]

## 5. 文書（docs.py）
- X9-11 改め: Edit を残しフックで囲む（X9-44・X9-53）。シェルでの文書の編集の扱いが残る
- X9-12 改め: `new S --section` で同じ節・族の既決を出し、族の S を知らせる [V-30・PI-36・PI-39]
- X9-65 blind: 推奨を伏せた版と、推奨の漏れの確かめ [PI-34]
- X9-66 answers: 回答の行を集める [PI-35]
- X9-67 ticket: 決定の数、ぶつかる事例、ID の確かめ、引き継ぎの雛形 [V-18・V-33・V-35・V-21・PI-38]
- X9-68 check: 族の S を指すか、日本語と ID の空白、規則の経緯の語（info）[PI-37・PI-40・PI-41・V-8]
- X9-69 点検の担当の字の出所の一覧 [PI-42]（advisor は道具にできないと見る）

## 6. 検査とファズ
- X9-70 test の段を --no-fail-fast [PI-43・V-24]
- X9-71 段の終わりの R の再現の入力 [PI-45・V-42]
- X9-72 自動の cargo clean [V-41]（低）
- X9-9 tool-refs [V-53]、X9-23・24 fuzz sort と --as [V-25]

## 7. 記録（logs.py）
- X9-32 に親の文脈も [V-15]。X9-61 が使う

## 8. 定義（利用者が直す）
- X9-73 〔メモ〕の票の定義（Edit を持たない）[V-50]

## 文書で確かめたこと（claude-code-guide、code.claude.com/docs の hooks・sub-agents・permissions・worktrees・env-vars）
- フックの入力に agent_id・agent_type（定義の name）。主のセッションには無い → 役割ごとの判定ができる
- WorktreeCreate は既定の git の作り方を置き換え、経路を stdout に出す。担当が終わってもフックが作った作業ツリーは残り、WorktreeRemove は走らない（自分で消す）→ 空の WIP は要らない、work.py done が消す
- SubagentStop は止められる（block の reason が担当の次の指示になる）。入力に stop_hook_active・agent_transcript_path・last_assistant_message
- PreToolUse: permissionDecision（allow・deny・ask・defer）、updatedInput は入力の全体を置き換える、additionalContext あり
- SessionStart の matcher に compact。additionalContext などは 1 万字まで
- SubagentStart は止められないが、担当の文脈に足せる
- 定義の frontmatter に hooks と disallowedTools
- 権限の経路: Write(...) の規則は見られない（Edit(...) で書く）。/path は設定の元（主の作業ディレクトリ）から、作業ツリーのセッションではその作業ツリーから
- 共通の入力に scratchpad_dir（v2.1.257 から）
- 未確認（実験で確かめる）: 担当のフックの cwd が作業ツリーか、settings の env が Bash と担当に届くか、`Edit(.claude/**)` が .claude/worktrees の下に当たるか

## 割れた点
1. コミット: 拒むのは git のフック、組み立ては work.py（advisor の形を採る）
2. 報告の保存: フックで自動（両方の洗い出しで一致。candidates の work.py は改める）
3. 空の WIP: WorktreeCreate で作った作業ツリーが残るなら要らない（確かめてから）
4. 文書の編集: Edit とフック（両方一致）。シェルでの編集をどうするか
5. 差分の印（PI-28 の .ok() など）: advisor は偽の陽性が多いと見る → 取り下げを推す
6. 字の出所（X9-69）: 割れた → 後回し

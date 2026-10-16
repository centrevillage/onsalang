### 3.1 スパンと診断（`onsa_diag`）

```rust
pub struct FileId(u32);
pub struct Span { pub file: FileId, pub start: u32, pub end: u32 }   // バイトオフセット、半開
pub struct Diagnostic {
    pub stage: Stage,               // 出した段（作る所が渡す。登録簿の「出しうる段」の一つ、W3-02）
    pub code: Code,                 // D-04 の登録簿
    pub message: String,            // 英語。登録簿のテンプレートに名前を埋めたもの
    pub span: Span,
    pub found: Option<String>,      // 問題の箇所のソース
    pub fixes: Vec<Fix>,            // Fix { title: 1 行・60 文字以内, edits: Vec<Edit> }、Edit { span: Span, replace: String }
    pub notes: Vec<Note>,           // Note { span: Option<Span>, message }（位置の無い note は規則を示す、S-114）
}
```

JSON は §18.1 の形そのもの（`span` は `file` / `line` / `col` / `end_line` / `end_col` に展開し、`end_line` は常に出す。列は文字で数える）。挿入は空の範囲の置き換えで表し、`insert_before` / `insert_after` は持たない（レビュー R-87、S-81）。修正候補の範囲は CST のトークンの範囲から作る（R-86）。

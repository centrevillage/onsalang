//! Source files and line/column lookup.

/// Index of a file in a [`SourceMap`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileId(pub u32);

/// 1-based line and column. The column counts Unicode scalar values from the
/// start of the line (LSP conversion to UTF-16 happens in `onsa_lsp`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

/// Byte offsets of line starts, for offset -> line/col conversion (D-02).
#[derive(Debug, Clone)]
pub struct LineIndex {
    line_starts: Vec<u32>,
    len: u32,
}

impl LineIndex {
    pub fn new(text: &str) -> LineIndex {
        let mut line_starts = vec![0];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i as u32 + 1);
            }
        }
        LineIndex { line_starts, len: text.len() as u32 }
    }

    /// 1-based line containing `offset`.
    pub fn line(&self, offset: u32) -> u32 {
        let offset = offset.min(self.len);
        match self.line_starts.binary_search(&offset) {
            Ok(i) => i as u32 + 1,
            Err(i) => i as u32,
        }
    }

    /// Byte offset of the start of a 1-based line.
    pub fn line_start(&self, line: u32) -> u32 {
        self.line_starts[(line - 1) as usize]
    }

    /// Byte offset of the end of a 1-based line (excluding the newline).
    pub fn line_end(&self, line: u32) -> u32 {
        match self.line_starts.get(line as usize) {
            Some(&next) => next - 1,
            None => self.len,
        }
    }

    pub fn line_count(&self) -> u32 {
        self.line_starts.len() as u32
    }
}

/// One source file with its line index.
#[derive(Debug, Clone)]
pub struct SourceFile {
    name: String,
    text: String,
    index: LineIndex,
}

impl SourceFile {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn line_col(&self, offset: u32) -> LineCol {
        let line = self.index.line(offset);
        let start = self.index.line_start(line) as usize;
        let offset = (offset as usize).min(self.text.len());
        let col = self.text[start..offset].chars().count() as u32 + 1;
        LineCol { line, col }
    }

    pub fn line_end(&self, line: u32) -> u32 {
        self.index.line_end(line)
    }

    /// Text of a 1-based line without its newline.
    pub fn line_text(&self, line: u32) -> Option<&str> {
        if line == 0 || line > self.index.line_count() {
            return None;
        }
        let start = self.index.line_start(line) as usize;
        let end = self.index.line_end(line) as usize;
        Some(self.text[start..end].trim_end_matches('\r'))
    }
}

/// All source files of one compilation.
#[derive(Debug, Default, Clone)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    pub fn add(&mut self, name: impl Into<String>, text: impl Into<String>) -> FileId {
        let text = text.into();
        let index = LineIndex::new(&text);
        self.files.push(SourceFile { name: name.into(), text, index });
        FileId(self.files.len() as u32 - 1)
    }

    pub fn file(&self, id: FileId) -> &SourceFile {
        &self.files[id.0 as usize]
    }

    pub fn files(&self) -> impl Iterator<Item = (FileId, &SourceFile)> {
        self.files.iter().enumerate().map(|(i, f)| (FileId(i as u32), f))
    }

    pub fn len(&self) -> usize {
        self.files.len()
    }

    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_col_basic() {
        let mut m = SourceMap::default();
        let f = m.add("a.onsa", "ab\ncd\n\nxyz");
        let file = m.file(f);
        assert_eq!(file.line_col(0), LineCol { line: 1, col: 1 });
        assert_eq!(file.line_col(2), LineCol { line: 1, col: 3 });
        assert_eq!(file.line_col(3), LineCol { line: 2, col: 1 });
        assert_eq!(file.line_col(6), LineCol { line: 3, col: 1 });
        assert_eq!(file.line_col(9), LineCol { line: 4, col: 3 });
        assert_eq!(file.line_text(2), Some("cd"));
        assert_eq!(file.line_text(3), Some(""));
        assert_eq!(file.line_text(5), None);
    }

    #[test]
    fn line_col_counts_chars_not_bytes() {
        let mut m = SourceMap::default();
        let f = m.add("a.onsa", "let 音 = 1");
        let file = m.file(f);
        let eq = file.text().find('=').unwrap() as u32;
        assert_eq!(file.line_col(eq), LineCol { line: 1, col: 7 });
    }
}

//! Source files and line/column lookup.

use std::sync::Arc;

/// Index of a file in a [`SourceMap`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileId(pub u32);

impl FileId {
    /// Whether this is one of the [`SharedFiles`], the files of the embedded
    /// std, whatever their names say: a user's package may have a `std/`.
    pub fn is_shared(self) -> bool {
        self.0 >= SHARED_BASE
    }
}

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
    /// Its index in the [`SourceMap`] (for the position of an internal error).
    id: FileId,
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

    /// The 1-based line and column of a byte offset, the column counted in
    /// characters (Unicode scalar values, spec §18.1). The one place that
    /// turns offsets into lines and columns; the LSP server (M7) adds its
    /// units (UTF-16) here as an argument, from the offset and not from the
    /// column in characters. An offset inside a character is a bug of the
    /// stage that made the span (an internal error).
    pub fn line_col(&self, offset: u32) -> LineCol {
        let line = self.index.line(offset);
        let start = self.index.line_start(line) as usize;
        let offset = (offset as usize).min(self.text.len());
        if !self.text.is_char_boundary(offset) {
            // The position is the start of the line (a boundary), so that the
            // error itself can be shown with its file and line.
            crate::internal::bug(
                Some(crate::Span::empty(self.id, start as u32)),
                format!("a span from a stage has the offset {offset} on line {line}, inside a character"),
            );
        }
        let col = self.text[start..offset].chars().count() as u32 + 1;
        LineCol { line, col }
    }

    /// The byte offset of the start of a 1-based line.
    pub fn line_start(&self, line: u32) -> u32 {
        self.index.line_start(line)
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

/// The first id of the files the source maps of a process share
/// ([`SharedFiles`]); the ids of a map's own files are below it.
pub const SHARED_BASE: u32 = 1 << 31;

/// Files read once in a process that every [`SourceMap`] attaching them
/// holds at the same ids (the embedded std, X-20 E (i)): what was parsed
/// with those ids is valid in each map.
#[derive(Debug, Clone)]
pub struct SharedFiles(Arc<[SourceFile]>);

impl SharedFiles {
    pub fn new(files: impl IntoIterator<Item = (String, String)>) -> SharedFiles {
        let file = |(i, (name, text)): (usize, (String, String))| {
            let index = LineIndex::new(&text);
            SourceFile { id: FileId(SHARED_BASE + i as u32), name, text, index }
        };
        SharedFiles(files.into_iter().enumerate().map(file).collect())
    }

    /// The files with their ids (the one place of the ids).
    pub fn files(&self) -> impl Iterator<Item = (FileId, &SourceFile)> {
        self.0.iter().map(|f| (f.id, f))
    }
}

/// All source files of one compilation: its own files, and the shared ones
/// it attached ([`SourceMap::share`]).
#[derive(Debug, Default, Clone)]
pub struct SourceMap {
    files: Vec<SourceFile>,
    shared: Option<SharedFiles>,
}

impl SourceMap {
    pub fn add(&mut self, name: impl Into<String>, text: impl Into<String>) -> FileId {
        let id = FileId(self.files.len() as u32);
        if id.0 >= SHARED_BASE {
            crate::internal::bug(None, "the own files of a source map reach the ids of the shared files");
        }
        let text = text.into();
        let index = LineIndex::new(&text);
        self.files.push(SourceFile { id, name: name.into(), text, index });
        id
    }

    /// Attach `shared`: attaching the same files again changes nothing,
    /// other files are a bug (one map has one set of shared files).
    pub fn share(&mut self, shared: &SharedFiles) {
        match &self.shared {
            None => self.shared = Some(shared.clone()),
            Some(s) if Arc::ptr_eq(&s.0, &shared.0) => {}
            Some(_) => crate::internal::bug(None, "a source map attaches two sets of shared files"),
        }
    }

    /// The file `id`, if the map holds it.
    pub fn get(&self, id: FileId) -> Option<&SourceFile> {
        match id.0.checked_sub(SHARED_BASE) {
            Some(i) => self.shared.as_ref()?.0.get(i as usize),
            None => self.files.get(id.0 as usize),
        }
    }

    pub fn file(&self, id: FileId) -> &SourceFile {
        self.get(id).unwrap_or_else(|| panic!("{id:?} is not a file of the source map"))
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

    /// X-20 E (i): two maps attaching the same shared files hold them at the
    /// same ids, above their own files, which count from 0 as before; a map
    /// that did not attach them does not hold them; other shared files are a bug.
    #[test]
    fn shared_files_have_the_same_ids_in_every_map() {
        let shared =
            SharedFiles::new([("std/a.onsa".to_string(), "x\ny".to_string()), ("std/b.onsa".into(), "z".into())]);
        let ids: Vec<FileId> = shared.files().map(|(f, _)| f).collect();
        assert_eq!(ids, [FileId(SHARED_BASE), FileId(SHARED_BASE + 1)]);
        let mut maps = [SourceMap::default(), SourceMap::default()];
        for (k, m) in maps.iter_mut().enumerate() {
            assert!(m.get(ids[0]).is_none());
            assert_eq!(m.add(format!("u{k}.onsa"), "u"), FileId(0));
            m.share(&shared);
            m.share(&shared);
            assert_eq!(m.add("v.onsa", "v"), FileId(1));
        }
        for m in &maps {
            assert_eq!((m.file(ids[0]).name(), m.file(ids[0]).line_text(2)), ("std/a.onsa", Some("y")));
            assert_eq!(m.file(ids[1]).text(), "z");
            assert_eq!(m.file(FileId(1)).name(), "v.onsa");
            assert!(m.get(FileId(SHARED_BASE + 2)).is_none() && m.get(FileId(2)).is_none());
        }
        let other = SharedFiles::new([("std/a.onsa".to_string(), "x".to_string())]);
        let again = std::panic::catch_unwind(move || maps[0].clone().share(&other));
        assert!(again.unwrap_err().downcast_ref::<crate::internal::InternalBug>().is_some());
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

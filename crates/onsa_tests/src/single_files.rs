//! Single-file inputs checked as `onsa check` checks them, for the tools of
//! the fix candidates (`onsa_cases --fix-same-place`, `--fix-loop`): reading
//! one, and running the inputs on threads with the stack of a command.

/// The text of an input file, or why it cannot be read (as `onsa check`).
pub fn read_input(path: &str) -> Result<String, String> {
    text_of(std::fs::read(path))
}

/// The text of the bytes of an input, or why they cannot be read ([`read_input`]).
pub fn text_of(bytes: std::io::Result<Vec<u8>>) -> Result<String, String> {
    match bytes.map(String::from_utf8) {
        Err(e) => Err(e.to_string()),
        Ok(Err(_)) => Err("not UTF-8".into()),
        Ok(Ok(text)) => Ok(text),
    }
}

/// What `onsa_cases --fix-same-place` prints for `files`, read by `read`
/// (the files, or the texts of `onsa_cases --serve`): the near "same place"
/// of each file, each on a thread with the stack of a command, in parallel.
pub fn fix_same_place(files: &[String], read: impl Fn(&str) -> Result<String, String> + Sync) -> String {
    let items = on_stacks(files.len(), |i| {
        let path = &files[i];
        match read(path) {
            Err(e) => serde_json::json!({"file": path, "unreadable": e}),
            // A panic outside the driver's stages is an internal error too.
            Ok(text) => match onsa_driver::guard(|| crate::fix_contract::same_place(&text)) {
                Ok(r) => {
                    let mut v = serde_json::json!(r);
                    v["file"] = serde_json::json!(path);
                    v
                }
                Err(e) => serde_json::json!({"file": path, "candidates": 0, "violations": [], "internal": e.message}),
            },
        }
    });
    format!("{}\n", serde_json::to_string_pretty(&items).expect("serializes"))
}

/// `f` of each index below `n`, on threads with the stack of a command, in
/// parallel; the results in the order of the indexes.
pub fn on_stacks<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    let next = std::sync::atomic::AtomicUsize::new(0);
    let out: std::sync::Mutex<Vec<Option<T>>> = std::sync::Mutex::new((0..n).map(|_| None).collect());
    let workers = std::thread::available_parallelism().map_or(4, |w| w.get()).min(n.max(1));
    std::thread::scope(|s| {
        for _ in 0..workers {
            onsa_diag::stack::spawn_scoped(s, "onsa-fix", || {
                loop {
                    let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    if i >= n {
                        break;
                    }
                    let v = f(i);
                    out.lock().expect("results")[i] = Some(v);
                }
            })
            .expect("spawn a worker");
        }
    });
    out.into_inner().expect("results").into_iter().map(|v| v.expect("every index ran")).collect()
}

//! Single-file inputs checked as `onsa check` checks them, for the tools of
//! the fix candidates (`onsa_cases --fix-same-place`, `--fix-loop`): reading
//! one, and running the inputs on threads with the stack of a command.

/// The text of an input file, or why it cannot be read (as `onsa check`).
pub fn read_input(path: &str) -> Result<String, String> {
    match std::fs::read(path).map(String::from_utf8) {
        Err(e) => Err(e.to_string()),
        Ok(Err(_)) => Err("not UTF-8".into()),
        Ok(Ok(text)) => Ok(text),
    }
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

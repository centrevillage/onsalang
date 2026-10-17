use onsa_tests::fix_contract::{check_candidate, check_text};

fn one(path: String) -> Vec<String> {
    let mut out = Vec::new();
    let Ok(text) = std::fs::read_to_string(&path) else { return out };
    let run = match check_text(&text) {
        Ok(r) => r,
        Err(_) => {
            out.push(format!("{path}: INTERNAL"));
            return out;
        }
    };
    let a = &run.analyzed;
    let unread = a.unread_units();
    for d in a.diagnostics.iter() {
        if d.code.as_str() == "E0020" && d.fixes.iter().any(|f| f.edits().len() == 1 && &text[f.edits()[0].span.start as usize..f.edits()[0].span.end as usize] == ";" && f.edits()[0].replace.is_empty()) {
            out.push(format!("SEMI {path}"));
            break;
        }
    }
    for d in a.diagnostics.iter() {
        for (k, f) in d.fixes.iter().enumerate() {
            match check_candidate(&run, d, f) {
                Ok(c) => {
                    for p in &c.problems {
                        if p.contains("besides") {
                            let first: String = p.lines().next().unwrap_or("").chars().take(300).collect();
                            out.push(format!(
                                "{path}: {} fix{} unread={:?}: {first}\n        {}",
                                d.code.as_str(),
                                k + 1,
                                unread,
                                p.lines().skip(1).take(3).collect::<Vec<_>>().join(" | ")
                            ));
                        }
                    }
                }
                Err(_) => {}
            }
        }
    }
    out
}

#[test]
fn sweep() {
    let list = std::fs::read_to_string(std::env::var("SWEEP_LIST").unwrap()).unwrap();
    let mut n = 0;
    let mut hits = 0;
    let mut semis = 0;
    for path in list.lines().filter(|l| !l.is_empty()) {
        let p = path.to_string();
        let h = std::thread::Builder::new().stack_size(512 << 20).spawn(move || one(p)).unwrap();
        match h.join() {
            Ok(v) => {
                hits += v.len();
                for l in v {
                    if l.starts_with("SEMI") { hits -= 1; semis += 1; continue; }
                    println!("HIT {l}");
                }
            }
            Err(_) => println!("PANIC {path}"),
        }
        n += 1;
    }
    println!("SWEEP files={n} hits={hits} semicolon_mutants={semis}");
}

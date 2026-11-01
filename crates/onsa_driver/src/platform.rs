//! The build platforms (spec §15.3 item 1, §13.4): the architectures and the
//! systems this version knows, and the reading of a target triple. The check
//! of the manifest and the build read the same table.

/// A build platform (spec §15.3 item 1, §13.4): pointer width and the
/// compiler flags that keep the IEEE semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Platform {
    pub triple: String,
    pub arch: String,
    pub os: String,
    pub ptr_size: u32,
    /// Has an operating system (hosted): `poison` is the default panic mode.
    pub hosted: bool,
    pub msvc: bool,
    pub cflags: Vec<String>,
}

/// Triple of the machine the compiler runs on.
pub fn host_triple() -> String {
    let arch = match std::env::consts::ARCH {
        "aarch64" => "aarch64",
        "x86_64" => "x86_64",
        "x86" => "i686",
        "arm" => "armv7",
        other => other,
    };
    let os = match std::env::consts::OS {
        "macos" => "apple-darwin",
        "linux" => "unknown-linux-gnu",
        "windows" => "pc-windows-msvc",
        "freebsd" => "unknown-freebsd",
        other => other,
    };
    format!("{arch}-{os}")
}

/// The architectures this version knows, with their pointer widths in
/// bytes; a name ending in `*` is the head of a name (S-824).
const ARCHS: &[(u32, &[&str])] = &[
    (8, &["x86_64", "aarch64", "arm64", "riscv64", "powerpc64", "mips64", "wasm64"]),
    (4, &["i686", "i586", "i386", "riscv32*", "xtensa", "arm", "armv*", "thumbv*", "wasm32", "mips", "powerpc"]),
];

/// The operating systems this version knows: a word of the triple after its
/// architecture, and the system; a word `none` is no system (S-824, S-837).
const SYSTEMS: &[(&str, &str)] =
    &[("darwin*", "macos"), ("apple", "macos"), ("linux*", "linux"), ("windows*", "windows"), ("freebsd*", "freebsd")];

/// `word` is `name`, or starts with it when `name` ends in `*`.
fn word_is(word: &str, name: &str) -> bool {
    name.strip_suffix('*').map_or(word == name, |head| word.starts_with(head))
}

/// The note of a platform this version does not know (S-824): what
/// [`platform`] knows.
pub fn platforms_note() -> String {
    let archs: Vec<String> = ARCHS.iter().flat_map(|(_, a)| a.iter()).map(|a| format!("`{a}`")).collect();
    let systems: Vec<String> = SYSTEMS.iter().map(|(w, _)| format!("`{w}`")).collect();
    format!(
        "a platform is `\"host\"` or a target triple, read by its words between `-`: the first word is the \
         architecture, one of {}; a later word `none` is no operating system, else a later word is the system, \
         one of {} (`*`: the word may go on, as `darwin25.4.0`)",
        archs.join(", "),
        systems.join(", ")
    )
}

/// Resolve a target triple (`"host"` is the compiler's own machine).
pub fn platform(triple: &str) -> Result<Platform, String> {
    let triple = if triple == "host" { host_triple() } else { triple.to_string() };
    let parts: Vec<&str> = triple.split('-').collect();
    if parts.len() < 2 {
        return Err(format!("`{triple}` is not a target triple (`<arch>-<vendor>-<os>[-<abi>]`)"));
    }
    let (arch, words) = (parts[0].to_string(), &parts[1..]);
    let rest = words.join("-");
    let Some(&(ptr_size, _)) = ARCHS.iter().find(|(_, a)| a.iter().any(|a| word_is(&arch, a))) else {
        return Err(format!("unknown architecture `{arch}` in `{triple}`"));
    };
    let bare = words.contains(&"none");
    let msvc = rest.contains("msvc");
    let os = match SYSTEMS.iter().find(|(name, _)| words.iter().any(|w| word_is(w, name))) {
        _ if bare => "none".to_string(),
        Some((_, os)) => os.to_string(),
        None => return Err(format!("unknown operating system in `{triple}`")),
    };
    // The flags the generated C needs (spec §13.4) are the backend's; then
    // the optimization level, then the flags of the architecture.
    let (fp, opt) = if msvc { (onsa_backend_c::FP_CFLAGS_MSVC, "/O2") } else { (onsa_backend_c::FP_CFLAGS, "-O2") };
    let mut cflags: Vec<String> = fp.iter().chain([&opt]).map(|f| f.to_string()).collect();
    match arch.as_str() {
        "i686" | "i586" | "i386" if !msvc => cflags.extend(["-m32".into(), "-msse2".into(), "-mfpmath=sse".into()]),
        a if a.starts_with("thumbv") => {
            cflags.extend(["-mthumb".into(), "-ffreestanding".into(), "-DONSA_NO_TLS".into()]);
            if rest.ends_with("hf") {
                cflags.push("-mfloat-abi=hard".into());
            }
        }
        _ => {}
    }
    Ok(Platform { triple, arch, os, ptr_size, hosted: !bare, msvc, cflags })
}

impl Platform {
    /// The compiler runs on this platform (so `cc` can build for it): its
    /// triple is the host's, letter for letter (§15.3, S-837).
    pub fn is_host(&self) -> bool {
        self.triple == host_triple()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn platforms() {
        let p = platform("aarch64-apple-darwin").unwrap();
        assert_eq!((p.ptr_size, p.hosted, p.msvc, p.os.as_str()), (8, true, false, "macos"));
        assert!(p.cflags.contains(&"-ffp-contract=off".to_string()));
        let p = platform("thumbv7em-none-eabihf").unwrap();
        assert_eq!((p.ptr_size, p.hosted), (4, false));
        assert!(p.cflags.iter().any(|f| f == "-mfloat-abi=hard"));
        assert!(p.cflags.iter().any(|f| f == "-DONSA_NO_TLS"));
        let p = platform("i686-unknown-linux-gnu").unwrap();
        assert_eq!(p.ptr_size, 4);
        assert!(p.cflags.iter().any(|f| f == "-mfpmath=sse"));
        let p = platform("x86_64-pc-windows-msvc").unwrap();
        assert!(p.msvc && p.cflags.iter().any(|f| f == "/fp:strict"));
        assert!(platform("sparc-sun-solaris").is_err());
        assert!(platform("nonsense").is_err());
    }

    /// S-837 (1): the host is `"host"` and its triple letter for letter; another
    /// spelling of the machine, another system on it or a versioned system is
    /// not (none of them is a triple `host_triple` gives, on any machine).
    #[test]
    fn host_is_its_triple() {
        assert!(platform("host").unwrap().is_host());
        assert!(platform(&host_triple()).unwrap().is_host());
        for t in ["arm64-apple-darwin", "aarch64-apple-ios", "aarch64-apple-darwin25.4.0"] {
            assert_ne!(t, host_triple());
            assert!(!platform(t).unwrap().is_host(), "{t}");
        }
    }

    /// S-837 (B'): the words between `-` give the system: a word `none` is no
    /// system, a system word may go on, `apple` is a whole word, and `none` or
    /// a system inside another word is not read.
    #[test]
    fn systems_by_words() {
        let read = |t: &str| platform(t).map(|p| (p.hosted, p.os));
        let macos = Ok((true, "macos".to_string()));
        assert_eq!(read("aarch64-nonexistent-apple-darwin"), macos);
        assert_eq!(read("aarch64-apple-darwin25.4.0"), macos);
        assert_eq!(read("aarch64-apple-ios"), macos);
        assert_eq!(read("x86_64-unknown-linux-gnu"), Ok((true, "linux".to_string())));
        for (t, os) in [
            ("x86_64-unknown-linux6-gnu", "linux"),
            ("x86_64-pc-windows11", "windows"),
            ("x86_64-unknown-freebsd14", "freebsd"),
        ] {
            assert_eq!(read(t), Ok((true, os.to_string())), "{t}");
        }
        for t in ["x86_64-unknown-linux-none", "thumbv7em-none-eabihf", "riscv32imac-unknown-none-elf"] {
            assert_eq!(read(t), Ok((false, "none".to_string())), "{t}");
        }
        for t in ["arm-unknown-eabi", "aarch64-applex-ios", "aarch64-xdarwin", "aarch64-nonelinux"] {
            assert!(read(t).is_err(), "{t}");
        }
    }
}

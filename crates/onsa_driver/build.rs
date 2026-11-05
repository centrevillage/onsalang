//! Makes the base of the embedded std (W5-19): the bytes `onsa_driver` embeds
//! and reads back at the first check of a process, in place of parsing and
//! analyzing std in each process. It runs again when `onsa_sema` changes, a
//! build dependency, which std is part of.
//!
//! When no bytes come, std has a diagnostic or the analysis panicked, the
//! build goes on with the bytes that say so and a warning: the compiler makes
//! std in each process, as if nothing was embedded, where a panic is an
//! internal error with its position, and the driver's test
//! `std_parses_and_analyzes_cleanly` names the diagnostic.

use std::panic::catch_unwind;
use std::path::PathBuf;

use onsa_sema::Base;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    let bytes = match onsa_diag::stack::run(|| catch_unwind(onsa_sema::std_bytes)) {
        Ok(Ok(bytes)) => bytes,
        Ok(Err(why)) => unusable(&format!("{why:?}")),
        Err(_) => unusable("the analysis panicked"),
    };
    let dest = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR")).join("std_base.bin");
    std::fs::write(&dest, bytes).expect("write the base of std");
}

/// The bytes that say there is no base, and the warning.
fn unusable(why: &str) -> Vec<u8> {
    println!("cargo:warning=no base of std ({why}): each process of the compiler parses and analyzes std");
    Base::unusable_bytes().expect("the head writes")
}

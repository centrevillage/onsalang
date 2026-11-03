//! A fast hash for the tables of the analysis (W5-18 B1): the hash of
//! rustc-hash 1's `FxHasher`, with a seed. Use [`HashMap`] and [`HashSet`]
//! with `default()` and `with_capacity_and_hasher(n, Default::default())`.
//!
//! A table takes its seed when it is made ([`FxBuild`]'s `Default`) and keeps
//! it. The seed is 0 in a release build, so a command lists the same order
//! every time. A debug build takes one random seed for the process (std's
//! `RandomState` took a random key for each table): the order changes from
//! one run to the next as it did, so that the runs of the gate keep shaking
//! out an output that follows the order of a table. `ONSA_HASH_SEED` (a
//! decimal `u64`; empty is unset) fixes it, to repeat a run
//! ([`process_seed`]). A test changes it for the tables it makes on its
//! thread with [`with_seed`].

use std::cell::Cell;
use std::hash::{BuildHasher, Hasher};

pub type HashMap<K, V> = std::collections::HashMap<K, V, FxBuild>;
pub type HashSet<T> = std::collections::HashSet<T, FxBuild>;

/// Makes the hashers of one table, all from its seed.
#[derive(Debug, Clone, Copy)]
pub struct FxBuild {
    seed: u64,
}

impl Default for FxBuild {
    fn default() -> FxBuild {
        FxBuild { seed: OVERRIDE.with(Cell::get).unwrap_or_else(process_seed) }
    }
}

impl BuildHasher for FxBuild {
    type Hasher = FxHasher;

    fn build_hasher(&self) -> FxHasher {
        FxHasher { hash: self.seed }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct FxHasher {
    hash: u64,
}

impl FxHasher {
    fn add(&mut self, i: u64) {
        self.hash = (self.hash.rotate_left(5) ^ i).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

impl Hasher for FxHasher {
    /// Eight bytes at a time, then four, two and one (little-endian, so the
    /// order is the same on every host).
    fn write(&mut self, mut bytes: &[u8]) {
        while let Some((word, rest)) = bytes.split_first_chunk::<8>() {
            self.add(u64::from_le_bytes(*word));
            bytes = rest;
        }
        if let Some((word, rest)) = bytes.split_first_chunk::<4>() {
            self.add(u32::from_le_bytes(*word).into());
            bytes = rest;
        }
        if let Some((word, rest)) = bytes.split_first_chunk::<2>() {
            self.add(u16::from_le_bytes(*word).into());
            bytes = rest;
        }
        if let Some(&b) = bytes.first() {
            self.add(b.into());
        }
    }

    fn write_u8(&mut self, i: u8) {
        self.add(i.into());
    }

    fn write_u16(&mut self, i: u16) {
        self.add(i.into());
    }

    fn write_u32(&mut self, i: u32) {
        self.add(i.into());
    }

    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }

    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }

    /// The low bits of the product depend on the low bits of the input
    /// alone, and a table indexes by the low bits: bring the high ones down.
    fn finish(&self) -> u64 {
        self.hash.rotate_left(26)
    }
}

thread_local! {
    static OVERRIDE: Cell<Option<u64>> = const { Cell::new(None) };
}

/// The seed of the tables made on this thread outside [`with_seed`]: 0 in a
/// release build. In a debug build, `ONSA_HASH_SEED` if it is set and not
/// empty, else one random value for the process. Another value that is not a
/// decimal `u64` is an internal error (a panic), not a seed quietly dropped.
pub fn process_seed() -> u64 {
    #[cfg(debug_assertions)]
    {
        static SEED: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
        *SEED.get_or_init(|| match std::env::var("ONSA_HASH_SEED") {
            Ok(s) if !s.is_empty() => {
                s.parse().unwrap_or_else(|_| panic!("ONSA_HASH_SEED is not a decimal u64: `{s}`"))
            }
            Ok(_) | Err(std::env::VarError::NotPresent) => {
                std::collections::hash_map::RandomState::new().build_hasher().finish()
            }
            Err(e) => panic!("ONSA_HASH_SEED: {e}"),
        })
    }
    #[cfg(not(debug_assertions))]
    0
}

/// Runs `f` with `seed` for the tables it makes on this thread (in a debug
/// and a release build), and puts back the seed before, even if `f` panics.
pub fn with_seed<T>(seed: u64, f: impl FnOnce() -> T) -> T {
    struct Back(Option<u64>);
    impl Drop for Back {
        fn drop(&mut self) {
            OVERRIDE.with(|o| o.set(self.0));
        }
    }
    let _back = Back(OVERRIDE.with(|o| o.replace(Some(seed))));
    f()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash_with(seed: u64, bytes: &[u8]) -> u64 {
        let mut h = FxBuild { seed }.build_hasher();
        h.write(bytes);
        h.finish()
    }

    #[test]
    fn same_key_and_seed_same_hash() {
        let a = with_seed(7, || FxBuild::default().hash_one(("name", 3u32)));
        let b = with_seed(7, || FxBuild::default().hash_one(("name", 3u32)));
        assert_eq!(a, b);
    }

    #[test]
    fn the_seed_changes_the_hash() {
        let [a, b, c] = [0, 1, 12345].map(|k| with_seed(k, || FxBuild::default().hash_one("name")));
        assert!(a != b && b != c && a != c, "{a} {b} {c}");
    }

    #[test]
    fn with_seed_puts_back_the_seed_before() {
        with_seed(5, || {
            assert_eq!(with_seed(9, || FxBuild::default().seed), 9);
            assert_eq!(FxBuild::default().seed, 5);
        });
        assert_eq!(FxBuild::default().seed, process_seed());
    }

    /// `write` reads the words of 8, 4, 2 and 1 bytes, little-endian, and no
    /// byte twice: each length from 0 to 23 gives the words the rule gives.
    #[test]
    fn write_reads_each_byte_once() {
        let bytes: Vec<u8> = (1..=23).collect();
        for n in 0..=23 {
            let mut want = FxHasher { hash: 3 };
            let mut rest = &bytes[..n];
            for size in [8, 8, 4, 2, 1] {
                if rest.len() >= size {
                    let mut word = [0u8; 8];
                    word[..size].copy_from_slice(&rest[..size]);
                    want.add(u64::from_le_bytes(word));
                    rest = &rest[size..];
                }
            }
            assert!(rest.is_empty(), "{n}");
            assert_eq!(hash_with(3, &bytes[..n]), want.finish(), "{n} bytes");
        }
        // The last byte counts: two inputs that differ only there hash apart.
        assert_ne!(hash_with(0, &[1, 2, 3, 4, 5, 6, 7, 8, 9]), hash_with(0, &[1, 2, 3, 4, 5, 6, 7, 8, 10]));
        assert_eq!(hash_with(0, &[]), 0);
        assert_eq!(hash_with(0, &[1]), 0x517c_c1b7_2722_0a95_u64.rotate_left(26));
    }
}

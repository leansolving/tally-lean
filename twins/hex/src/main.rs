//! Independent, unverified twin counter for OEIS A066864 (independent sets of the
//! n x n rhombus of the triangular lattice; hard hexagons with free boundary).
//!
//! It does NOT count independent sets. It counts, via the identity stated by
//! A. P. Heinz in the A066864 entry, the tilings of the (n+1) x (n+1) square by
//! 1 x 1 squares and L-trominoes in one fixed orientation (the 2 x 2 block minus
//! its upper-right cell). The algorithm is a port of Heinz's Maple program
//! (A066864 %p, ported to Python in scan/proto/a066864.py, function `tiling`):
//!
//!   b(m, l) = 1                                    if m < 2
//!           = b(m-1, l - 1)                        if min(l) > 0
//!           = b(m, l[k:=1])                        (place a square at k)
//!             + [k+1 < w and l[k+1] = 0] b(m, l[k:=2, k+1:=1])   (place an L)
//!                                                  where k = first index with l[k] = 0
//!   a(n) = b(n+1, [0; n+1]).
//!
//! Here l is the height profile of the tiled region above the current base row
//! (w = n+1 entries, each 0, 1 or 2) and m is the number of rows not yet
//! completed. The L placed at column k covers (k, row), (k, row+1), (k+1, row).
//! When m = 1 the last row can only be filled by squares, so it contributes 1.
//!
//! Layered forward version (memory one layer at a time): the recursion always
//! fills the leftmost empty cell of the base row, so we sweep the base row
//! cell by cell, k = 0..w-1. At layer (row, k) a state with l[k] != 0 is passed
//! on unchanged; a state with l[k] = 0 branches exactly as above. After the last
//! cell all entries are positive and the profile shifts down by one (l - 1),
//! which is injective. This runs for the n rows with m = n+1, ..., 2; the
//! answer is the sum of all counts left (each such state has b(1, l) = 1).
//!
//! State key: u128 holding Heinz's profile literally, column j in bits
//! [2j, 2j+2), so w = n+1 <= 64. Counts are GMP integers (rug::Integer).
//!
//! Why this is an independent check of the Tally frontier DP: Tally sweeps the
//! n x n rhombus and keeps one bit per column (last cell of that column in the
//! independent set), testing left, above and above-right neighbours. This
//! program works on a different object (tilings of an (n+1) x (n+1) square),
//! with a different state (tile heights 0..2 under a first-empty-cell rule) and
//! enforces the hard-core constraint only implicitly, through non-overlap of
//! tiles. Agreement therefore also tests the Lean adjacency definition against
//! Heinz's bijection and the published b-files. Shared with Tally: nothing but
//! the general idea of a row-wise profile DP.

use rug::Integer;
use rustc_hash::FxHashMap;
use std::collections::hash_map::Entry;
use std::time::Instant;

#[inline(always)]
fn get(key: u128, j: usize) -> u128 {
    (key >> (2 * j)) & 3
}

#[inline(always)]
fn add_to(map: &mut FxHashMap<u128, Integer>, key: u128, cnt: Integer) {
    match map.entry(key) {
        Entry::Occupied(mut e) => *e.get_mut() += &cnt,
        Entry::Vacant(e) => {
            e.insert(cnt);
        }
    }
}

fn peak_rss_bytes() -> u64 {
    let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
    unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut ru) };
    let v = ru.ru_maxrss as u64;
    if cfg!(target_os = "macos") { v } else { v * 1024 }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: hex <n>");
        std::process::exit(2);
    }
    let n: usize = args[1].parse().expect("n");
    assert!(n <= 63, "u128 profile packing supports n <= 63");

    let t0 = Instant::now();
    let w = n + 1;
    // ones = the profile with every entry equal to 1 (used for the shift l - 1)
    let ones: u128 = (0..w).fold(0u128, |a, j| a | (1u128 << (2 * j)));
    let mut st: FxHashMap<u128, Integer> = FxHashMap::default();
    st.insert(0, Integer::from(1));
    let mut nst: FxHashMap<u128, Integer> = FxHashMap::default();
    let mut max_states: usize = 1;
    let mut transitions: u64 = 0; // successor insertions
    let mut sources: u64 = 0; // states processed

    // rows with m = n+1, ..., 2 (m = 1 contributes the factor 1)
    for _row in 0..n {
        for k in 0..w {
            nst.clear();
            nst.reserve(st.len() + st.len() / 2);
            sources += st.len() as u64;
            let sh = 2 * k as u32;
            for (key, cnt) in st.drain() {
                if get(key, k) != 0 {
                    // not the first empty cell: pass through
                    transitions += 1;
                    add_to(&mut nst, key, cnt);
                    continue;
                }
                if k + 1 < w && get(key, k + 1) == 0 {
                    // L-tromino: l[k] := 2, l[k+1] := 1
                    transitions += 2;
                    let lk = key | (2u128 << sh) | (1u128 << (sh + 2));
                    add_to(&mut nst, lk, cnt.clone());
                }
                else {
                    transitions += 1;
                }
                // square: l[k] := 1
                add_to(&mut nst, key | (1u128 << sh), cnt);
            }
            std::mem::swap(&mut st, &mut nst);
            max_states = max_states.max(st.len());
        }
        // base row complete: every entry is 1 or 2; shift the profile down (l - 1)
        nst.clear();
        nst.reserve(st.len());
        for (key, cnt) in st.drain() {
            assert!((key | (key >> 1)) & ones == ones, "row not complete");
            nst.insert(key - ones, cnt); // injective, no merging
        }
        std::mem::swap(&mut st, &mut nst);
    }

    let mut total = Integer::new();
    for cnt in st.values() {
        total += cnt;
    }
    let secs = t0.elapsed().as_secs_f64();
    println!("n={} count={} states={}", n, total, max_states);
    eprintln!(
        "time={:.3}s sources={} transitions={} trans_per_s={:.3e} peak_rss={} rss_bytes_per_max_state={:.1}",
        secs,
        sources,
        transitions,
        transitions as f64 / secs.max(1e-9),
        peak_rss_bytes(),
        peak_rss_bytes() as f64 / max_states as f64
    );
}

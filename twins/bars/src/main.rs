//! Independent, unverified twin counter for n x n binary arrays whose ones form
//! pairwise non-touching 1 x k / k x 1 bars (A145773 k=2, A145757 k=3, A145789 k=4).
//!
//! Port of scan/proto/bars.py: nondeterministic broken-profile DP, cell by cell in
//! row-major order.
//!   profile entry (what the cell above demands of the cell below):
//!     0 = free, 1 = B (must be 0), 2..=k = V1..V(k-1) (vertical bar must continue)
//!   left register (what the cell to the left demands of the current cell):
//!     0 = free, 1 = mustZero, 2..=k = H1..H(k-1) (horizontal bar must continue)
//! A fresh one (above free, left free) is either the start of a vertical bar
//! (entry 2, left 1) or the start of a horizontal bar (entry 1, left 2).
//!
//! State key: u64, column c in bits [3c, 3c+3), left register in bits [60, 63).

use rug::Integer;
use rustc_hash::FxHashMap;
use std::time::Instant;

const LEFT_SHIFT: u32 = 60;

#[inline(always)]
fn get(key: u64, c: usize) -> u64 {
    (key >> (3 * c)) & 7
}

fn peak_rss_bytes() -> u64 {
    let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
    unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut ru) };
    let v = ru.ru_maxrss as u64;
    if cfg!(target_os = "macos") { v } else { v * 1024 }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: bars <k> <n>");
        std::process::exit(2);
    }
    let k: u64 = args[1].parse().expect("k");
    let n: usize = args[2].parse().expect("n");
    assert!((2..=7).contains(&k), "need 2 <= k <= 7 (3-bit entries, k=1 would double count)");
    assert!(n <= 20, "u64 packing supports n <= 20");

    let t0 = Instant::now();
    let w = n;
    let mut st: FxHashMap<u64, Integer> = FxHashMap::default();
    st.insert(0, Integer::from(1));
    let mut nst: FxHashMap<u64, Integer> = FxHashMap::default();
    let mut max_states: usize = 1;
    let mut transitions: u64 = 0; // successor insertions
    let mut sources: u64 = 0; // states processed

    for _r in 0..n {
        for c in 0..w {
            nst.clear();
            nst.reserve(st.len() + st.len() / 2);
            let sh = 3 * c as u32;
            let mask = !(7u64 << sh) & !(7u64 << LEFT_SHIFT);
            sources += st.len() as u64;
            for (key, cnt) in st.drain() {
                let above = get(key, c);
                let left = key >> LEFT_SHIFT;
                let base = key & mask;
                // up to 3 options (newprofentry, newleft)
                let mut opts = [(0u64, 0u64); 3];
                let m: usize;
                if (2..=k).contains(&above) {
                    // vertical continues
                    if left != 0 {
                        continue;
                    }
                    if above == k {
                        opts[0] = (1, 1);
                    } else {
                        opts[0] = (above + 1, 1);
                    }
                    m = 1;
                } else if above == 1 {
                    if (2..=k).contains(&left) {
                        continue;
                    }
                    opts[0] = (0, 0);
                    m = 1;
                } else if (2..=k).contains(&left) {
                    if left == k {
                        opts[0] = (1, 1);
                    } else {
                        opts[0] = (1, left + 1);
                    }
                    m = 1;
                } else if left == 1 {
                    opts[0] = (0, 0);
                    m = 1;
                } else {
                    opts[0] = (0, 0);
                    opts[1] = (2, 1); // start vertical
                    opts[2] = (1, 2); // start horizontal
                    m = 3;
                }
                transitions += m as u64;
                for i in 0..m {
                    let (pe, nl) = opts[i];
                    let nk = base | (pe << sh) | (nl << LEFT_SHIFT);
                    if i + 1 == m {
                        // last option: move the count
                        match nst.get_mut(&nk) {
                            Some(e) => *e += &cnt,
                            None => {
                                nst.insert(nk, cnt);
                                break;
                            }
                        }
                    } else {
                        match nst.get_mut(&nk) {
                            Some(e) => *e += &cnt,
                            None => {
                                nst.insert(nk, cnt.clone());
                            }
                        }
                    }
                }
            }
            std::mem::swap(&mut st, &mut nst);
            max_states = max_states.max(st.len());
        }
        // end of row: no pending horizontal bar; reset left register
        nst.clear();
        nst.reserve(st.len());
        for (key, cnt) in st.drain() {
            let left = key >> LEFT_SHIFT;
            if (2..=k).contains(&left) {
                continue;
            }
            let nk = key & !(7u64 << LEFT_SHIFT);
            match nst.get_mut(&nk) {
                Some(e) => *e += &cnt,
                None => {
                    nst.insert(nk, cnt);
                }
            }
        }
        std::mem::swap(&mut st, &mut nst);
    }

    // accept: no vertical bar pending below the last row
    let mut total = Integer::new();
    for (key, cnt) in st.iter() {
        if (0..w).all(|c| get(*key, c) <= 1) {
            total += cnt;
        }
    }
    let secs = t0.elapsed().as_secs_f64();
    println!("k={} n={} count={} states={}", k, n, total, max_states);
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

// Count independent sets of the n x n grid graph (OEIS A006506) by a
// cell-by-cell frontier DP. State bit c = cell above (r-1,c), bit c-1 = left cell.
use rustc_hash::FxHashMap;
use std::time::Instant;

#[cfg(feature = "gmp")]
type Big = rug::Integer;
#[cfg(all(feature = "bigint", not(feature = "gmp")))]
type Big = num_bigint::BigUint;

#[cfg(feature = "gmp")]
const BACKEND: &str = "rug(GMP)";
#[cfg(all(feature = "bigint", not(feature = "gmp")))]
const BACKEND: &str = "num-bigint";

fn one() -> Big {
    Big::from(1u32)
}

#[inline]
fn add_to(m: &mut FxHashMap<u64, Big>, s: u64, v: &Big) {
    match m.get_mut(&s) {
        Some(w) => *w += v,
        None => {
            m.insert(s, v.clone());
        }
    }
}

fn count(n: usize) -> (Big, usize, u64) {
    let mut cur: FxHashMap<u64, Big> = FxHashMap::default();
    cur.insert(0, one());
    let mut max_states = 1usize;
    let mut pairs: u64 = 0;
    for _r in 0..n {
        for c in 0..n {
            let bit: u64 = 1u64 << c;
            let mask: u64 = if c == 0 { bit } else { bit | (bit >> 1) };
            pairs += 2 * cur.len() as u64;
            let mut nxt: FxHashMap<u64, Big> = FxHashMap::default();
            nxt.reserve(cur.len() + cur.len() / 2);
            for (s, v) in cur.drain() {
                if s & mask == 0 {
                    add_to(&mut nxt, s | bit, &v);
                }
                // symbol 0: move v into the map when the slot is new
                let t = s & !bit;
                match nxt.get_mut(&t) {
                    Some(w) => *w += &v,
                    None => {
                        nxt.insert(t, v);
                    }
                }
            }
            cur = nxt;
            max_states = max_states.max(cur.len());
        }
    }
    let mut total = Big::from(0u32);
    for v in cur.values() {
        total += v;
    }
    (total, max_states, pairs)
}

fn vm_hwm() -> String {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmHWM:"))
                .map(|l| l[6..].split_whitespace().collect::<String>())
        })
        .unwrap_or_else(|| "?".to_string())
}

fn main() {
    let n: usize = std::env::args()
        .nth(1)
        .expect("usage: gridis N")
        .parse()
        .expect("N");
    assert!(n >= 1 && n <= 63);
    let t0 = Instant::now();
    let (cnt, ms, pairs) = count(n);
    let s = cnt.to_string();
    let dt = t0.elapsed().as_secs_f64();
    println!(
        "variant=rust backend={} n={} count={} digits={} maxstates={} pairs={} time_s={:.6} vmhwm={}",
        BACKEND, n, s, s.len(), ms, pairs, dt, vm_hwm()
    );
}

# Tally, verified counting in Lean 4

[![CI](https://github.com/leansolving/tally-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/leansolving/tally-lean/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.30.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.30.0)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.30.0-blue)](https://github.com/leanprover-community/mathlib4/releases/tag/v4.30.0)

Tally computes terms of integer sequences from the [OEIS](https://oeis.org)
as theorems of Lean 4. The engine counts discrete objects in general; the OEIS
is its intended use. It consists of a generic layered dynamic-programming
engine, proved correct once, and one specification per family of related OEIS
sequences, each with a proof that the words the specification accepts
correspond to the objects the OEIS entry counts. A specification is a root
state and a step function that, for each layer and symbol, rejects or returns
the next state, plus an acceptance test on the final state; a word has one
symbol per layer, and for the grid sequences a layer is one cell of the grid.
A term `A(n) = N` is then a Lean theorem proved with `native_decide`: the
compiled engine computes the count, and the kernel accepts the result through
an axiom recorded for that theorem (see Trust base).

The engine implements the transfer-matrix method of enumerative combinatorics.
It processes the cells one at a time; after each cell, a state records only
what the remaining cells need to know about the cells already filled (for
independent sets, which cells of the current row boundary are occupied). One
hash map per layer maps each state to the number of partial words that reach
it, and partial words with the same state are merged by adding their counts.

## Trust base

Every claimed value rests on the following three theorems.

1. The engine theorem `Tally.Spec.count_eq` (`Tally/Engine.lean`): for every
   layered specification, the engine returns the number of accepted words.
   Kernel-checked; axioms `propext`, `Classical.choice`, `Quot.sound` only.
2. The family theorem, for example `Tally.GridIndep.A006506_eq_count`: for
   `n ≤ 64`, `A006506 n` (defined on the OEIS side as the number of
   independent sets of the `n × n` grid graph, as a `Fintype.card`) equals the
   engine's count on the family's packed specification. Kernel-checked, same
   three axioms.
3. The value theorem, for example `TallyValues.GridIndep.A006506_34`:
   `A006506 34 = 3878911...`. Proved by rewriting with the family theorem and
   evaluating a compiled checker with `native_decide`. Lean 4.30 records this
   as a per-theorem axiom `A006506_34._native.native_decide.ax_*`; the trust
   base is the Lean kernel together with the Lean compiler, runtime and GMP.

`#print axioms` is run on every main theorem, with a positive control
(`Tally/Examples.lean`, a `native_decide` theorem whose axiom must show up).
The library contains no `sorry`, `implemented_by`, `extern`, `partial` or
`unsafe`. The script `scripts/audit.sh` performs both checks; CI runs it after
every build.

Every new term is additionally cross-checked by an independent, unverified
Rust counter of a different formulation (`twins/`) before it is reported.

## Results

Reproduced OEIS terms (value theorems agreeing with the b-files):

| Sequence | Objects | Reproduced |
|---|---|---|
| A006506 | independent sets of the n × n grid | n ≤ 22, n = 30, 32, 34 |
| A066864 | independent sets of the n × n rhombus of the triangular lattice (grid plus one diagonal) | n ≤ 12 |
| A145789 | n × n binary arrays whose ones form 1 × 4 or 4 × 1 bars, no two edge-adjacent (diagonal contact allowed) | n ≤ 16 |
| A145757 | the same with 1 × 3 bars | n ≤ 13 |
| A145773 | the same with 1 × 2 bars | n ≤ 16 |

New terms, not previously in the OEIS, each a value theorem and each
confirmed by the Rust twin:

| Sequence | n | value |
|---|---|---|
| A145789 | 17 | 9785146634014064625393401 |
| A145789 | 18 | 11262206161582131074872044449 |
| A145757 | 14 | 2888043759564731544899 |
| A145757 | 15 | 4445172150564510501924876 |
| A145757 | 16 | 11333612994442379223678158722 |
| A145757 | 17 | 47899376481659557565552633068946 |
| A145757 | 18 | 335445240830628876055122463675824591 |
| A145757 | 19 | 3893352754929945400656602001519284982288 |
| A145757 | 20 | 74884831469127956412481229662897119514478477 |
| A145773 | 17 | 46839836853957809440360002900901859008904988 |
| A145773 | 18 | 8474755609615024639072040185775092207187308736075 |
| A145773 | 19 | 3049316398131213684814440285325751907489056552840344971 |
| A145773 | 20 | 2181932762442101813725359996607027632484242114323157049789130 |

The value modules for these terms are `TallyValues/Bars_<k>_<n>.lean`
(k = bar length). They take from minutes to hours and several GB each and are
therefore not imported by `TallyValues.lean`; build one with
`lake build TallyValues.Bars_3_18`.

## Layout

- `Tally/Spec.lean`: layered specifications (`Spec`), acceptance, completion
  counts, and two generic proof tools a family instantiates: frontier
  descriptions (`IsFront`, `accepts_iff_front`) and simulations between a
  packed and a mathematical specification (`IsSim`, `accepts_iff_sim`).
- `Tally/Engine.lean`: the engine (`Spec.count`) and its theorem
  `Spec.count_eq`, plus `count_eq_of_sim`.
- `Tally/Grid.lean`, `Tally/Bits.lean`: shared lemmas for grid words and for
  `UInt64` bit fields.
- `Tally/Families/GridIndep*.lean`: A006506 and A066864 (one family with a
  Boolean parameter that selects the grid graph or the grid plus anti-diagonal).
- `Tally/Families/BarArray*.lean`: A145789, A145757, A145773.
- `Tally/Examples.lean`: toy specifications and the axiom audit.
- `TallyValues/`: value theorems (separate library, see Results and Building).
- `Main.lean`: `lake exe tally-lean`, an unverified command-line runner of the
  verified engine, for timings and cross-checks.
- `twins/gridis`, `twins/bars`: the independent Rust counters.

## Building

Toolchain: `leanprover/lean4:v4.30.0` with Mathlib `v4.30.0` (pinned in
`lean-toolchain` and `lake-manifest.json`). With `elan` installed:

```
lake exe cache get      # Mathlib build cache
lake build              # library Tally, kernel-checked part
lake build TallyValues  # value theorems for small n (minutes)
lake exe tally-lean 20          # A006506(20), unverified runner
lake exe tally-lean hex 20      # A066864(20)
lake exe tally-lean bar 3 12    # A145757(12)
```

A parallel variant of the engine, `Spec.countPar` (`Tally/Engine.lean`, section
"Parallel engine"), splits the states of every layer into `P` disjoint parts and
processes them in `P` parallel tasks. Its theorem `Spec.countPar_eq` is proved
with the same invariant as `Spec.count_eq`. `Task.spawn` and `Task.get` have
ordinary definitions in the Lean core library (`Task.spawn f` is `⟨f ()⟩`,
`Task.get` is the field projection) and the proofs unfold them, so value
theorems through `checkCountPar` have the same trust base as through
`checkCount`. Splitting the layer also keeps every hash map below 2^27 buckets;
on Linux the Lean runtime does not free larger bucket arrays, so a sequential
run beyond about 1e8 states per layer grows until it fails.
`lake exe tally-lean par 8 hex 30` runs the parallel engine with 8 parts.

`Tally` is built with `precompileModules`, so that `native_decide` in the
value theorems runs the compiled engine rather than the IR interpreter. Each
value proof goes through an out-of-line compiled checker (`checkCount`) for the
same reason.

The Rust twins need `cargo` and GMP (through the `rug` crate):
`cd twins/bars && cargo build --release && target/release/bars 3 12`.

## Development

The code and proofs were developed with AI assistance (Claude Code with Opus and
Fable models). The Lean kernel checks every proof, so the trust base stated
above does not depend on how a proof was found. During development, each edit
was checked with [LeanBack](https://pypi.org/project/leanback/), the author's
Model Context Protocol (MCP) server through which an AI assistant calls Lean 4
(check, prove, goals, eval, search).

## Author

Stefan Szeider, TU Wien. Licensed under the Apache License 2.0 (see `LICENSE`).

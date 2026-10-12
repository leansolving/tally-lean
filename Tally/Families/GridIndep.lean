import Tally.Grid

/-!
# Independent sets of the `n × n` grid, with or without a diagonal (OEIS A006506, A066864)

One family with a Boolean parameter `d`:

* `d = false`: the `n × n` grid graph (cells adjacent along rows and columns).
  `A006506 n` is its number of independent vertex sets.
* `d = true`: the grid graph plus the anti-diagonal edges `(r, c) ~ (r + 1, c - 1)`,
  which is the `n × n` rhombus of the triangular lattice ("hard hexagons" with free
  boundary). `A066864 n` is its number of independent vertex sets ("binary
  arrangements without adjacent 1's on n X n rhombic hexagonal grid", OEIS; the
  entry's program uses exactly this anti-diagonal, and the main-diagonal choice is
  isomorphic by reflecting columns).

The OEIS-facing definitions are stated on `Finset (Fin n × Fin n)` with the explicit
adjacency `AdjD n d` (`AdjD n false` is `Tally.Grid.Adj`, the adjacency of
`pathGraph n □ pathGraph n`).

The counting goes through two specifications:

* `mspec n d`, the mathematical frontier specification with state `Fin n → Bool`:
  cells are read in row-major order, the state remembers for each column the most
  recently read cell of that column, and a cell may be selected only if its earlier
  neighbours are not: the cell above, the cell to the left, and for `d = true` the
  cell above-right (`(r - 1, c + 1)`, still present in the frontier since column
  `c + 1` has not been read in row `r` yet).
* `fspec n d`, the same automaton with the frontier packed into a `UInt64` bitmask
  (valid for `n ≤ 64`), which is what the engine runs.

This file holds the definitions only. `GridIndepAccept` proves `accepts_iff` (a word
is accepted by `mspec n d` iff it selects an independent set) and `A_eq_card`;
`GridIndepFast` proves `fspec_isSim` (for `n ≤ 64` the bitmask spec simulates
`mspec n d`); `GridIndepMain` assembles `A006506_eq_count` and `A066864_eq_count`.
-/

namespace Tally.GridIndep

open Tally Tally.Grid

variable (n : Nat) (d : Bool)

/-! ### The combinatorial objects -/

/-- Anti-diagonal adjacency: `(r, c) ~ (r + 1, c - 1)` (either way round). -/
def AntiDiag (u v : V n) : Prop :=
  (u.1.val + 1 = v.1.val ∧ v.2.val + 1 = u.2.val) ∨
  (v.1.val + 1 = u.1.val ∧ u.2.val + 1 = v.2.val)

instance : DecidableRel (AntiDiag n) := fun _ _ => by unfold AntiDiag; infer_instance

/-- Adjacency of the family: the grid adjacency, plus the anti-diagonal when `d = true`. -/
def AdjD (u v : V n) : Prop := Adj n u v ∨ (d = true ∧ AntiDiag n u v)

instance : DecidableRel (AdjD n d) := fun _ _ => by unfold AdjD; infer_instance

theorem adjD_false (u v : V n) : AdjD n false u v ↔ Adj n u v := by
  simp [AdjD]

/-- A vertex set is independent iff it contains no two adjacent vertices. -/
def IsIndep (s : Finset (V n)) : Prop := ∀ u ∈ s, ∀ v ∈ s, ¬ AdjD n d u v

instance : DecidablePred (IsIndep n d) := fun _ => by unfold IsIndep; infer_instance

/-- **OEIS A006506**: the number of independent vertex sets of the `n × n` grid graph. -/
def A006506 (n : Nat) : Nat := Fintype.card {s : Finset (V n) // IsIndep n false s}

/-- **OEIS A066864**: the number of independent vertex sets of the `n × n` rhombus of the
triangular lattice, i.e. the `n × n` grid graph with the anti-diagonals
`(r, c) ~ (r + 1, c - 1)` added. -/
def A066864 (n : Nat) : Nat := Fintype.card {s : Finset (V n) // IsIndep n true s}

/-! ### The mathematical frontier specification -/

/-- Frontier state: for each column, whether its most recently read cell is selected. -/
abbrev MState := Fin n → Bool

/-- One step of the frontier automaton at cell index `i` (row `i / n`, column `i % n`):
a selected cell is rejected if the cell above, the cell to the left, or (for `d = true`)
the cell above-right is selected; the frontier entry of the column is then replaced. -/
def mstep (i : Nat) (s : MState n) (a : Fin 2) : Option (MState n) :=
  if hc : i % n < n then
    let c : Fin n := ⟨i % n, hc⟩
    let above := s c
    let left := if hc0 : 0 < c.val then s ⟨c.val - 1, by omega⟩ else false
    let aboveRight := d && (if hc1 : c.val + 1 < n then s ⟨c.val + 1, hc1⟩ else false)
    if a.val = 1 then
      if above || left || aboveRight then none else some (Function.update s c true)
    else some (Function.update s c false)
  else none

/-- The mathematical specification: `n * n` cells in row-major order, symbols `0`/`1`. -/
def mspec : Spec (MState n) (n * n) 2 where
  root := fun _ => false
  step := mstep n d
  final := fun _ => true

/-! ### Frontier description and local conditions (used by `GridIndepAccept`) -/

/-- The frontier after reading the first `i` cells (row `i / n`, column `i % n`):
column `j` holds cell `(i / n, j)` if `j < i % n`, else cell `(i / n - 1, j)`. -/
def front (w : Word (n * n) 2) (i : Nat) : MState n := fun j =>
  if j.val < i % n then selAt n w (i / n) j.val
  else if 0 < i / n then selAt n w (i / n - 1) j.val else false

/-- No two selected cells among the first `i` are adjacent. -/
def IndepUpTo (w : Word (n * n) 2) (i : Nat) : Prop :=
  ∀ u v : V n, (cell n u).val < i → (cell n v).val < i →
    w (cell n u) = 1 → w (cell n v) = 1 → ¬ AdjD n d u v

instance (w : Word (n * n) 2) (i : Nat) : Decidable (IndepUpTo n d w i) := by
  unfold IndepUpTo; infer_instance

/-- Whether the cell above cell `i` is selected. -/
def aboveSel (w : Word (n * n) 2) (i : Nat) : Bool :=
  if 0 < i / n then selAt n w (i / n - 1) (i % n) else false

/-- Whether the cell left of cell `i` is selected. -/
def leftSel (w : Word (n * n) 2) (i : Nat) : Bool :=
  if 0 < i % n then selAt n w (i / n) (i % n - 1) else false

/-- Whether the cell above-right of cell `i` is selected (`false` off the board). -/
def aboveRightSel (w : Word (n * n) 2) (i : Nat) : Bool :=
  if 0 < i / n ∧ i % n + 1 < n then selAt n w (i / n - 1) (i % n + 1) else false

/-- The earlier neighbours of cell `i` that the step at `i` checks, as a Boolean. -/
def blocked (w : Word (n * n) 2) (i : Nat) : Bool :=
  aboveSel n w i || leftSel n w i || (d && aboveRightSel n w i)

/-! ### The bitmask specification -/

/-- One step of the bitmask automaton; bit `c` of the state is column `c` of the frontier.
The above-right test reads bit `c + 1`, guarded by `c + 1 < n` so that only frontier bits
are read. -/
def fstep (i : Nat) (s : UInt64) (a : Fin 2) : Option UInt64 :=
  let c := i % n
  let bit : UInt64 := (1 : UInt64) <<< c.toUInt64
  let above := (s &&& bit) != 0
  let left := c != 0 && (s &&& (bit >>> 1)) != 0
  let aboveRight := d && c + 1 < n && (s &&& (bit <<< 1)) != 0
  if a.val = 1 then
    if above || left || aboveRight then none else some (s ||| bit)
  else some (s &&& ~~~bit)

/-- The bitmask specification run by the engine (correct for `n ≤ 64`). -/
def fspec : Spec UInt64 (n * n) 2 where
  root := 0
  step := fstep n d
  final := fun _ => true

/-- Shard partition for the parallel engine (performance only, see `Spec.countPar`): the
step at layer `i` modifies frontier bit `i % n`, so the key is the top `m` bits while
`i % n < n - m` and the low `m` bits otherwise; it changes only twice per row. -/
def part (m : Nat) (i : Nat) (s : UInt64) : Nat :=
  if i % n < n - m then (s >>> (n - m).toUInt64).toNat else (s &&& ((1 <<< m.toUInt64) - 1)).toNat

/-- Fresh spec object per worker of the parallel engine: `noinline` so that each call
allocates its own closure objects (see `Spec.advancePar`). -/
@[noinline] def mkSpec (n : Nat) (d : Bool) (_j : Nat) : Spec UInt64 (n * n) 2 := fspec n d

/-- Fresh partition closure per worker of the parallel engine. -/
@[noinline] def mkPart (n m : Nat) (_j : Nat) : Nat → UInt64 → Nat := part n m

/-- Simulation relation: the low `n` bits of `s` are the frontier `t`. -/
def Rel (s : UInt64) (t : MState n) : Prop := ∀ j : Fin n, s.toBitVec.getLsbD j.val = t j

end Tally.GridIndep

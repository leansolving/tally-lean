import Tally.Grid
import Tally.Bits

/-!
# Binary arrays whose ones form `1 × k` bars, no two edge-adjacent (OEIS A145757, A145773, A145789)

`A145789 n` counts `n × n` binary arrays "with all ones connected only either
four adjacent vertically or four adjacent horizontally" (OEIS): every connected
component of the ones is a horizontal or vertical bar of exactly four cells.
`A145757` is the same with bars of three cells. We define `IsBarArray n k f`
for a general bar length `k ≥ 2`: every one-cell lies in a `k`-bar of ones that
has no one-cell adjacent to it from outside (so that bar is its whole
component).

The counting goes through a deterministic frontier automaton reading the cells
in row-major order with alphabet `{0, 1}`:

* the frontier remembers, per column, whether the last cell read there is
  empty (`free`), a one that must not be extended downwards (`block`: it lies
  in a horizontal bar or ends a vertical bar), or the lowest cell of a vertical
  run of `m < k` ones that must continue (`vert m`);
* the "left" register remembers the cell to the left: empty (`free`), a one that
  must not be extended to the right (`block`), a fresh single one whose bar
  direction is not yet known (`pend`), or the last cell of a horizontal run of
  `m < k` ones that must continue (`horiz m`).

A fresh one with empty neighbours above and to the left is recorded as a
vertical run of length one and `pend`; the next cell in the row resolves it:
a one turns both into a horizontal run, a zero leaves it vertical.
-/

namespace Tally.BarArray

open Tally Tally.Grid Tally.Bits

variable (n k : Nat)

/-! ### The combinatorial objects -/

/-- A bar: `k` consecutive cells in a row (`horizontal := true`) or a column,
with the top-left cell `(r, c)`. Validity (fits on the board) is a separate predicate. -/
structure Bar where
  /-- `true` for a bar along a row, `false` for a bar along a column. -/
  horizontal : Bool
  /-- Row of the top-left cell. -/
  r : Nat
  /-- Column of the top-left cell. -/
  c : Nat
  deriving DecidableEq, Repr

/-- The cells of a bar (as coordinates, not necessarily on the board). -/
def Bar.cells (b : Bar) : List (Nat × Nat) :=
  (List.range k).map fun t => if b.horizontal then (b.r, b.c + t) else (b.r + t, b.c)

/-- A bar lies on the `n × n` board. -/
def Bar.OnBoard (b : Bar) : Prop :=
  b.r < n ∧ b.c < n ∧ (if b.horizontal then b.c + k ≤ n else b.r + k ≤ n)

instance (b : Bar) : Decidable (Bar.OnBoard n k b) := by unfold Bar.OnBoard; infer_instance

/-- Membership of a board cell in a bar. -/
def Bar.Mem (b : Bar) (v : V n) : Prop := (v.1.val, v.2.val) ∈ Bar.cells k b

instance (b : Bar) (v : V n) : Decidable (Bar.Mem n k b v) := by unfold Bar.Mem; infer_instance

/-- **The counted property.** Every one-cell `v` lies in a `k`-bar `b` on the board all of whose
cells are ones, and no one-cell outside `b` is adjacent to a cell of `b` (so the connected
component of the ones containing `v` is exactly `b`). -/
def IsBarArray (f : V n → Bool) : Prop :=
  ∀ v : V n, f v = true →
    ∃ b : Bar, Bar.OnBoard n k b ∧ Bar.Mem n k b v ∧
      (∀ u : V n, Bar.Mem n k b u → f u = true) ∧
      (∀ u w : V n, Bar.Mem n k b u → Adj n u w → f w = true → Bar.Mem n k b w)

/-- Bars on the board, as a finite type (only `r, c < n` matter for `OnBoard`). -/
def boardBars : Finset Bar :=
  (Finset.univ : Finset (Bool × Fin n × Fin n)).image fun x => ⟨x.1, x.2.1.val, x.2.2.val⟩

theorem mem_boardBars_of_onBoard {b : Bar} (h : Bar.OnBoard n k b) : b ∈ boardBars n := by
  unfold boardBars
  rw [Finset.mem_image]
  exact ⟨(b.horizontal, ⟨b.r, h.1⟩, ⟨b.c, h.2.1⟩), Finset.mem_univ _, rfl⟩

/-- Decidable version: the existential ranges over `boardBars`. -/
def IsBarArrayB (f : V n → Bool) : Prop :=
  ∀ v : V n, f v = true →
    ∃ b ∈ boardBars n, Bar.OnBoard n k b ∧ Bar.Mem n k b v ∧
      (∀ u : V n, Bar.Mem n k b u → f u = true) ∧
      (∀ u w : V n, Bar.Mem n k b u → Adj n u w → f w = true → Bar.Mem n k b w)

instance (f : V n → Bool) : Decidable (IsBarArrayB n k f) := by
  unfold IsBarArrayB; infer_instance

theorem isBarArrayB_iff (f : V n → Bool) : IsBarArrayB n k f ↔ IsBarArray n k f := by
  constructor
  · intro h v hv
    obtain ⟨b, -, hb⟩ := h v hv
    exact ⟨b, hb⟩
  · intro h v hv
    obtain ⟨b, hb⟩ := h v hv
    exact ⟨b, mem_boardBars_of_onBoard n k hb.1, hb⟩

instance (f : V n → Bool) : Decidable (IsBarArray n k f) :=
  decidable_of_iff _ (isBarArrayB_iff n k f)

/-- Number of `n × n` bar arrays with bar length `k`; the OEIS sequences are
`A145789 n = barCount n 4`, `A145757 n = barCount n 3`, `A145773 n = barCount n 2`. -/
def barCount : Nat := Fintype.card {f : V n → Bool // IsBarArray n k f}

/-- **OEIS A145789**: `n × n` binary arrays whose ones form `1 × 4` or `4 × 1` bars, no two
of them edge-adjacent (diagonal contact is allowed). -/
def A145789 (n : Nat) : Nat := barCount n 4

/-- **OEIS A145757**: `n × n` binary arrays whose ones form `1 × 3` or `3 × 1` bars, no two
of them edge-adjacent (diagonal contact is allowed). -/
def A145757 (n : Nat) : Nat := barCount n 3

/-! ### The mathematical frontier specification -/

/-- Per-column frontier entry. -/
inductive Col where
  | free
  | block
  | vert (m : Nat)
  deriving DecidableEq, Repr

/-- The register describing the cell to the left of the current one. -/
inductive Left where
  | free
  | block
  | pend
  | horiz (m : Nat)
  deriving DecidableEq, Repr

/-- State of the frontier automaton: one entry per column and the left register. -/
abbrev MState := (Fin n → Col) × Left

/-- Result of placing a symbol: new entry for the current column, optional new entry for
the previous column, new left register. `none` rejects. -/
def place (a : Col) (l : Left) (s : Fin 2) : Option (Col × Option Col × Left) :=
  match s.val, a, l with
  | 0, .vert _, _ => none
  | 0, _, .horiz _ => none
  | 0, _, _ => some (.free, none, .free)
  | 1, _, .block => none
  | 1, .block, _ => none
  | 1, .vert m, .free => some (if m + 1 = k then .block else .vert (m + 1), none, .block)
  | 1, .vert _, _ => none
  | 1, .free, .free => some (.vert 1, none, .pend)
  | 1, .free, .pend => some (.block, some .block, if k = 2 then .block else .horiz 2)
  | 1, .free, .horiz m => some (.block, none, if m + 1 = k then .block else .horiz (m + 1))
  | _, _, _ => none

/-- One step of the frontier automaton at cell index `i`. -/
def mstep (i : Nat) (st : MState n) (s : Fin 2) : Option (MState n) :=
  if hc : i % n < n then
    let c : Fin n := ⟨i % n, hc⟩
    match place k (st.1 c) st.2 s with
    | none => none
    | some (e, e', l) =>
      let f := Function.update st.1 c e
      let f := match e' with
        | none => f
        | some e' => if hc0 : 0 < c.val then Function.update f ⟨c.val - 1, by omega⟩ e' else f
      if c.val + 1 = n then
        match l with
        | .horiz _ => none
        | _ => some (f, .free)
      else some (f, l)
  else none

/-- A column entry is complete (no pending vertical run). -/
def Col.done : Col → Bool
  | .free => true
  | .block => true
  | .vert _ => false

/-- The mathematical specification. -/
def mspec : Spec (MState n) (n * n) 2 where
  root := (fun _ => .free, .free)
  step := mstep n k
  final := fun st => decide (∀ j, (st.1 j).done = true)

/-! ### The packed specification

Three bits per column (`0` free, `1` block, `m + 1` for `vert m`), the left register in the
three bits above the columns (`0` free, `1` block, `2` pend, `m + 1` for `horiz m`).
Valid for `k ≤ 6` and `3 * (n + 1) ≤ 64`, i.e. `n ≤ 20`. -/

/-- Three-bit code of a column entry: `0` free, `1` block, `m + 1` for `vert m`. -/
def encCol : Col → UInt64
  | .free => 0
  | .block => 1
  | .vert m => (m + 1).toUInt64

/-- Decodes a three-bit field into a column entry (inverse of `encCol` on well-formed
entries). -/
def decCol (x : UInt64) : Col :=
  if x = 0 then .free else if x = 1 then .block else .vert (x.toNat - 1)

/-- Three-bit code of the left register: `0` free, `1` block, `2` pend, `m + 1` for
`horiz m`. -/
def encLeft : Left → UInt64
  | .free => 0
  | .block => 1
  | .pend => 2
  | .horiz m => (m + 1).toUInt64

/-- Decodes a three-bit field into a left register (inverse of `encLeft` on well-formed
registers). -/
def decLeft (x : UInt64) : Left :=
  if x = 0 then .free else if x = 1 then .block else if x = 2 then .pend else .horiz (x.toNat - 1)

/-- One step of the packed automaton. -/
def fstep (i : Nat) (s : UInt64) (a : Fin 2) : Option UInt64 :=
  let c := i % n
  let col := decCol (getField s c)
  let l := decLeft (getField s n)
  match place k col l a with
  | none => none
  | some (e, e', l') =>
    let s := setField s c (encCol e)
    let s := match e' with
      | none => s
      | some e' => if 0 < c then setField s (c - 1) (encCol e') else s
    if c + 1 = n then
      match l' with
      | .horiz _ => none
      | _ => some (setField s n 0)
    else some (setField s n (encLeft l'))

/-- All column fields are `0` or `1` (no pending vertical run). -/
def fdone (s : UInt64) : Bool :=
  (List.range n).all fun c => getField s c ≤ 1

/-- The packed specification: the frontier automaton with its state packed into a
`UInt64`. -/
def fspec : Spec UInt64 (n * n) 2 where
  root := 0
  step := fstep n k
  final := fdone n

/-! ### Proof infrastructure for `accepts_iff`

All reasoning is done on the total array `g : Nat → Nat → Bool` (false outside the
board). `vlen g r c` is the length of the run of ones ending at `(r, c)` going up,
`hlen g r c` the length of the run ending at `(r, c)` going left (both `0` on a
zero cell). The frontier after `i = n * R + C` cells is described explicitly by
`front`, and the counted property has a local characterization
`IsBarArrayLocal` (no L-shapes, no isolated ones, every horizontal run has length
`k`, every vertical run has length `k`). The proofs are in `BarArrayLocal`
(`IsBarArrayLocal ↔ IsBarArray`), `BarArrayFront` (the run reaches `front`),
`BarArrayAccept` (acceptance ↔ `IsBarArrayLocal`), `BarArrayFast` (packed
simulation), assembled in `BarArrayMain`. -/

/-- Length of the vertical run of ones ending at `(r, c)` (going up). -/
def vlen (g : Nat → Nat → Bool) : Nat → Nat → Nat
  | 0, c => if g 0 c then 1 else 0
  | r + 1, c => if g (r + 1) c then vlen g r c + 1 else 0

/-- Length of the horizontal run of ones ending at `(r, c)` (going left). -/
def hlen (g : Nat → Nat → Bool) (r : Nat) : Nat → Nat
  | 0 => if g r 0 then 1 else 0
  | c + 1 => if g r (c + 1) then hlen g r c + 1 else 0

/-- `(r, c)` is a one with a horizontal one-neighbour. -/
def IsHoriz (g : Nat → Nat → Bool) (r c : Nat) : Prop :=
  g r c = true ∧ ((0 < c ∧ g r (c - 1) = true) ∨ g r (c + 1) = true)

/-- `(r, c)` is a one with a vertical one-neighbour. -/
def IsVert (g : Nat → Nat → Bool) (r c : Nat) : Prop :=
  g r c = true ∧ ((0 < r ∧ g (r - 1) c = true) ∨ g (r + 1) c = true)

/-- Local characterization of bar arrays: every one is horizontal or vertical but not both,
the right end of a horizontal run has run length `k`, the bottom end of a vertical run has
run length `k`. -/
def IsBarArrayLocal (g : Nat → Nat → Bool) : Prop :=
  ∀ r c, g r c = true →
    (IsHoriz g r c ∨ IsVert g r c) ∧ ¬ (IsHoriz g r c ∧ IsVert g r c) ∧
    (IsHoriz g r c → g r (c + 1) = false → hlen g r c = k) ∧
    (IsVert g r c → g (r + 1) c = false → vlen g r c = k)

/-- Column entry of the frontier after `n * R + C` cells, for column `j`. -/
def colEntry (g : Nat → Nat → Bool) (R C j : Nat) : Col :=
  if j < C then
    -- last cell of column `j` is `(R, j)`; its right neighbour is processed iff `j + 1 < C`
    if g R j = false then .free
    else if (0 < j ∧ g R (j - 1) = true) ∨ (j + 1 < C ∧ g R (j + 1) = true) then .block
    else if vlen g R j = k then .block else .vert (vlen g R j)
  else if 0 < R then
    if g (R - 1) j = false then .free
    else if (0 < j ∧ g (R - 1) (j - 1) = true) ∨ g (R - 1) (j + 1) = true then .block
    else if vlen g (R - 1) j = k then .block else .vert (vlen g (R - 1) j)
  else .free

/-- Left register of the frontier after `n * R + C` cells (about the cell `(R, C - 1)`). -/
def leftReg (g : Nat → Nat → Bool) (R C : Nat) : Left :=
  if C = 0 then .free
  else if g R (C - 1) = false then .free
  else if 0 < R ∧ g (R - 1) (C - 1) = true then .block
  else if hlen g R (C - 1) = 1 then .pend
  else if hlen g R (C - 1) = k then .block
  else .horiz (hlen g R (C - 1))

/-- The frontier after reading the first `i` cells. -/
def front (g : Nat → Nat → Bool) (i : Nat) : MState n :=
  (fun j => colEntry k g (i / n) (i % n) j.val, leftReg k g (i / n) (i % n))

/-- Fresh spec object per worker of the parallel engine (see `Spec.advancePar`). -/
@[noinline] def mkSpec (n k : Nat) (_j : Nat) : Spec UInt64 (n * n) 2 := fspec n k

end Tally.BarArray

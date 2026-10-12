import Tally.Spec
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The `n × n` grid as a word layer

Shared infrastructure for the grid families. The cells of the `n × n` board
`V n = Fin n × Fin n` are read in row-major order, cell `(r, c)` at index
`c + n * r` (`cell`, inverse `cellInv`). A word of length `n * n` over `{0, 1}`
is the same thing as a vertex set (`wordEquivSet`) or a Boolean array
(`wordEquivArray`). For local reasoning an array is extended to the total
function `grid n f : Nat → Nat → Bool`, `false` outside the board. `Adj` is
the grid adjacency, equal to that of `pathGraph n □ pathGraph n`.
-/

namespace Tally.Grid

open Tally

variable (n : Nat)

/-! ### Vertices and adjacency -/

/-- Vertices of the `n × n` grid: (row, column). -/
abbrev V := Fin n × Fin n

/-- Grid adjacency: same row and adjacent columns, or same column and adjacent rows. -/
def Adj (u v : V n) : Prop :=
  (u.1 = v.1 ∧ (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)) ∨
  (u.2 = v.2 ∧ (u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val))

instance : DecidableRel (Adj n) := fun _ _ => by unfold Adj; infer_instance

/-- `Adj` is the adjacency of the grid graph `pathGraph n □ pathGraph n`. -/
theorem adj_iff_boxProd (u v : V n) :
    Adj n u v ↔ (SimpleGraph.pathGraph n □ SimpleGraph.pathGraph n).Adj u v := by
  rw [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, SimpleGraph.pathGraph_adj]
  unfold Adj
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩

theorem adj_symm {u v : V n} (h : Adj n u v) : Adj n v u := by
  unfold Adj at *
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h1.symm, h2.symm⟩

/-! ### Row-major cell order -/

/-- Row-major cell index: `(r, c) ↦ c + n * r`. -/
abbrev cell : V n ≃ Fin (n * n) := finProdFinEquiv

theorem cell_val (v : V n) : (cell n v).val = v.2.val + n * v.1.val :=
  finProdFinEquiv_apply_val v

/-- An earlier neighbour of `v` is the cell above it or the cell to its left. -/
theorem adj_of_lt (u v : V n) (hadj : Adj n u v) (hlt : (cell n u).val < (cell n v).val) :
    (u.1.val + 1 = v.1.val ∧ u.2 = v.2) ∨ (u.1 = v.1 ∧ u.2.val + 1 = v.2.val) := by
  rw [cell_val, cell_val] at hlt
  rcases hadj with ⟨hr, hc⟩ | ⟨hc, hr⟩
  · rw [hr] at hlt
    generalize n * v.1.val = m at hlt
    rcases hc with hc | hc
    · exact Or.inr ⟨hr, hc⟩
    · omega
  · rw [hc] at hlt
    rcases hr with hr | hr
    · exact Or.inl ⟨hr, hc⟩
    · rw [← hr, Nat.mul_succ] at hlt
      generalize n * v.1.val = m at hlt
      omega

/-- Advancing one cell: either the column increases or a new row starts. -/
theorem succ_div_mod (hn : 0 < n) (i : Nat) :
    (i % n + 1 < n ∧ (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1) ∨
    (i % n + 1 = n ∧ (i + 1) / n = i / n + 1 ∧ (i + 1) % n = 0) := by
  have hdm := Nat.div_add_mod i n
  have hlt := Nat.mod_lt i hn
  by_cases h : i % n + 1 < n
  · left
    refine ⟨h, (Nat.div_mod_unique hn).mpr ⟨?_, h⟩⟩
    omega
  · right
    have he : i % n + 1 = n := by omega
    refine ⟨he, (Nat.div_mod_unique hn).mpr ⟨?_, hn⟩⟩
    rw [Nat.mul_succ]
    omega

/-- The vertex with cell index `i`. -/
def cellInv (i : Nat) (hi : i < n * n) : V n := (cell n).symm ⟨i, hi⟩

theorem cellInv_fst (i : Nat) (hi : i < n * n) : (cellInv n i hi).1.val = i / n := by
  simp [cellInv, finProdFinEquiv_symm_apply, Fin.coe_divNat]

theorem cellInv_snd (i : Nat) (hi : i < n * n) : (cellInv n i hi).2.val = i % n := by
  simp [cellInv, finProdFinEquiv_symm_apply, Fin.coe_modNat]

theorem cell_cellInv (i : Nat) (hi : i < n * n) : cell n (cellInv n i hi) = ⟨i, hi⟩ :=
  (cell n).apply_symm_apply _

theorem eq_cellInv_of_cell_eq {u : V n} {i : Nat} (hi : i < n * n) (h : (cell n u).val = i) :
    u = cellInv n i hi := by
  unfold cellInv
  rw [Equiv.eq_symm_apply]
  exact Fin.ext h

theorem div_lt_of_lt_mul {i : Nat} (hn : 0 < n) (hi : i < n * n) : i / n < n :=
  (Nat.div_lt_iff_lt_mul hn).mpr hi

/-! ### Words as vertex sets and as arrays -/

/-- The vertex set selected by a word: the cells reading symbol `1`. -/
def toSet (w : Word (n * n) 2) : Finset (V n) :=
  Finset.univ.filter fun v => w (cell n v) = 1

/-- The word selecting a given vertex set. -/
def ofSet (s : Finset (V n)) : Word (n * n) 2 :=
  fun i => if (cell n).symm i ∈ s then 1 else 0

/-- Words of length `n * n` over `{0, 1}` correspond to vertex sets. -/
def wordEquivSet : Word (n * n) 2 ≃ Finset (V n) where
  toFun := toSet n
  invFun := ofSet n
  left_inv := by
    intro w
    funext i
    simp only [toSet, ofSet, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
    split
    · exact (by assumption : w i = 1).symm
    · have h : w i ≠ 1 := by assumption
      have h' : (w i).val ≠ 1 := fun e => h (Fin.ext e)
      have := (w i).isLt
      exact Fin.ext (by simp only [Fin.val_zero]; omega)
  right_inv := by
    intro s
    ext v
    simp [toSet, ofSet]

/-- The array read by a word (symbol `1` = one). -/
def toArray (w : Word (n * n) 2) : V n → Bool := fun v => w (cell n v) = 1

/-- Words of length `n * n` over `{0, 1}` correspond to arrays. -/
def wordEquivArray : Word (n * n) 2 ≃ (V n → Bool) where
  toFun := toArray n
  invFun := fun f i => if f ((cell n).symm i) then 1 else 0
  left_inv := by
    intro w
    funext i
    simp only [toArray, Equiv.apply_symm_apply]
    by_cases h : w i = 1
    · simp [h]
    · have h' : (w i).val ≠ 1 := fun e => h (Fin.ext e)
      have := (w i).isLt
      have h0 : w i = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      simp [h0]
  right_inv := by
    intro f
    funext v
    simp [toArray]

/-! ### Selection by coordinates -/

/-- Selection by coordinates; `false` outside the grid. -/
def selAt (w : Word (n * n) 2) (r c : Nat) : Bool :=
  if h : r < n ∧ c < n then decide (w (cell n (⟨r, h.1⟩, ⟨c, h.2⟩)) = 1) else false

/-- `selAt` at a vertex's coordinates is selection of that vertex. -/
theorem selAt_eq (w : Word (n * n) 2) (v : V n) :
    selAt n w v.1.val v.2.val = decide (w (cell n v) = 1) := by
  unfold selAt
  rw [dif_pos ⟨v.1.isLt, v.2.isLt⟩]

/-- The array as a total function on coordinates (`false` outside the board). -/
def grid (f : V n → Bool) (r c : Nat) : Bool :=
  if h : r < n ∧ c < n then f (⟨r, h.1⟩, ⟨c, h.2⟩) else false

theorem grid_off (f : V n → Bool) (r : Nat) : grid n f r n = false := by
  simp [grid]

section Implicit

variable {n}

theorem grid_lt {f : V n → Bool} {r c : Nat} (h : grid n f r c = true) : r < n ∧ c < n := by
  unfold grid at h
  split_ifs at h with h'
  · exact h'

theorem grid_mk (f : V n → Bool) {r c : Nat} (hr : r < n) (hc : c < n) :
    grid n f r c = f (⟨r, hr⟩, ⟨c, hc⟩) := by
  simp [grid, hr, hc]

theorem grid_val (f : V n → Bool) (v : V n) : grid n f v.1.val v.2.val = f v :=
  grid_mk f v.1.isLt v.2.isLt

end Implicit

/-- The current cell `i` of a word, read through `grid`. -/
theorem grid_cur (hn : 0 < n) (w : Word (n * n) 2) (i : Nat) (hi : i < n * n) :
    (w ⟨i, hi⟩).val = 1 ↔ grid n (toArray n w) (i / n) (i % n) = true := by
  unfold grid toArray
  rw [dif_pos ⟨div_lt_of_lt_mul n hn hi, Nat.mod_lt i hn⟩]
  have hc : cell n (⟨i / n, div_lt_of_lt_mul n hn hi⟩, ⟨i % n, Nat.mod_lt i hn⟩) = ⟨i, hi⟩ := by
    apply Fin.ext
    rw [cell_val]
    simp only
    have := Nat.div_add_mod i n
    omega
  rw [hc]
  simp only [decide_eq_true_eq]
  constructor
  · intro h; exact Fin.ext h
  · intro h; rw [h]; rfl

/-- The symbol of a cell value. -/
def sym (b : Bool) : Fin 2 := if b then 1 else 0

variable {n} in
/-- A word reads, at cell `i`, the symbol of its array at that cell. -/
theorem word_eq_sym (w : Word (n * n) 2) (i : Nat) (hi : i < n * n) :
    w ⟨i, hi⟩ = sym (grid n (toArray n w) (i / n) (i % n)) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hcell : cell n (⟨i / n, div_lt_of_lt_mul n hn hi⟩, ⟨i % n, Nat.mod_lt i hn⟩) = ⟨i, hi⟩ := by
    apply Fin.ext
    rw [cell_val]
    exact Nat.mod_add_div i n
  unfold grid toArray sym
  rw [dif_pos ⟨div_lt_of_lt_mul n hn hi, Nat.mod_lt i hn⟩, hcell]
  by_cases h : w ⟨i, hi⟩ = 1
  · simp [h]
  · have h' : (w ⟨i, hi⟩).val ≠ 1 := fun e => h (Fin.ext e)
    have := (w ⟨i, hi⟩).isLt
    have h0 : w ⟨i, hi⟩ = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    simp [h0]

end Tally.Grid

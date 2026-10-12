import Tally.Grid

/-!
# Independent sets of the `n × n` grid graph (OEIS A006506)

The OEIS-facing definition is `A006506 n`, the number of independent vertex
sets of the `n × n` grid graph, stated directly on `Finset (Fin n × Fin n)`
with the explicit grid adjacency `Tally.Grid.Adj` (shown equal to Mathlib's
`pathGraph n □ pathGraph n`).

The counting goes through two specifications:

* `mspec n`, the mathematical frontier specification with state
  `Fin n → Bool`: cells are read in row-major order, the state remembers for
  each column the most recently read cell of that column, and a cell may be
  selected only if its upper and left neighbours are not.
* `fspec n`, the same automaton with the frontier packed into a `UInt64`
  bitmask (valid for `n ≤ 64`), which is what the engine runs.

Main results here: `accepts_iff` (a word is accepted by `mspec n` iff it
selects an independent set) and `A006506_eq_card` (hence `A006506 n` is the
number of accepted words of `mspec n`). The bitmask layer, `fspec_isSim`
(for `n ≤ 64` the bitmask spec simulates `mspec n`, see `Spec.IsSim`) and the
final `A006506_eq_count : A006506 n = (fspec n).count`, is in `GridIndepFast`.
-/

namespace Tally.GridIndep

open Tally Tally.Grid

variable (n : Nat)

/-! ### The combinatorial objects -/

/-- A vertex set is independent iff it contains no two adjacent vertices. -/
def IsIndep (s : Finset (V n)) : Prop := ∀ u ∈ s, ∀ v ∈ s, ¬ Adj n u v

instance : DecidablePred (IsIndep n) := fun _ => by unfold IsIndep; infer_instance

/-- **OEIS A006506**: the number of independent vertex sets of the `n × n` grid graph. -/
def A006506 (n : Nat) : Nat := Fintype.card {s : Finset (V n) // IsIndep n s}

/-! ### The mathematical frontier specification -/

/-- Frontier state: for each column, whether its most recently read cell is selected. -/
abbrev MState := Fin n → Bool

/-- One step of the frontier automaton at cell index `i` (row `i / n`, column `i % n`). -/
def mstep (i : Nat) (s : MState n) (a : Fin 2) : Option (MState n) :=
  if hc : i % n < n then
    let c : Fin n := ⟨i % n, hc⟩
    let above := s c
    let left := if hc0 : 0 < c.val then s ⟨c.val - 1, by omega⟩ else false
    if a.val = 1 then
      if above || left then none else some (Function.update s c true)
    else some (Function.update s c false)
  else none

/-- The mathematical specification: `n * n` cells in row-major order, symbols `0`/`1`. -/
def mspec : Spec (MState n) (n * n) 2 where
  root := fun _ => false
  step := mstep n
  final := fun _ => true

/-! #### Proof infrastructure for `accepts_iff`

Cells are read in the order of their index `cell n v = v.2 + n * v.1`. The run is
described by the frontier `front w i` (`isFront_front`), so the generic
`Spec.accepts_iff_front` applies. The step at cell `i` rejects iff the cell is
selected and its upper or left neighbour is (`stepOK_iff`), and all cells pass iff
no two selected cells are adjacent (`IndepUpTo`, `indepUpTo_iff`). -/

/-- The frontier after reading the first `i` cells (row `i / n`, column `i % n`):
column `j` holds cell `(i / n, j)` if `j < i % n`, else cell `(i / n - 1, j)`. -/
def front (w : Word (n * n) 2) (i : Nat) : MState n := fun j =>
  if j.val < i % n then selAt n w (i / n) j.val
  else if 0 < i / n then selAt n w (i / n - 1) j.val else false

/-- No two selected cells among the first `i` are adjacent. -/
def IndepUpTo (w : Word (n * n) 2) (i : Nat) : Prop :=
  ∀ u v : V n, (cell n u).val < i → (cell n v).val < i →
    w (cell n u) = 1 → w (cell n v) = 1 → ¬ Adj n u v

instance (w : Word (n * n) 2) (i : Nat) : Decidable (IndepUpTo n w i) := by
  unfold IndepUpTo; infer_instance

theorem indepUpTo_mono (w : Word (n * n) 2) {i j : Nat} (hij : i ≤ j) (h : IndepUpTo n w j) :
    IndepUpTo n w i :=
  fun u v hu hv su sv => h u v (by omega) (by omega) su sv

theorem indepUpTo_zero (w : Word (n * n) 2) : IndepUpTo n w 0 :=
  fun _ _ hu => absurd hu (Nat.not_lt_zero _)

/-- Whether the cell above cell `i` is selected. -/
def aboveSel (w : Word (n * n) 2) (i : Nat) : Bool :=
  if 0 < i / n then selAt n w (i / n - 1) (i % n) else false

/-- Whether the cell left of cell `i` is selected. -/
def leftSel (w : Word (n * n) 2) (i : Nat) : Bool :=
  if 0 < i % n then selAt n w (i / n) (i % n - 1) else false

theorem front_above (w : Word (n * n) 2) (i : Nat) (hc : i % n < n) :
    front n w i ⟨i % n, hc⟩ = aboveSel n w i := by
  simp [front, aboveSel]

theorem front_left (w : Word (n * n) 2) (i : Nat) (hc : 0 < i % n) (hc' : i % n - 1 < n) :
    front n w i ⟨i % n - 1, hc'⟩ = leftSel n w i := by
  simp [front, leftSel, hc, Nat.sub_lt hc Nat.one_pos]

theorem front_left' (w : Word (n * n) 2) (i : Nat) (hmod : i % n < n) :
    (if h : 0 < i % n then front n w i ⟨i % n - 1, by omega⟩ else false) = leftSel n w i := by
  unfold leftSel
  split
  · rename_i hc
    simp [front, Nat.sub_lt hc Nat.one_pos]
  · rfl

/-- Reading cell `i` updates column `i % n` of the frontier. -/
theorem front_succ (hn : 0 < n) (w : Word (n * n) 2) (i : Nat) :
    front n w (i + 1) =
      Function.update (front n w i) ⟨i % n, Nat.mod_lt i hn⟩ (selAt n w (i / n) (i % n)) := by
  funext j
  rw [Function.update_apply]
  rcases succ_div_mod n hn i with ⟨-, hd, hm⟩ | ⟨heq, hd, hm⟩
  · simp only [front, hd, hm]
    by_cases hj : j = ⟨i % n, Nat.mod_lt i hn⟩
    · subst hj
      simp
    · have hj' : j.val ≠ i % n := fun h => hj (Fin.ext h)
      simp only [hj, if_false]
      by_cases h1 : j.val < i % n
      · simp [h1, show j.val < i % n + 1 by omega]
      · simp [h1, show ¬ j.val < i % n + 1 by omega]
  · simp only [front, hd, hm, Nat.not_lt_zero, if_false, Nat.zero_lt_succ, if_true,
      Nat.add_sub_cancel]
    by_cases hj : j = ⟨i % n, Nat.mod_lt i hn⟩
    · subst hj
      simp
    · have hj' : j.val ≠ i % n := fun h => hj (Fin.ext h)
      have hjl : j.val < i % n := by have := j.isLt; omega
      simp [hj, hjl]

/-- Adding cell `i` keeps independence iff, when selected, its upper and left neighbours are not. -/
theorem indepUpTo_succ (hn : 0 < n) (w : Word (n * n) 2) (i : Nat) (hi : i < n * n) :
    IndepUpTo n w (i + 1) ↔
      IndepUpTo n w i ∧ (w ⟨i, hi⟩ = 1 → aboveSel n w i = false ∧ leftSel n w i = false) := by
  have hdm := Nat.div_add_mod i n
  have hmod := Nat.mod_lt i hn
  have hdiv := div_lt_of_lt_mul n hn hi
  constructor
  · intro h
    refine ⟨indepUpTo_mono n w (Nat.le_succ i) h, fun hsel => ⟨?_, ?_⟩⟩
    · unfold aboveSel
      split
      · rename_i hpos
        unfold selAt
        rw [dif_pos ⟨by omega, hmod⟩]
        simp only [decide_eq_false_iff_not]
        intro hu
        -- the cell above is adjacent to cell `i` and comes earlier
        have hv := cell_cellInv n i hi
        refine h (⟨⟨i / n - 1, by omega⟩, ⟨i % n, hmod⟩⟩) (cellInv n i hi) ?_ ?_ hu ?_ ?_
        · rw [cell_val]
          simp only
          have : n * (i / n - 1) + n = n * (i / n) := by
            rw [← Nat.mul_succ]; congr 1; omega
          omega
        · rw [hv]; exact Nat.lt_succ_self i
        · rw [hv]; exact hsel
        · unfold Adj
          right
          refine ⟨Fin.ext ?_, Or.inl ?_⟩
          · simp [cellInv_snd]
          · simp [cellInv_fst]; omega
      · rfl
    · unfold leftSel
      split
      · rename_i hpos
        unfold selAt
        rw [dif_pos ⟨hdiv, by omega⟩]
        simp only [decide_eq_false_iff_not]
        intro hu
        have hv := cell_cellInv n i hi
        refine h (⟨⟨i / n, hdiv⟩, ⟨i % n - 1, by omega⟩⟩) (cellInv n i hi) ?_ ?_ hu ?_ ?_
        · rw [cell_val]
          simp only
          omega
        · rw [hv]; exact Nat.lt_succ_self i
        · rw [hv]; exact hsel
        · unfold Adj
          left
          refine ⟨Fin.ext ?_, Or.inl ?_⟩
          · simp [cellInv_fst]
          · simp [cellInv_snd]; omega
      · rfl
  · rintro ⟨h, himp⟩ u v hu hv su sv hadj
    by_cases hu' : (cell n u).val < i
    · by_cases hv' : (cell n v).val < i
      · exact h u v hu' hv' su sv hadj
      · -- v is cell i, u is earlier
        have hvi : (cell n v).val = i := by omega
        have hveq := eq_cellInv_of_cell_eq n hi hvi
        have hsel : w ⟨i, hi⟩ = 1 := by rw [← cell_cellInv n i hi, ← hveq]; exact sv
        obtain ⟨ha, hl⟩ := himp hsel
        rcases adj_of_lt n u v hadj (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- u above v
          unfold aboveSel at ha
          rw [if_pos (by rw [← cellInv_fst n i hi, ← hveq]; omega)] at ha
          have hcoord : selAt n w (i / n - 1) (i % n) = selAt n w u.1.val u.2.val := by
            congr 1
            · rw [← cellInv_fst n i hi, ← hveq]; omega
            · rw [← cellInv_snd n i hi, ← hveq, h2]
          rw [hcoord, selAt_eq] at ha
          simp [su] at ha
        · -- u left of v
          unfold leftSel at hl
          rw [if_pos (by rw [← cellInv_snd n i hi, ← hveq]; omega)] at hl
          have hcoord : selAt n w (i / n) (i % n - 1) = selAt n w u.1.val u.2.val := by
            congr 1
            · rw [← cellInv_fst n i hi, ← hveq, h1]
            · rw [← cellInv_snd n i hi, ← hveq]; omega
          rw [hcoord, selAt_eq] at hl
          simp [su] at hl
    · -- u is cell i, v is earlier (symmetric)
      have hui : (cell n u).val = i := by omega
      have hv' : (cell n v).val < i := by
        rcases Nat.lt_or_ge (cell n v).val i with h' | h'
        · exact h'
        · exfalso
          have : (cell n v).val = i := by omega
          have huv : u = v := (cell n).injective (Fin.ext (hui.trans this.symm))
          subst huv
          unfold Adj at hadj
          omega
      have hueq := eq_cellInv_of_cell_eq n hi hui
      have hsel : w ⟨i, hi⟩ = 1 := by rw [← cell_cellInv n i hi, ← hueq]; exact su
      obtain ⟨ha, hl⟩ := himp hsel
      rcases adj_of_lt n v u (adj_symm n hadj) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · unfold aboveSel at ha
        rw [if_pos (by rw [← cellInv_fst n i hi, ← hueq]; omega)] at ha
        have hcoord : selAt n w (i / n - 1) (i % n) = selAt n w v.1.val v.2.val := by
          congr 1
          · rw [← cellInv_fst n i hi, ← hueq]; omega
          · rw [← cellInv_snd n i hi, ← hueq, h2]
        rw [hcoord, selAt_eq] at ha
        simp [sv] at ha
      · unfold leftSel at hl
        rw [if_pos (by rw [← cellInv_snd n i hi, ← hueq]; omega)] at hl
        have hcoord : selAt n w (i / n) (i % n - 1) = selAt n w v.1.val v.2.val := by
          congr 1
          · rw [← cellInv_fst n i hi, ← hueq, h1]
          · rw [← cellInv_snd n i hi, ← hueq]; omega
        rw [hcoord, selAt_eq] at hl
        simp [sv] at hl

theorem front_zero (w : Word (n * n) 2) : front n w 0 = (mspec n).root := by
  funext j
  simp [front, mspec]

theorem selAt_cell (w : Word (n * n) 2) (i : Nat) (hi : i < n * n) :
    selAt n w (i / n) (i % n) = decide (w ⟨i, hi⟩ = 1) := by
  have := selAt_eq n w (cellInv n i hi)
  rwa [cellInv_fst, cellInv_snd, cell_cellInv] at this

/-- One step from the described frontier: reject iff cell `i` is selected and its upper
or left neighbour is, else move to the next frontier. -/
theorem mstep_front (hn : 0 < n) (w : Word (n * n) 2) (i : Nat) (hi : i < n * n) :
    mstep n i (front n w i) (w ⟨i, hi⟩) =
      if w ⟨i, hi⟩ = 1 ∧ (aboveSel n w i || leftSel n w i) = true then none
      else some (front n w (i + 1)) := by
  unfold mstep
  rw [dif_pos (Nat.mod_lt i hn)]
  simp only [front_above]
  rw [front_left' n w i (Nat.mod_lt i hn), front_succ n hn w i, selAt_cell n w i hi]
  by_cases hsel : w ⟨i, hi⟩ = 1
  · have hv : (w ⟨i, hi⟩).val = 1 := by rw [hsel]; rfl
    rw [if_pos hv]
    by_cases hr : (aboveSel n w i || leftSel n w i) = true <;> simp [hsel, hr]
  · have hv : ¬ (w ⟨i, hi⟩).val = 1 := fun h => hsel (Fin.ext h)
    rw [if_neg hv]
    simp [hsel]

/-- `front` describes the run of the automaton on `w`. -/
theorem isFront_front (hn : 0 < n) (w : Word (n * n) 2) : (mspec n).IsFront w (front n w) where
  zero := front_zero n w
  step i hi s' h := by
    change mstep n i (front n w i) (w ⟨i, hi⟩) = some s' at h
    rw [mstep_front n hn w i hi] at h
    split at h
    · exact absurd h (by simp)
    · exact (Option.some.inj h).symm

/-- The step at cell `i` does not reject iff, when selected, its upper and left neighbours
are not. -/
theorem stepOK_iff (hn : 0 < n) (w : Word (n * n) 2) (i : Nat) (hi : i < n * n) :
    (mspec n).StepOK w (front n w) i hi ↔
      (w ⟨i, hi⟩ = 1 → aboveSel n w i = false ∧ leftSel n w i = false) := by
  unfold Spec.StepOK
  change mstep n i (front n w i) (w ⟨i, hi⟩) ≠ none ↔ _
  rw [mstep_front n hn w i hi]
  by_cases hsel : w ⟨i, hi⟩ = 1 <;> by_cases ha : aboveSel n w i <;>
    by_cases hl : leftSel n w i <;> simp [hsel, ha, hl]

/-- Independence of the first `i` cells is the per-cell condition at every earlier cell. -/
theorem indepUpTo_iff (hn : 0 < n) (w : Word (n * n) 2) (i : Nat) (hi : i ≤ n * n) :
    IndepUpTo n w i ↔ ∀ j (hj : j < n * n), j < i →
      (w ⟨j, hj⟩ = 1 → aboveSel n w j = false ∧ leftSel n w j = false) := by
  induction i with
  | zero => exact ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ => indepUpTo_zero n w⟩
  | succ i ih =>
    have hi' : i < n * n := hi
    rw [indepUpTo_succ n hn w i hi', ih hi'.le]
    constructor
    · rintro ⟨h, hc⟩ j hj hji
      rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hlt | rfl
      · exact h j hj hlt
      · exact hc
    · intro h
      exact ⟨fun j hj hji => h j hj (Nat.lt_succ_of_lt hji), h i hi' (Nat.lt_succ_self i)⟩

theorem indepUpTo_iff_isIndep (w : Word (n * n) 2) :
    IndepUpTo n w (n * n) ↔ IsIndep n (toSet n w) := by
  constructor
  · intro hind u hu v hv hadj
    simp only [toSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact hind u v (cell n u).isLt (cell n v).isLt hu hv hadj
  · intro hind u v _ _ su sv hadj
    exact hind u (by simp [toSet, su]) v (by simp [toSet, sv]) hadj

/-- A word is accepted by the frontier automaton iff it selects an independent set. -/
theorem accepts_iff (w : Word (n * n) 2) : (mspec n).Accepts w ↔ IsIndep n (toSet n w) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    constructor
    · intro _ u
      exact (Fin.elim0 u.1)
    · intro _
      show (mspec 0).acceptsB w = true
      simp [Spec.acceptsB, Spec.acceptsFrom, List.ofFn_zero, mspec]
  · rw [(mspec n).accepts_iff_front (isFront_front n hn w),
      and_iff_left (show (mspec n).final (front n w (n * n)) = true from rfl),
      ← indepUpTo_iff_isIndep, indepUpTo_iff n hn w (n * n) le_rfl]
    exact ⟨fun h j hj _ => (stepOK_iff n hn w j hj).mp (h j hj),
      fun h j hj => (stepOK_iff n hn w j hj).mpr (h j hj hj)⟩

/-- Accepted words of `mspec n` correspond to independent sets. -/
def acceptedEquiv : (mspec n).Accepted ≃ {s : Finset (V n) // IsIndep n s} :=
  Equiv.subtypeEquiv (wordEquivSet n) (accepts_iff n)

theorem A006506_eq_card : A006506 n = Fintype.card (mspec n).Accepted :=
  (Fintype.card_congr (acceptedEquiv n)).symm

/-! ### The bitmask specification -/

/-- One step of the bitmask automaton; bit `c` of the state is column `c` of the frontier. -/
def fstep (i : Nat) (s : UInt64) (a : Fin 2) : Option UInt64 :=
  let c := i % n
  let bit : UInt64 := (1 : UInt64) <<< c.toUInt64
  let above := (s &&& bit) != 0
  let left := c != 0 && (s &&& (bit >>> 1)) != 0
  if a.val = 1 then
    if above || left then none else some (s ||| bit)
  else some (s &&& ~~~bit)

/-- The bitmask specification run by the engine (correct for `n ≤ 64`). -/
def fspec : Spec UInt64 (n * n) 2 where
  root := 0
  step := fstep n
  final := fun _ => true

/-- Simulation relation: the low `n` bits of `s` are the frontier `t`. -/
def Rel (s : UInt64) (t : MState n) : Prop := ∀ j : Fin n, s.toBitVec.getLsbD j.val = t j

end Tally.GridIndep

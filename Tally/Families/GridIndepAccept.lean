import Tally.Families.GridIndep

/-!
# Acceptance theorem for the grid / rhombus independent-set family

`accepts_iff`: a word is accepted by `mspec n d` iff it selects an independent set
(`IsIndep n d`), hence `A006506_eq_card` (`d = false`) and `A066864_eq_card` (`d = true`).

Cells are read in the order of their index `cell n v = v.2 + n * v.1`. The run is
described by the frontier `front w i` (`isFront_front`), so the generic
`Spec.accepts_iff_front` applies. An earlier neighbour of a cell is the cell above, the
cell to the left, or for `d = true` the cell above-right (`adjD_of_lt`). The step at cell
`i` rejects iff the cell is selected and one of these is (`blocked`, `stepOK_iff`), and
all cells pass iff no two selected cells are adjacent (`IndepUpTo`, `indepUpTo_iff`).
-/

namespace Tally.GridIndep

open Tally Tally.Grid

variable (n : Nat) (d : Bool)

/-! #### Adjacency facts -/

theorem adjD_symm {u v : V n} (h : AdjD n d u v) : AdjD n d v u := by
  rcases h with h | ⟨hd, h⟩
  · exact Or.inl (adj_symm n h)
  · refine Or.inr ⟨hd, ?_⟩
    unfold AntiDiag at *
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem adjD_irrefl (u : V n) : ¬ AdjD n d u u := by
  unfold AdjD Adj AntiDiag
  omega

/-- An earlier neighbour of `v` is the cell above it, the cell to its left, or (for
`d = true`) the cell above-right. -/
theorem adjD_of_lt (u v : V n) (hadj : AdjD n d u v) (hlt : (cell n u).val < (cell n v).val) :
    (u.1.val + 1 = v.1.val ∧ u.2 = v.2) ∨ (u.1 = v.1 ∧ u.2.val + 1 = v.2.val) ∨
      (d = true ∧ u.1.val + 1 = v.1.val ∧ v.2.val + 1 = u.2.val) := by
  rcases hadj with h | ⟨hd, h⟩
  · rcases adj_of_lt n u v h hlt with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases h with h | ⟨h1, h2⟩
    · exact Or.inr (Or.inr ⟨hd, h⟩)
    · exfalso
      rw [cell_val, cell_val, ← h1, Nat.mul_succ] at hlt
      have := u.2.isLt
      generalize n * v.1.val = m at hlt
      omega

/-! #### Proof infrastructure for `accepts_iff` -/

theorem indepUpTo_mono (w : Word (n * n) 2) {i j : Nat} (hij : i ≤ j) (h : IndepUpTo n d w j) :
    IndepUpTo n d w i :=
  fun u v hu hv su sv => h u v (by omega) (by omega) su sv

theorem indepUpTo_zero (w : Word (n * n) 2) : IndepUpTo n d w 0 :=
  fun _ _ hu => absurd hu (Nat.not_lt_zero _)

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

theorem front_aboveRight (w : Word (n * n) 2) (i : Nat) (hc1 : i % n + 1 < n) :
    front n w i ⟨i % n + 1, hc1⟩ = aboveRightSel n w i := by
  simp [front, aboveRightSel, hc1]

theorem front_aboveRight' (w : Word (n * n) 2) (i : Nat) :
    (if hc1 : i % n + 1 < n then front n w i ⟨i % n + 1, hc1⟩ else false) =
      aboveRightSel n w i := by
  split
  · rename_i hc1
    exact front_aboveRight n w i hc1
  · rename_i hc1
    simp [aboveRightSel, hc1]

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

/-- An earlier cell adjacent to a selected cell `i` is not selected, if the first `i + 1`
cells are independent. -/
theorem selAt_false_of_adj (w : Word (n * n) 2) (i : Nat) (hi : i < n * n)
    (h : IndepUpTo n d w (i + 1)) (hsel : w ⟨i, hi⟩ = 1) (u : V n) (hu : (cell n u).val < i)
    (hadj : AdjD n d u (cellInv n i hi)) : selAt n w u.1.val u.2.val = false := by
  rw [selAt_eq, decide_eq_false_iff_not]
  intro su
  have hv := cell_cellInv n i hi
  exact h u (cellInv n i hi) (by omega) (by rw [hv]; exact Nat.lt_succ_self i) su
    (by rw [hv]; exact hsel) hadj

/-- A selected cell `i` that is not `blocked` has no selected adjacent earlier cell. -/
theorem not_adj_cur (w : Word (n * n) 2) (i : Nat) (hi : i < n * n)
    (himp : w ⟨i, hi⟩ = 1 → blocked n d w i = false) (u v : V n) (hu : (cell n u).val < i)
    (hv : (cell n v).val = i) (su : w (cell n u) = 1) (sv : w (cell n v) = 1)
    (hadj : AdjD n d u v) : False := by
  have hveq := eq_cellInv_of_cell_eq n hi hv
  have hsel : w ⟨i, hi⟩ = 1 := by rw [← cell_cellInv n i hi, ← hveq]; exact sv
  have hb := himp hsel
  rw [blocked, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hb
  obtain ⟨⟨ha, hl⟩, har⟩ := hb
  have hv1 : v.1.val = i / n := by rw [hveq, cellInv_fst]
  have hv2 : v.2.val = i % n := by rw [hveq, cellInv_snd]
  have hsu : selAt n w u.1.val u.2.val = true := by rw [selAt_eq]; simp [su]
  rcases adjD_of_lt n d u v hadj (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hd, h1, h2⟩
  · -- u above v
    have h2' := congrArg Fin.val h2
    unfold aboveSel at ha
    rw [if_pos (by omega)] at ha
    have hcoord : selAt n w (i / n - 1) (i % n) = selAt n w u.1.val u.2.val := by
      congr 1 <;> omega
    rw [hcoord, hsu] at ha
    exact Bool.noConfusion ha
  · -- u left of v
    have h1' := congrArg Fin.val h1
    unfold leftSel at hl
    rw [if_pos (by omega)] at hl
    have hcoord : selAt n w (i / n) (i % n - 1) = selAt n w u.1.val u.2.val := by
      congr 1 <;> omega
    rw [hcoord, hsu] at hl
    exact Bool.noConfusion hl
  · -- u above-right of v (d = true)
    subst hd
    rw [Bool.true_and] at har
    unfold aboveRightSel at har
    rw [if_pos ⟨by omega, by have := u.2.isLt; omega⟩] at har
    have hcoord : selAt n w (i / n - 1) (i % n + 1) = selAt n w u.1.val u.2.val := by
      congr 1 <;> omega
    rw [hcoord, hsu] at har
    exact Bool.noConfusion har

/-- Adding cell `i` keeps independence iff, when selected, it is not `blocked`. -/
theorem indepUpTo_succ (hn : 0 < n) (w : Word (n * n) 2) (i : Nat) (hi : i < n * n) :
    IndepUpTo n d w (i + 1) ↔
      IndepUpTo n d w i ∧ (w ⟨i, hi⟩ = 1 → blocked n d w i = false) := by
  have hdm := Nat.div_add_mod i n
  have hmod := Nat.mod_lt i hn
  have hdiv := div_lt_of_lt_mul n hn hi
  have hc1 := cellInv_fst n i hi
  have hc2 := cellInv_snd n i hi
  constructor
  · intro h
    refine ⟨indepUpTo_mono n d w (Nat.le_succ i) h, fun hsel => ?_⟩
    rw [blocked, Bool.or_eq_false_iff, Bool.or_eq_false_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- the cell above
      unfold aboveSel
      split
      · rename_i hpos
        refine selAt_false_of_adj n d w i hi h hsel (⟨⟨i / n - 1, by omega⟩, ⟨i % n, hmod⟩⟩)
          ?_ (Or.inl (Or.inr ⟨Fin.ext hc2.symm, Or.inl (by simp only; omega)⟩))
        rw [cell_val]
        simp only
        have : n * (i / n - 1) + n = n * (i / n) := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega
      · rfl
    · -- the cell to the left
      unfold leftSel
      split
      · rename_i hpos
        refine selAt_false_of_adj n d w i hi h hsel (⟨⟨i / n, hdiv⟩, ⟨i % n - 1, by omega⟩⟩)
          ?_ (Or.inl (Or.inl ⟨Fin.ext hc1.symm, Or.inl (by simp only; omega)⟩))
        rw [cell_val]
        simp only
        omega
      · rfl
    · -- the cell above-right (only for `d = true`)
      cases d
      · rfl
      · rw [Bool.true_and]
        unfold aboveRightSel
        split
        · rename_i hpos
          refine selAt_false_of_adj n true w i hi h hsel
            (⟨⟨i / n - 1, by omega⟩, ⟨i % n + 1, hpos.2⟩⟩) ?_
            (Or.inr ⟨rfl, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩)
          rw [cell_val]
          simp only
          have : n * (i / n - 1) + n = n * (i / n) := by
            rw [← Nat.mul_succ]; congr 1; omega
          omega
        · rfl
  · rintro ⟨h, himp⟩ u v hu hv su sv hadj
    by_cases hu' : (cell n u).val < i
    · by_cases hv' : (cell n v).val < i
      · exact h u v hu' hv' su sv hadj
      · exact not_adj_cur n d w i hi himp u v hu' (by omega) su sv hadj
    · have hui : (cell n u).val = i := by omega
      have hv' : (cell n v).val < i := by
        rcases Nat.lt_or_ge (cell n v).val i with h' | h'
        · exact h'
        · exfalso
          have : (cell n v).val = i := by omega
          have huv : u = v := (cell n).injective (Fin.ext (hui.trans this.symm))
          subst huv
          exact adjD_irrefl n d u hadj
      exact not_adj_cur n d w i hi himp v u hv' hui sv su (adjD_symm n d hadj)

theorem front_zero (w : Word (n * n) 2) : front n w 0 = (mspec n d).root := by
  funext j
  simp [front, mspec]

theorem selAt_cell (w : Word (n * n) 2) (i : Nat) (hi : i < n * n) :
    selAt n w (i / n) (i % n) = decide (w ⟨i, hi⟩ = 1) := by
  have := selAt_eq n w (cellInv n i hi)
  rwa [cellInv_fst, cellInv_snd, cell_cellInv] at this

/-- One step from the described frontier: reject iff cell `i` is selected and `blocked`,
else move to the next frontier. -/
theorem mstep_front (hn : 0 < n) (w : Word (n * n) 2) (i : Nat) (hi : i < n * n) :
    mstep n d i (front n w i) (w ⟨i, hi⟩) =
      if w ⟨i, hi⟩ = 1 ∧ blocked n d w i = true then none
      else some (front n w (i + 1)) := by
  unfold mstep
  rw [dif_pos (Nat.mod_lt i hn)]
  simp only [front_above]
  rw [front_left' n w i (Nat.mod_lt i hn), front_aboveRight', front_succ n hn w i,
    selAt_cell n w i hi]
  by_cases hsel : w ⟨i, hi⟩ = 1
  · have hv : (w ⟨i, hi⟩).val = 1 := by rw [hsel]; rfl
    rw [if_pos hv]
    by_cases hr : blocked n d w i = true
    · simp [hsel, ← hr, blocked]
    · simp [hsel, hr, show (aboveSel n w i || leftSel n w i || (d && aboveRightSel n w i)) = false
        from Bool.eq_false_iff.mpr hr]
  · have hv : ¬ (w ⟨i, hi⟩).val = 1 := fun h => hsel (Fin.ext h)
    rw [if_neg hv]
    simp [hsel]

/-- `front` describes the run of the automaton on `w`. -/
theorem isFront_front (hn : 0 < n) (w : Word (n * n) 2) :
    (mspec n d).IsFront w (front n w) where
  zero := front_zero n d w
  step i hi s' h := by
    change mstep n d i (front n w i) (w ⟨i, hi⟩) = some s' at h
    rw [mstep_front n d hn w i hi] at h
    split at h
    · exact absurd h (by simp)
    · exact (Option.some.inj h).symm

/-- The step at cell `i` does not reject iff, when selected, it is not `blocked`. -/
theorem stepOK_iff (hn : 0 < n) (w : Word (n * n) 2) (i : Nat) (hi : i < n * n) :
    (mspec n d).StepOK w (front n w) i hi ↔ (w ⟨i, hi⟩ = 1 → blocked n d w i = false) := by
  unfold Spec.StepOK
  change mstep n d i (front n w i) (w ⟨i, hi⟩) ≠ none ↔ _
  rw [mstep_front n d hn w i hi]
  by_cases hsel : w ⟨i, hi⟩ = 1 <;> by_cases hb : blocked n d w i <;> simp [hsel, hb]

/-- Independence of the first `i` cells is the per-cell condition at every earlier cell. -/
theorem indepUpTo_iff (hn : 0 < n) (w : Word (n * n) 2) (i : Nat) (hi : i ≤ n * n) :
    IndepUpTo n d w i ↔ ∀ j (hj : j < n * n), j < i →
      (w ⟨j, hj⟩ = 1 → blocked n d w j = false) := by
  induction i with
  | zero => exact ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ => indepUpTo_zero n d w⟩
  | succ i ih =>
    have hi' : i < n * n := hi
    rw [indepUpTo_succ n d hn w i hi', ih hi'.le]
    constructor
    · rintro ⟨h, hc⟩ j hj hji
      rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hlt | rfl
      · exact h j hj hlt
      · exact hc
    · intro h
      exact ⟨fun j hj hji => h j hj (Nat.lt_succ_of_lt hji), h i hi' (Nat.lt_succ_self i)⟩

theorem indepUpTo_iff_isIndep (w : Word (n * n) 2) :
    IndepUpTo n d w (n * n) ↔ IsIndep n d (toSet n w) := by
  constructor
  · intro hind u hu v hv hadj
    simp only [toSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact hind u v (cell n u).isLt (cell n v).isLt hu hv hadj
  · intro hind u v _ _ su sv hadj
    exact hind u (by simp [toSet, su]) v (by simp [toSet, sv]) hadj

/-- A word is accepted by the frontier automaton iff it selects an independent set. -/
theorem accepts_iff (w : Word (n * n) 2) : (mspec n d).Accepts w ↔ IsIndep n d (toSet n w) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    constructor
    · intro _ u
      exact (Fin.elim0 u.1)
    · intro _
      show (mspec 0 d).acceptsB w = true
      simp [Spec.acceptsB, Spec.acceptsFrom, List.ofFn_zero, mspec]
  · rw [(mspec n d).accepts_iff_front (isFront_front n d hn w),
      and_iff_left (show (mspec n d).final (front n w (n * n)) = true from rfl),
      ← indepUpTo_iff_isIndep, indepUpTo_iff n d hn w (n * n) le_rfl]
    exact ⟨fun h j hj _ => (stepOK_iff n d hn w j hj).mp (h j hj),
      fun h j hj => (stepOK_iff n d hn w j hj).mpr (h j hj hj)⟩

/-- Accepted words of `mspec n d` correspond to independent sets. -/
def acceptedEquiv : (mspec n d).Accepted ≃ {s : Finset (V n) // IsIndep n d s} :=
  Equiv.subtypeEquiv (wordEquivSet n) (accepts_iff n d)

theorem card_eq :
    Fintype.card {s : Finset (V n) // IsIndep n d s} = Fintype.card (mspec n d).Accepted :=
  (Fintype.card_congr (acceptedEquiv n d)).symm

theorem A006506_eq_card : A006506 n = Fintype.card (mspec n false).Accepted :=
  card_eq n false

theorem A066864_eq_card : A066864 n = Fintype.card (mspec n true).Accepted :=
  card_eq n true

end Tally.GridIndep

import Tally.Families.GridIndep
import Tally.Engine
import Tally.Bits

/-!
# The bitmask specification simulates the frontier specification

For `n ≤ 64` and either value of the diagonal flag `d`, the `UInt64` state of
`fspec n d` represents the frontier `Fin n → Bool` of `mspec n d` bit by bit
(`Rel`). The family proves the root case (`rel_root`) and the one-step lemma
(`fstep_rel`), which make `Rel` a simulation (`fspec_isSim`); the induction over
the word is the generic one in `Tally.Spec`. The main theorems
`A006506_eq_count` (`d = false`) and `A066864_eq_count` (`d = true`), which
combine this simulation with `Spec.count_eq_of_sim`, live in `GridIndepMain`.
-/

namespace Tally.GridIndep

open Tally Tally.Bits

theorem fstep_rel (n : Nat) (d : Bool) (hn0 : 0 < n) (hn : n ≤ 64) (i : Nat) (s : UInt64)
    (t : MState n) (h : Rel n s t) (a : Fin 2) :
    (fspec n d).StepRel (mspec n d) (Rel n) i s t a := by
  unfold Spec.StepRel
  rw [show (fspec n d).step = fstep n d from rfl, show (mspec n d).step = mstep n d from rfl]
  have hc : i % n < n := Nat.mod_lt _ hn0
  have hc64 : i % n < 64 := by omega
  have abo : ((s &&& ((1 : UInt64) <<< (i % n).toUInt64)) != 0) = t ⟨i % n, hc⟩ := by
    rw [and_single_ne_zero s _ (i % n) hc64 (fun j hj => by rw [bit_getLsbD _ hc64 j]; simp [hj])]
    exact h ⟨i % n, hc⟩
  have lft : ((i % n != 0) && ((s &&& (((1 : UInt64) <<< (i % n).toUInt64) >>> 1)) != 0)) =
      (if hc0 : 0 < i % n then t ⟨i % n - 1, by omega⟩ else false) := by
    by_cases hc0 : 0 < i % n
    · rw [dif_pos hc0, and_single_ne_zero s _ (i % n - 1) (by omega)
        (fun j hj => bitr_getLsbD _ hc64 hc0 j hj)]
      have hne : (i % n != 0) = true := by simp; omega
      rw [hne, Bool.true_and]
      exact h ⟨i % n - 1, by omega⟩
    · rw [dif_neg hc0]
      have he : i % n = 0 := by omega
      simp [he]
  have abr : (d && decide (i % n + 1 < n) &&
      ((s &&& (((1 : UInt64) <<< (i % n).toUInt64) <<< 1)) != 0)) =
      (d && (if hc1 : i % n + 1 < n then t ⟨i % n + 1, hc1⟩ else false)) := by
    by_cases hc1 : i % n + 1 < n
    · rw [dif_pos hc1, decide_eq_true hc1, Bool.and_true, and_single_ne_zero s _ (i % n + 1)
        (by omega) (fun j hj => bitl_getLsbD _ (by omega) j hj)]
      rw [h ⟨i % n + 1, hc1⟩]
    · rw [dif_neg hc1, decide_eq_false hc1]
      simp
  simp only [fstep, mstep, dif_pos hc]
  rw [abo, lft, abr]
  split_ifs
  all_goals first
    | trivial
    | (intro j
       have hj : j.val < 64 := by omega
       first
         | rw [or_bit_getLsbD s _ hc64 j.val hj, h j]
         | rw [andnot_bit_getLsbD s _ hc64 j.val hj, h j]
       by_cases hji : j.val = i % n <;> simp [Function.update_apply, Fin.ext_iff, hji])

theorem rel_root (n : Nat) : Rel n 0 (fun _ => false) := by
  intro j; simp

/-- `Rel` is a simulation of `mspec n d` by `fspec n d`. -/
theorem fspec_isSim (n : Nat) (d : Bool) (hn : n ≤ 64) : (fspec n d).IsSim (mspec n d) (Rel n) where
  root := rel_root n
  step i hi s t a h := fstep_rel n d (Nat.pos_of_ne_zero (by rintro rfl; simp at hi)) hn i s t h a
  final _ _ _ := rfl

end Tally.GridIndep

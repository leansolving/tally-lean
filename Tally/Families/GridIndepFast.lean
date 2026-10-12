import Tally.Families.GridIndep
import Tally.Engine
import Tally.Bits

/-!
# The bitmask specification simulates the frontier specification

For `n ≤ 64` the `UInt64` state of `fspec n` represents the frontier
`Fin n → Bool` of `mspec n` bit by bit (`Rel`). The family proves the root case
(`rel_root`) and the one-step lemma (`fstep_rel`), which make `Rel` a simulation
(`fspec_isSim`); the induction over the word is the generic one in `Tally.Spec`.
Then `Spec.count_eq_of_sim` gives `A006506 n = (fspec n).count`
(`A006506_eq_count`): the number the engine computes is the number of
independent sets of the `n × n` grid.
-/

namespace Tally.GridIndep

open Tally Tally.Bits

theorem fstep_rel (n : Nat) (hn0 : 0 < n) (hn : n ≤ 64) (i : Nat) (s : UInt64) (t : MState n)
    (h : Rel n s t) (a : Fin 2) : (fspec n).StepRel (mspec n) (Rel n) i s t a := by
  unfold Spec.StepRel
  rw [show (fspec n).step = fstep n from rfl, show (mspec n).step = mstep n from rfl]
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
  simp only [fstep, mstep, dif_pos hc]
  rw [abo, lft]
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

/-- `Rel` is a simulation of `mspec n` by `fspec n`. -/
theorem fspec_isSim (n : Nat) (hn : n ≤ 64) : (fspec n).IsSim (mspec n) (Rel n) where
  root := rel_root n
  step i hi s t a h := fstep_rel n (Nat.pos_of_ne_zero (by rintro rfl; simp at hi)) hn i s t h a
  final _ _ _ := rfl

/-- **Main theorem of the family.** For `n ≤ 64`, the engine run on the bitmask
specification computes `A006506 n`. -/
theorem A006506_eq_count (n : Nat) (hn : n ≤ 64) : A006506 n = (fspec n).count := by
  rw [Spec.count_eq_of_sim (fspec n) (fspec_isSim n hn), A006506_eq_card]

/-- Compiled check `(fspec n).count = expected`, kept out of line so that
`native_decide` calls this compiled function instead of inlining (and then
interpreting) the engine. -/
@[noinline] def checkCount (n expected : Nat) : Bool := decide ((fspec n).count = expected)

theorem count_eq_of_check {n expected : Nat} (h : checkCount n expected = true) :
    (fspec n).count = expected :=
  of_decide_eq_true h

end Tally.GridIndep

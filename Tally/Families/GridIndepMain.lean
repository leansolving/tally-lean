import Tally.Families.GridIndepAccept
import Tally.Families.GridIndepFast
import Tally.Engine

/-!
# Grid / rhombus independent sets: assembly of the family theorems

`card_eq_count` (for `n ≤ 64` the engine run on the packed specification computes the
number of independent sets of `AdjD n d`), instantiated to `A006506_eq_count`
(`d = false`, grid graph) and `A066864_eq_count` (`d = true`, triangular rhombus),
plus the compiled checker `checkCount` for the value theorems in `TallyValues`.
-/

namespace Tally.GridIndep

open Tally Tally.Grid

variable (n : Nat) (d : Bool)

/-- For `n ≤ 64` the engine run on the packed specification counts the independent sets. -/
theorem card_eq_count (hn : n ≤ 64) :
    Fintype.card {s : Finset (V n) // IsIndep n d s} = (fspec n d).count := by
  rw [Spec.count_eq_of_sim (fspec n d) (fspec_isSim n d hn), card_eq n d]

/-- **Main theorem for A006506.** For `n ≤ 64`, the engine run on the bitmask
specification computes `A006506 n`. -/
theorem A006506_eq_count (hn : n ≤ 64) : A006506 n = (fspec n false).count :=
  card_eq_count n false hn

/-- **Main theorem for A066864.** For `n ≤ 64`, the engine run on the bitmask
specification computes `A066864 n`. -/
theorem A066864_eq_count (hn : n ≤ 64) : A066864 n = (fspec n true).count :=
  card_eq_count n true hn

/-- Compiled check `(fspec n d).count = expected`, kept out of line so that
`native_decide` calls this compiled function instead of inlining (and then
interpreting) the engine. -/
@[noinline] def checkCount (n : Nat) (d : Bool) (expected : Nat) : Bool :=
  decide ((fspec n d).count = expected)

theorem count_eq_of_check {n : Nat} {d : Bool} {expected : Nat}
    (h : checkCount n d expected = true) : (fspec n d).count = expected :=
  of_decide_eq_true h


/-- Compiled check through the parallel engine (`Spec.countPar` with `P` shards, per-worker
spec and partition objects; same trust base as `checkCount`). -/
@[noinline] def checkCountPar (n : Nat) (d : Bool) (P : Nat) (expected : Nat) : Bool :=
  decide (Spec.countPar (mkSpec n d) (mkPart n (Nat.log2 P)) P = expected)

theorem count_eq_of_checkPar {n : Nat} {d : Bool} {P expected : Nat}
    (h : checkCountPar n d P expected = true) : (fspec n d).count = expected := by
  rw [Spec.count_eq]
  have e := Spec.countPar_eq (mkSpec n d) (mkPart n (Nat.log2 P)) P (fun _ => rfl)
  exact e ▸ of_decide_eq_true h

end Tally.GridIndep

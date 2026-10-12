import Tally.Families.GridIndepMain

/-!
# Values of A066864 reproduced by the engine

Same pattern as `TallyValues/GridIndep.lean`: rewrite with the kernel-checked
`A066864_eq_count`, evaluate the compiled checker with `native_decide`. Values agree
with the OEIS b-file (n ≤ 12 here; larger known and new terms are run on the cluster).
Trust base of these value theorems: Lean kernel plus the Lean compiler, runtime and GMP
(the per-theorem axiom `A066864_n._native.native_decide.ax_*` that `#print axioms` shows).
-/

namespace TallyValues.HexIndep

open Tally.GridIndep

theorem A066864_0 : A066864 0 = 1 := by
  rw [A066864_eq_count 0 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_1 : A066864 1 = 2 := by
  rw [A066864_eq_count 1 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_2 : A066864 2 = 6 := by
  rw [A066864_eq_count 2 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_3 : A066864 3 = 42 := by
  rw [A066864_eq_count 3 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_4 : A066864 4 = 524 := by
  rw [A066864_eq_count 4 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_5 : A066864 5 = 13322 := by
  rw [A066864_eq_count 5 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_6 : A066864 6 = 647252 := by
  rw [A066864_eq_count 6 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_7 : A066864 7 = 61758332 := by
  rw [A066864_eq_count 7 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_8 : A066864 8 = 11435477118 := by
  rw [A066864_eq_count 8 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_9 : A066864 9 = 4129523869606 := by
  rw [A066864_eq_count 9 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_10 : A066864 10 = 2902264461628298 := by
  rw [A066864_eq_count 10 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_11 : A066864 11 = 3973109800760143708 := by
  rw [A066864_eq_count 11 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A066864_12 : A066864 12 = 10590895512774862686570 := by
  rw [A066864_eq_count 12 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A066864_12

end TallyValues.HexIndep

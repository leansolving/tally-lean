import Tally.Families.BarArrayMain

/-!
# Values of A145789, A145757, A145773 reproduced by the engine

Same pattern as `TallyValues/GridIndep.lean`: rewrite with the kernel-checked
`*_eq_count`, evaluate the compiled checker with `native_decide`. Values agree
with the OEIS b-files. Small `n` only; larger known terms and new terms are run
on the cluster.
-/

namespace TallyValues.BarArray

open Tally.BarArray

theorem A145789_0 : A145789 0 = 1 := by
  rw [A145789_eq_count 0 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_1 : A145789 1 = 1 := by
  rw [A145789_eq_count 1 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_2 : A145789 2 = 1 := by
  rw [A145789_eq_count 2 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_3 : A145789 3 = 1 := by
  rw [A145789_eq_count 3 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_4 : A145789 4 = 15 := by
  rw [A145789_eq_count 4 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_5 : A145789 5 = 89 := by
  rw [A145789_eq_count 5 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_6 : A145789 6 = 904 := by
  rw [A145789_eq_count 6 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_7 : A145789 7 = 10469 := by
  rw [A145789_eq_count 7 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_8 : A145789 8 = 202299 := by
  rw [A145789_eq_count 8 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_9 : A145789 9 = 6253788 := by
  rw [A145789_eq_count 9 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_10 : A145789 10 = 295345323 := by
  rw [A145789_eq_count 10 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_11 : A145789 11 = 20297903190 := by
  rw [A145789_eq_count 11 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145789_12 : A145789 12 = 2062672356086 := by
  rw [A145789_eq_count 12 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145757_1 : A145757 1 = 1 := by
  rw [A145757_eq_count 1 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145757_2 : A145757 2 = 1 := by
  rw [A145757_eq_count 2 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145757_3 : A145757 3 = 9 := by
  rw [A145757_eq_count 3 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145757_4 : A145757 4 = 45 := by
  rw [A145757_eq_count 4 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145757_5 : A145757 5 = 476 := by
  rw [A145757_eq_count 5 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145757_6 : A145757 6 = 6933 := by
  rw [A145757_eq_count 6 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145757_7 : A145757 7 = 199238 := by
  rw [A145757_eq_count 7 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145757_8 : A145757 8 = 8764691 := by
  rw [A145757_eq_count 8 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145757_9 : A145757 9 = 657200985 := by
  rw [A145757_eq_count 9 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145757_10 : A145757 10 = 80295518797 := by
  rw [A145757_eq_count 10 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145757_11 : A145757 11 = 16444907566268 := by
  rw [A145757_eq_count 11 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145773_0 : A145773 0 = 1 := by
  rw [A145773_eq_count 0 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145773_1 : A145773 1 = 1 := by
  rw [A145773_eq_count 1 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145773_2 : A145773 2 = 5 := by
  rw [A145773_eq_count 2 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145773_3 : A145773 3 = 25 := by
  rw [A145773_eq_count 3 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145773_4 : A145773 4 = 314 := by
  rw [A145773_eq_count 4 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145773_5 : A145773 5 = 7358 := by
  rw [A145773_eq_count 5 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145773_6 : A145773 6 = 349511 := by
  rw [A145773_eq_count 6 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145773_7 : A145773 7 = 32855368 := by
  rw [A145773_eq_count 7 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145773_8 : A145773 8 = 6141909014 := by
  rw [A145773_eq_count 8 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145773_9 : A145773 9 = 2284689480141 := by
  rw [A145773_eq_count 9 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A145773_10 : A145773 10 = 1689669248970784 := by
  rw [A145773_eq_count 10 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145789_12

end TallyValues.BarArray

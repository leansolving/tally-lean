import Tally.Families.BarArrayMain

/-! Known b-file terms of A145789, A145757, A145773 re-derived by the verified engine
through the compiled checker (regression for the larger runs).
Trust base of this value theorem: Lean kernel plus the Lean compiler, runtime and GMP
(`native_decide`; the per-theorem axiom `<thm>._native.native_decide.ax_*` shown by
`#print axioms`). The family theorem it rewrites with is kernel-checked. -/

namespace TallyValues.BarArray

open Tally.BarArray

set_option maxHeartbeats 0 in
theorem A145789_13 : A145789 13 = 313264131593508 := by
  rw [A145789_eq_count 13 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145789_13

set_option maxHeartbeats 0 in
theorem A145789_14 : A145789 14 = 71761762035300434 := by
  rw [A145789_eq_count 14 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145789_14

set_option maxHeartbeats 0 in
theorem A145789_15 : A145789 15 = 24717630557949691794 := by
  rw [A145789_eq_count 15 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145789_15

set_option maxHeartbeats 0 in
theorem A145789_16 : A145789 16 = 12717303956216247045468 := by
  rw [A145789_eq_count 16 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145789_16

set_option maxHeartbeats 0 in
theorem A145757_12 : A145757 12 = 5549422397331424 := by
  rw [A145757_eq_count 12 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145757_12

set_option maxHeartbeats 0 in
theorem A145757_13 : A145757 13 = 3112070848837147326 := by
  rw [A145757_eq_count 13 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145757_13

set_option maxHeartbeats 0 in
theorem A145773_11 : A145773 11 = 2485350221377308028 := by
  rw [A145773_eq_count 11 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145773_11

set_option maxHeartbeats 0 in
theorem A145773_12 : A145773 12 = 7269523179423750332937 := by
  rw [A145773_eq_count 12 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145773_12

set_option maxHeartbeats 0 in
theorem A145773_13 : A145773 13 = 42286820404292801713317670 := by
  rw [A145773_eq_count 13 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145773_13

set_option maxHeartbeats 0 in
theorem A145773_14 : A145773 14 = 489171492515135237008883532896 := by
  rw [A145773_eq_count 14 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145773_14

set_option maxHeartbeats 0 in
theorem A145773_15 : A145773 15 = 11253368362763343319841968035523559 := by
  rw [A145773_eq_count 15 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145773_15

set_option maxHeartbeats 0 in
theorem A145773_16 : A145773 16 = 514834001847660368120286449303218684955 := by
  rw [A145773_eq_count 16 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145773_16

end TallyValues.BarArray

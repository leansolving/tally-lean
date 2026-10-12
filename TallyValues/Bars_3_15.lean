import Tally.Families.BarArrayMain

/-! A145757 15: value computed by the Rust twin (bars) and the compiled runner,
certified here by the verified engine through the compiled checker.
Trust base of this value theorem: Lean kernel plus the Lean compiler, runtime and GMP
(`native_decide`; the per-theorem axiom `<thm>._native.native_decide.ax_*` shown by
`#print axioms`). The family theorem it rewrites with is kernel-checked. -/

namespace TallyValues.BarArray

open Tally.BarArray

set_option maxHeartbeats 0 in
theorem A145757_15 : A145757 15 = 4445172150564510501924876 := by
  rw [A145757_eq_count 15 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145757_15

end TallyValues.BarArray

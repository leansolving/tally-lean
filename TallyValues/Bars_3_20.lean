import Tally.Families.BarArrayMain

/-! A145757 20: value computed by the Rust twin (bars) and the compiled runner,
certified here by the verified engine through the compiled checker.
Trust base of this value theorem: Lean kernel plus the Lean compiler, runtime and GMP
(`native_decide`; the per-theorem axiom `<thm>._native.native_decide.ax_*` shown by
`#print axioms`). The family theorem it rewrites with is kernel-checked. -/

namespace TallyValues.BarArray

open Tally.BarArray

set_option maxHeartbeats 0 in
theorem A145757_20 : A145757 20 = 74884831469127956412481229662897119514478477 := by
  rw [A145757_eq_count 20 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145757_20

end TallyValues.BarArray

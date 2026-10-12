import Tally.Families.BarArrayMain

/-! A145773 17: value computed by the Rust twin (bars) and the compiled runner,
certified here by the verified engine through the compiled checker.
Trust base of this value theorem: Lean kernel plus the Lean compiler, runtime and GMP
(`native_decide`; the per-theorem axiom `<thm>._native.native_decide.ax_*` shown by
`#print axioms`). The family theorem it rewrites with is kernel-checked. -/

namespace TallyValues.BarArray

open Tally.BarArray

set_option maxHeartbeats 0 in
theorem A145773_17 : A145773 17 = 46839836853957809440360002900901859008904988 := by
  rw [A145773_eq_count 17 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145773_17

end TallyValues.BarArray

import Tally.Families.BarArrayMain

/-! A145773 18: value computed by the Rust twin (bars) and the compiled runner,
certified here by the verified engine through the compiled checker.
Trust base of this value theorem: Lean kernel plus the Lean compiler, runtime and GMP
(`native_decide`; the per-theorem axiom `<thm>._native.native_decide.ax_*` shown by
`#print axioms`). The family theorem it rewrites with is kernel-checked. -/

namespace TallyValues.BarArray

open Tally.BarArray

set_option maxHeartbeats 0 in
theorem A145773_18 : A145773 18 = 8474755609615024639072040185775092207187308736075 := by
  rw [A145773_eq_count 18 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A145773_18

end TallyValues.BarArray

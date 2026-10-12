import Tally.Families.GridIndepMain

/-! Scaling test: A006506 32 (b-file value) through the compiled checker.
Trust base of this value theorem: Lean kernel plus the Lean compiler, runtime and GMP
(`native_decide`; the per-theorem axiom `<thm>._native.native_decide.ax_*` shown by
`#print axioms`). The family theorem it rewrites with is kernel-checked. -/

namespace TallyValues.GridIndep

open Tally.GridIndep

set_option maxHeartbeats 0 in
theorem A006506_32 : A006506 32 = 1293610782537380062750834541787067327216099960402483810534636303148904354725352922280461789260135159483731789518847103985667992830570856310313642194651494698031350657047234754882428439 := by
  rw [A006506_eq_count 32 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A006506_32

end TallyValues.GridIndep

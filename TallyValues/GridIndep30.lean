import Tally.Families.GridIndepFast

/-! Scaling test: A006506 30 (b-file value) through the compiled checker.
Trust base of this value theorem: Lean kernel plus the Lean compiler, runtime and GMP
(`native_decide`; the per-theorem axiom `<thm>._native.native_decide.ax_*` shown by
`#print axioms`). The family theorem it rewrites with is kernel-checked. -/

namespace TallyValues.GridIndep

open Tally.GridIndep

set_option maxHeartbeats 0 in
theorem A006506_30 : A006506 30 = 112377766778527126203646648402050958984330252199994469198044986979798657215652532005142877926040203499014641860333039219325350361465468647055420204598509312491705 := by
  rw [A006506_eq_count 30 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A006506_30

end TallyValues.GridIndep

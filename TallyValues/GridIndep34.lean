import Tally.Families.GridIndepFast

/-! Scaling test: A006506 34 (b-file value) through the compiled checker.
Trust base of this value theorem: Lean kernel plus the Lean compiler, runtime and GMP
(`native_decide`; the per-theorem axiom `<thm>._native.native_decide.ax_*` shown by
`#print axioms`). The family theorem it rewrites with is kernel-checked. -/

namespace TallyValues.GridIndep

open Tally.GridIndep

set_option maxHeartbeats 0 in
theorem A006506_34 : A006506 34 = 387891128933234889019525245048798489818497881776634515543429025520634672163871702025048010830489308788291356426276659253850079610851584099797152548773065607505250668587876084152495126750481594564582029827282 := by
  rw [A006506_eq_count 34 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A006506_34

end TallyValues.GridIndep

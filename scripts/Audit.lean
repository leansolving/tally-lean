import Tally
import TallyValues

/-! Axiom audit (run by `scripts/audit.sh`). Kernel-checked results must depend on
`propext`, `Classical.choice`, `Quot.sound` only; the two controls at the end must
show a `native_decide` axiom, which proves that the check can see one. -/

#print axioms Tally.Spec.count_eq
#print axioms Tally.Spec.countPar_eq
#print axioms Tally.Spec.accepts_iff_front
#print axioms Tally.Spec.accepts_iff_sim
#print axioms Tally.GridIndep.A006506_eq_count
#print axioms Tally.GridIndep.A066864_eq_count
#print axioms Tally.BarArray.A145789_eq_count
#print axioms Tally.BarArray.A145757_eq_count
#print axioms Tally.BarArray.A145773_eq_count
#print axioms Tally.GridIndep.count_eq_of_check
#print axioms Tally.GridIndep.count_eq_of_checkPar
#print axioms Tally.BarArray.count_eq_of_check
#print axioms Tally.BarArray.count_eq_of_checkPar
-- controls: value theorems carry their native_decide axiom
#print axioms Tally.Examples.noTwoOnes_ten
#print axioms TallyValues.GridIndep.A006506_16

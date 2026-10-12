import Tally.Families.GridIndepMain

/-! A066864 12 through the parallel engine (`checkCountPar`, 4 shards): the test module for
value theorems that run `Spec.countPar` inside `native_decide`. Same trust base as the
sequential value theorems. -/

namespace TallyValues.HexIndep

open Tally.GridIndep

theorem A066864_12_par : A066864 12 = 10590895512774862686570 := by
  rw [A066864_eq_count 12 (by omega)]
  exact count_eq_of_checkPar (P := 4) (by native_decide)

#print axioms A066864_12_par

end TallyValues.HexIndep

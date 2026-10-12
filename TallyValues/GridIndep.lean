import Tally.Families.GridIndepMain

/-!
# Values of A006506 reproduced by the engine

Each theorem `A006506_n` states an OEIS term (b-file b006506.txt). Proof:
rewrite with the kernel-checked `A006506_eq_count`, then evaluate the compiled
checker `checkCount` with `native_decide`. Trust base of these value theorems:
Lean kernel plus the Lean compiler, runtime and GMP (the per-theorem axiom
`A006506_n._native.native_decide.ax_*` that `#print axioms` shows).
-/

namespace TallyValues.GridIndep

open Tally.GridIndep

theorem A006506_0 : A006506 0 = 1 := by
  rw [A006506_eq_count 0 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_1 : A006506 1 = 2 := by
  rw [A006506_eq_count 1 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_2 : A006506 2 = 7 := by
  rw [A006506_eq_count 2 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_3 : A006506 3 = 63 := by
  rw [A006506_eq_count 3 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_4 : A006506 4 = 1234 := by
  rw [A006506_eq_count 4 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_5 : A006506 5 = 55447 := by
  rw [A006506_eq_count 5 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_6 : A006506 6 = 5598861 := by
  rw [A006506_eq_count 6 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_7 : A006506 7 = 1280128950 := by
  rw [A006506_eq_count 7 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_8 : A006506 8 = 660647962955 := by
  rw [A006506_eq_count 8 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_9 : A006506 9 = 770548397261707 := by
  rw [A006506_eq_count 9 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_10 : A006506 10 = 2030049051145980050 := by
  rw [A006506_eq_count 10 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_11 : A006506 11 = 12083401651433651945979 := by
  rw [A006506_eq_count 11 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_12 : A006506 12 = 162481813349792588536582997 := by
  rw [A006506_eq_count 12 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_13 : A006506 13 = 4935961285224791538367780371090 := by
  rw [A006506_eq_count 13 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_14 : A006506 14 = 338752110195939290445247645371206783 := by
  rw [A006506_eq_count 14 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_15 : A006506 15 = 52521741712869136440040654451875316861275 := by
  rw [A006506_eq_count 15 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_16 : A006506 16 = 18396766424410124752958806046933947217821482942 := by
  rw [A006506_eq_count 16 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_17 : A006506 17 = 14557601701834111295974187104248827765798599152358303 := by
  rw [A006506_eq_count 17 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_18 : A006506 18 = 26024585612650837861658126921792857026992497268285945167621 := by
  rw [A006506_eq_count 18 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_19 : A006506 19 = 105105055066577962012604229608317915229737651637019975757755051314 := by
  rw [A006506_eq_count 19 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_20 : A006506 20 = 958979036662929619406859624886958746851620546557485230898539651354907499 := by
  rw [A006506_eq_count 20 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_21 : A006506 21 = 19766982580727525559447459703066410506378295841376040664015562851325369819076327 := by
  rw [A006506_eq_count 21 (by omega)]
  exact count_eq_of_check (by native_decide)

theorem A006506_22 : A006506 22 = 920486427724231647653646535134255190048558085587696509535085179014710020739303637413062 := by
  rw [A006506_eq_count 22 (by omega)]
  exact count_eq_of_check (by native_decide)

#print axioms A006506_22

end TallyValues.GridIndep

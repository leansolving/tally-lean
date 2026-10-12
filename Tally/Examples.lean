import Tally.Engine

/-!
# Smoke tests and axiom audit for the engine

Three toy specifications whose counts are known in closed form. The `example`s
compare the engine's count with those closed-form values on small lengths
(through `native_decide`; kernel `decide` would be too slow), and one theorem
instantiates `Spec.count_eq` so that it is kernel-checked without computing
anything. The `#print axioms` lines are the audit:
the engine theorem must depend on `propext`, `Classical.choice`, `Quot.sound`
only, and the `native_decide` positive control must show its generated
`_native.native_decide.ax` axiom.
-/

namespace Tally.Examples

/-- Binary words with no two consecutive ones; state = last symbol. Count: Fibonacci. -/
def noTwoOnes (L : Nat) : Spec Bool L 2 where
  root := false
  step := fun _ last a => if last && a.val == 1 then none else some (a.val == 1)
  final := fun _ => true

/-- All words over `Fin 3`. Count: `3^L`. -/
def allWords (L : Nat) : Spec Unit L 3 where
  root := ()
  step := fun _ _ _ => some ()
  final := fun _ => true

/-- Binary words with an even number of ones. Count: `2^(L-1)` for `L ≥ 1`, `1` for `L = 0`. -/
def evenOnes (L : Nat) : Spec Bool L 2 where
  root := false
  step := fun _ p a => some (p != (a.val == 1))
  final := fun p => !p

-- engine against closed forms (compiled evaluation)
example : (List.range 8).map (fun L => (noTwoOnes L).count) = [1, 2, 3, 5, 8, 13, 21, 34] := by
  native_decide
example : (List.range 6).map (fun L => (allWords L).count) = [1, 3, 9, 27, 81, 243] := by
  native_decide
example : (List.range 8).map (fun L => (evenOnes L).count) = [1, 1, 2, 4, 8, 16, 32, 64] := by
  native_decide

-- the degenerate cases: the empty word is accepted iff the root is final
example : (noTwoOnes 0).count = 1 := by native_decide
example : (evenOnes 0).count = 1 := by native_decide

-- kernel-checked instance of the main theorem (no native evaluation)
theorem noTwoOnes_five : (noTwoOnes 5).count = Fintype.card (noTwoOnes 5).Accepted :=
  Spec.count_eq _

/-- Positive control for the axiom audit: a `native_decide` value theorem. -/
theorem noTwoOnes_ten : (noTwoOnes 10).count = 144 := by native_decide

#print axioms Tally.Spec.count_eq
#print axioms Tally.Spec.count_eq_card_filter
#print axioms noTwoOnes_five
#print axioms noTwoOnes_ten

end Tally.Examples

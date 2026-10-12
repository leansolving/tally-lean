import Tally.Families.BarArray
import Tally.Families.BarArrayLocal
import Tally.Families.BarArrayFront
import Tally.Families.BarArrayAccept
import Tally.Families.BarArrayFast
import Tally.Engine

/-!
# Bar arrays: assembly of the family theorems

`accepts_iff` (a word is accepted by `mspec n k` iff it reads a bar array),
`barCount_eq_card`, and `barCount_eq_count` (for `2 ≤ k ≤ 6`, `n ≤ 20` the engine
run on the packed specification computes `barCount n k`), instantiated to
A145789 (`k = 4`), A145757 (`k = 3`) and A145773 (`k = 2`).
-/

namespace Tally.BarArray

open Tally Tally.Grid

variable (n k : Nat)

/-- A word is accepted iff it reads a bar array. -/
theorem accepts_iff (hk : 2 ≤ k) (w : Word (n * n) 2) :
    (mspec n k).Accepts w ↔ IsBarArray n k (toArray n w) := by
  rw [← isBarArrayLocal_iff n k hk]
  exact ⟨local_of_accepts n k hk w, acceptsB_of_local n k hk w⟩

/-- Accepted words correspond to bar arrays. -/
def acceptedEquiv (hk : 2 ≤ k) : (mspec n k).Accepted ≃ {f : V n → Bool // IsBarArray n k f} :=
  Equiv.subtypeEquiv (wordEquivArray n) (accepts_iff n k hk)

theorem barCount_eq_card (hk : 2 ≤ k) : barCount n k = Fintype.card (mspec n k).Accepted :=
  (Fintype.card_congr (acceptedEquiv n k hk)).symm

/-- **Main theorem of the family.** For `2 ≤ k ≤ 6` and `n ≤ 20`, the engine run on the
packed specification computes the number of `n × n` bar arrays with bar length `k`. -/
theorem barCount_eq_count (hk2 : 2 ≤ k) (hk : k ≤ 6) (hn : n ≤ 20) :
    barCount n k = (fspec n k).count := by
  rw [Spec.count_eq_of_sim (fspec n k) (fspec_isSim hk2 hk hn), barCount_eq_card n k hk2]

theorem A145789_eq_count (hn : n ≤ 20) : A145789 n = (fspec n 4).count :=
  barCount_eq_count n 4 (by omega) (by omega) hn

theorem A145757_eq_count (hn : n ≤ 20) : A145757 n = (fspec n 3).count :=
  barCount_eq_count n 3 (by omega) (by omega) hn

/-- **OEIS A145773**: `n × n` binary arrays whose ones form `1 × 2` or `2 × 1` bars, no two
of them edge-adjacent (diagonal contact is allowed). -/
def A145773 (n : Nat) : Nat := barCount n 2

theorem A145773_eq_count (hn : n ≤ 20) : A145773 n = (fspec n 2).count :=
  barCount_eq_count n 2 (by omega) (by omega) hn

/-- Compiled check `(fspec n k).count = expected`, out of line for `native_decide`. -/
@[noinline] def checkCount (n k expected : Nat) : Bool := decide ((fspec n k).count = expected)

theorem count_eq_of_check {n k expected : Nat} (h : checkCount n k expected = true) :
    (fspec n k).count = expected :=
  of_decide_eq_true h


/-- Compiled check through the parallel engine (`Spec.countPar` with `P` shards, hash
partition; same trust base as `checkCount`). -/
@[noinline] def checkCountPar (n k : Nat) (P : Nat) (expected : Nat) : Bool :=
  decide (Spec.countPar (mkSpec n k) (fun _ => hashPart) P = expected)

theorem count_eq_of_checkPar {n k : Nat} {P expected : Nat}
    (h : checkCountPar n k P expected = true) : (fspec n k).count = expected := by
  rw [Spec.count_eq]
  have e := Spec.countPar_eq (mkSpec n k) (fun _ => hashPart) P (fun _ => rfl)
  exact e ▸ of_decide_eq_true h

end Tally.BarArray

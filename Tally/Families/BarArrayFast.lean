import Tally.Families.BarArray
import Tally.Bits
/-!
# The packed specification simulates the frontier specification

For `2 ≤ k ≤ 6` and `n ≤ 20` the `UInt64` state of `fspec n k` represents a well-formed
frontier state of `mspec n k` field by field (`Rel`). The family proves the root case
(`rel_root`), the one-step lemma (`fstep_rel`) and the final check (`fdone_iff`), which make
`Rel` a simulation (`fspec_isSim`); the induction over the word is the generic one in
`Tally.Spec`.
-/

namespace Tally.BarArray

open Tally Tally.Bits

/-! ### Well-formed states -/

/-- Well-formed column entry: a pending vertical run has length in `1 .. k-1`. -/
def WFc (k : Nat) : Col → Prop
  | .vert m => 1 ≤ m ∧ m < k
  | _ => True

/-- Well-formed left register: a horizontal run has length in `2 .. k-1`. -/
def WFl (k : Nat) : Left → Prop
  | .horiz m => 2 ≤ m ∧ m < k
  | _ => True

/-- Well-formed state: every column entry and the left register are well formed. -/
def WF (k : Nat) {n : Nat} (st : MState n) : Prop := (∀ j, WFc k (st.1 j)) ∧ WFl k st.2

theorem wf_root (k n : Nat) : WF k ((fun _ => .free, .free) : MState n) :=
  ⟨fun _ => trivial, trivial⟩

theorem place_wf {k : Nat} (hk2 : 2 ≤ k) {a : Col} {l : Left} {s : Fin 2} {e : Col}
    {e' : Option Col} {l' : Left} (ha : WFc k a) (hl : WFl k l)
    (h : place k a l s = some (e, e', l')) :
    WFc k e ∧ (∀ x, e' = some x → WFc k x) ∧ WFl k l' := by
  obtain ⟨sv, hs⟩ := s
  obtain rfl | rfl : sv = 0 ∨ sv = 1 := by omega
  all_goals cases a <;> cases l <;>
    simp only [place, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [WFc, WFl] at ha hl
    try split_ifs
    all_goals simp [WFc, WFl]
    all_goals omega

theorem mstep_wf {n k : Nat} (hk2 : 2 ≤ k) (i : Nat) (st st' : MState n) (a : Fin 2)
    (hst : WF k st) (h : mstep n k i st a = some st') : WF k st' := by
  have hc : i % n < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [mstep] at h
    · exact Nat.mod_lt _ hn
  simp only [mstep, dif_pos hc] at h
  rcases hp : place k (st.1 ⟨i % n, hc⟩) st.2 a with _ | ⟨e, e', l'⟩ <;> simp only [hp] at h
  · exact absurd h (by simp)
  obtain ⟨he, he', hl'⟩ := place_wf hk2 (hst.1 _) hst.2 hp
  have hx : ∀ x, e' = some x → WFc k x := he'
  rcases e' with _ | x <;> cases l' <;> simp only at h <;> (try split_ifs at h) <;>
    simp only [Option.some.injEq] at h <;> subst h <;>
    refine ⟨fun j => ?_, ?_⟩ <;> simp only [Function.update_apply] <;> (try split_ifs) <;>
    first | exact hst.1 _ | exact he | exact hx _ rfl | exact hl'


/-! ### Encoding and decoding -/

theorem encCol_lt {k : Nat} (hk : k ≤ 6) {e : Col} (h : WFc k e) : (encCol e).toNat < 8 := by
  cases e with
  | free => decide
  | block => decide
  | vert m =>
    simp only [WFc] at h
    simp only [encCol]
    rw [toUInt64_toNat_small _ (by omega)]
    omega

theorem decCol_encCol {k : Nat} (hk : k ≤ 6) {e : Col} (h : WFc k e) : decCol (encCol e) = e := by
  cases e with
  | free => rfl
  | block => rfl
  | vert m =>
    simp only [WFc] at h
    have h1 := toUInt64_toNat_small (m + 1) (by omega)
    simp only [encCol, decCol]
    rw [if_neg (ne_of_toNat_ne (by rw [h1]; simp)),
      if_neg (ne_of_toNat_ne (by rw [h1]; simp; omega)), h1]
    rfl

theorem encLeft_lt {k : Nat} (hk : k ≤ 6) {l : Left} (h : WFl k l) : (encLeft l).toNat < 8 := by
  cases l with
  | free => decide
  | block => decide
  | pend => decide
  | horiz m =>
    simp only [WFl] at h
    simp only [encLeft]
    rw [toUInt64_toNat_small _ (by omega)]
    omega

theorem decLeft_encLeft {k : Nat} (hk : k ≤ 6) {l : Left} (h : WFl k l) :
    decLeft (encLeft l) = l := by
  cases l with
  | free => rfl
  | block => rfl
  | pend => rfl
  | horiz m =>
    simp only [WFl] at h
    have h1 := toUInt64_toNat_small (m + 1) (by omega)
    simp only [encLeft, decLeft]
    rw [if_neg (ne_of_toNat_ne (by rw [h1]; simp)),
      if_neg (ne_of_toNat_ne (by rw [h1]; simp; omega)),
      if_neg (ne_of_toNat_ne (by rw [h1]; simp; omega)), h1]
    rfl


theorem decLeft_zero : decLeft 0 = .free := rfl

/-! ### The simulation relation -/

/-- The packed state `s` represents the well-formed mathematical state `st`. -/
def Rel (n k : Nat) (s : UInt64) (st : MState n) : Prop :=
  WF k st ∧ (∀ j : Fin n, decCol (getField s j.val) = st.1 j) ∧ decLeft (getField s n) = st.2

theorem fstep_dec {n k : Nat} (hk2 : 2 ≤ k) (hk : k ≤ 6) (hn0 : 0 < n) (hn : n ≤ 20) (i : Nat)
    (s : UInt64) (st : MState n) (h : Rel n k s st) (a : Fin 2) :
    match fstep n k i s a, mstep n k i st a with
    | none, none => True
    | some s', some st' =>
        (∀ j : Fin n, decCol (getField s' j.val) = st'.1 j) ∧ decLeft (getField s' n) = st'.2
    | _, _ => False := by
  obtain ⟨hwf, hcol, hleft⟩ := h
  have hc : i % n < n := Nat.mod_lt _ hn0
  have h1 : decCol (getField s (i % n)) = st.1 ⟨i % n, hc⟩ := hcol ⟨i % n, hc⟩
  simp only [fstep, mstep, dif_pos hc]
  rw [h1, hleft]
  rcases hp : place k (st.1 ⟨i % n, hc⟩) st.2 a with _ | ⟨e, e', l'⟩
  · trivial
  obtain ⟨he, he', hl'⟩ := place_wf hk2 (hwf.1 _) hwf.2 hp
  have hvE := encCol_lt hk he
  have hvL := encLeft_lt hk hl'
  have hdE := decCol_encCol hk he
  have hdL := decLeft_encLeft hk hl'
  have hcn : i % n ≤ 20 := by omega
  have hcm : i % n - 1 ≤ 20 := by omega
  have hx : ∀ x, e' = some x → decCol (encCol x) = x ∧ (encCol x).toNat < 8 :=
    fun x hx => ⟨decCol_encCol hk (he' x hx), encCol_lt hk (he' x hx)⟩
  rcases e' with _ | x <;> by_cases hrow : i % n + 1 = n <;> by_cases h0 : 0 < i % n <;>
    cases l' <;> simp only [hrow, h0, ↓reduceIte, ↓reduceDIte] <;> refine ⟨fun j => ?_, ?_⟩
  all_goals first
    | (have hj : (j : Nat) ≤ 20 := by omega
       have hjn : (j : Nat) ≠ n := by omega
       simp only [UInt64.toNat_zero, Nat.ofNat_pos, getField_setField, ↓reduceIte,
         Function.update_apply, Fin.ext_iff, hvL, hn, hj, hjn, hx, hcm, hvE, hcn]
       split_ifs <;> first | (exfalso; omega) | rfl | simp [*])
    | simp [getField_setField, decLeft_zero, *]


/-- **Step simulation.** Both automata reject together, and otherwise the packed successor
represents the mathematical successor. -/
theorem fstep_rel {n k : Nat} (hk2 : 2 ≤ k) (hk : k ≤ 6) (hn0 : 0 < n) (hn : n ≤ 20) (i : Nat)
    (s : UInt64) (st : MState n) (h : Rel n k s st) (a : Fin 2) :
    (fspec n k).StepRel (mspec n k) (Rel n k) i s st a := by
  unfold Spec.StepRel
  rw [show (fspec n k).step = fstep n k from rfl, show (mspec n k).step = mstep n k from rfl]
  have hd := fstep_dec hk2 hk hn0 hn i s st h a
  rcases hf : fstep n k i s a with _ | s' <;> rcases hm : mstep n k i st a with _ | st' <;>
    simp only [hf, hm] at hd ⊢
  exact ⟨mstep_wf hk2 i st st' a h.1 hm, hd⟩

theorem decCol_done (x : UInt64) : (decCol x).done = decide (x ≤ 1) := by
  unfold decCol
  by_cases h0 : x = 0
  · subst h0; rfl
  · by_cases h1 : x = 1
    · subst h1; rfl
    · rw [if_neg h0, if_neg h1]
      have : ¬ x ≤ 1 := by
        intro hle
        rw [UInt64.le_iff_toNat_le] at hle
        have : x.toNat = 0 ∨ x.toNat = 1 := by simp at hle; omega
        rcases this with h | h
        · exact h0 (UInt64.toNat_inj.mp (by simpa using h))
        · exact h1 (UInt64.toNat_inj.mp (by simpa using h))
      simp [this, Col.done]

/-- **Final check.** -/
theorem fdone_iff {n k : Nat} (s : UInt64) (st : MState n) (h : Rel n k s st) :
    fdone n s = true ↔ (∀ j, (st.1 j).done = true) := by
  unfold fdone
  rw [List.all_eq_true]
  constructor
  · intro hall j
    rw [← h.2.1 j, decCol_done]
    exact hall j.val (List.mem_range.mpr j.isLt)
  · intro hall c hc
    have hc' := List.mem_range.mp hc
    have := hall ⟨c, hc'⟩
    rw [← h.2.1 ⟨c, hc'⟩, decCol_done] at this
    exact this

theorem rel_root (n k : Nat) : Rel n k 0 ((fun _ => .free, .free) : MState n) :=
  ⟨wf_root k n, fun j => by rw [getField_zero]; rfl, by rw [getField_zero]; rfl⟩

/-- **`Rel` is a simulation** of `mspec n k` by `fspec n k`. -/
theorem fspec_isSim {n k : Nat} (hk2 : 2 ≤ k) (hk : k ≤ 6) (hn : n ≤ 20) :
    (fspec n k).IsSim (mspec n k) (Rel n k) where
  root := rel_root n k
  step i hi s st a h :=
    fstep_rel hk2 hk (Nat.pos_of_ne_zero (by rintro rfl; simp at hi)) hn i s st h a
  final s st h := by
    show fdone n s = decide (∀ j, (st.1 j).done = true)
    rw [Bool.eq_iff_iff, fdone_iff s st h, decide_eq_true_iff]

end Tally.BarArray

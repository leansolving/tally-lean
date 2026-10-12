import Tally.Families.BarArray
import Tally.Families.BarArrayFront

/-!
# Acceptance of bar arrays by the frontier automaton

Proofs of `acceptsB_of_local` and `local_of_accepts`: a word is accepted by `mspec n k`
iff its array satisfies `IsBarArrayLocal k`. Via `isFront_front` and the generic
`Spec.accepts_iff_front`, the run is reduced to a per-cell condition `CellOK` plus a final
check on the last row, and both are related to the local characterization directly on the
total array.
-/

namespace Tally.BarArray

open Tally Tally.Grid

section Accept

variable {n k : Nat}

/-! ### Run lengths -/

theorem hlen_zero_of (g : Nat → Nat → Bool) {r c : Nat} (h : g r c = false) :
    hlen g r c = 0 := by
  cases c <;> simp [hlen, h]

theorem hlen_of_left (g : Nat → Nat → Bool) {r c : Nat} (hc : 0 < c) (h : g r c = true) :
    hlen g r c = hlen g r (c - 1) + 1 := by
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  simp [hlen, h]

theorem hlen_eq_one (g : Nat → Nat → Bool) {r c : Nat} (h : g r c = true)
    (hl : ¬ (0 < c ∧ g r (c - 1) = true)) : hlen g r c = 1 := by
  cases c with
  | zero => simp [hlen, h]
  | succ c =>
    have h' : g r c = false := by simpa using hl
    simp [hlen, h, hlen_zero_of g h']

theorem left_of_hlen_ne_one (g : Nat → Nat → Bool) {r c : Nat} (h : g r c = true)
    (h1 : hlen g r c ≠ 1) : 0 < c ∧ g r (c - 1) = true := by
  by_contra hl
  exact h1 (hlen_eq_one g h hl)

theorem vlen_zero_of (g : Nat → Nat → Bool) {r c : Nat} (h : g r c = false) :
    vlen g r c = 0 := by
  cases r <;> simp [vlen, h]

theorem vlen_of_above (g : Nat → Nat → Bool) {r c : Nat} (hr : 0 < r) (h : g r c = true) :
    vlen g r c = vlen g (r - 1) c + 1 := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simp [vlen, h]

theorem vlen_eq_one (g : Nat → Nat → Bool) {r c : Nat} (h : g r c = true)
    (ha : ¬ (0 < r ∧ g (r - 1) c = true)) : vlen g r c = 1 := by
  cases r with
  | zero => simp [vlen, h]
  | succ r =>
    have h' : g r c = false := by simpa using ha
    simp [vlen, h, vlen_zero_of g h']

/-! ### Run lengths are bounded by `k` in a local bar array -/

theorem hlen_le_of_local {g : Nat → Nat → Bool} (hg : ∀ r c, g r c = true → r < n ∧ c < n)
    (L : IsBarArrayLocal k g) : ∀ d r c, n ≤ c + d → IsHoriz g r c → hlen g r c ≤ k := by
  intro d
  induction d with
  | zero =>
    intro r c hd h
    have := (hg r c h.1).2
    omega
  | succ d ih =>
    intro r c hd h
    cases hr : g r (c + 1) with
    | false => exact le_of_eq ((L r c h.1).2.2.1 h hr)
    | true =>
      have h' : IsHoriz g r (c + 1) := ⟨hr, Or.inl ⟨Nat.succ_pos c, by simpa using h.1⟩⟩
      have h2 := ih r (c + 1) (by omega) h'
      have e : hlen g r (c + 1) = hlen g r c + 1 := by simp [hlen, hr]
      omega

theorem vlen_le_of_local {g : Nat → Nat → Bool} (hg : ∀ r c, g r c = true → r < n ∧ c < n)
    (L : IsBarArrayLocal k g) : ∀ d r c, n ≤ r + d → IsVert g r c → vlen g r c ≤ k := by
  intro d
  induction d with
  | zero =>
    intro r c hd h
    have := (hg r c h.1).1
    omega
  | succ d ih =>
    intro r c hd h
    cases hr : g (r + 1) c with
    | false => exact le_of_eq ((L r c h.1).2.2.2 h hr)
    | true =>
      have h' : IsVert g (r + 1) c := ⟨hr, Or.inl ⟨Nat.succ_pos r, by simpa using h.1⟩⟩
      have h2 := ih (r + 1) c (by omega) h'
      have e : vlen g (r + 1) c = vlen g r c + 1 := by simp [vlen, hr]
      omega

/-! ### The frontier entries -/

/-- The column entry describing the cell `(R - 1, j)` above row `R`. -/
def aboveEntry (k : Nat) (g : Nat → Nat → Bool) (R j : Nat) : Col :=
  if 0 < R then
    if g (R - 1) j = false then .free
    else if (0 < j ∧ g (R - 1) (j - 1) = true) ∨ g (R - 1) (j + 1) = true then .block
    else if vlen g (R - 1) j = k then .block else .vert (vlen g (R - 1) j)
  else .free

theorem colEntry_of_not_lt (g : Nat → Nat → Bool) {R C j : Nat} (h : ¬ j < C) :
    colEntry k g R C j = aboveEntry k g R j := by
  unfold colEntry aboveEntry
  rw [if_neg h]

theorem aboveEntry_eq_vert {g : Nat → Nat → Bool} {R j m : Nat}
    (h : aboveEntry k g R j = .vert m) :
    0 < R ∧ g (R - 1) j = true ∧
      ¬ ((0 < j ∧ g (R - 1) (j - 1) = true) ∨ g (R - 1) (j + 1) = true) ∧
      vlen g (R - 1) j ≠ k ∧ m = vlen g (R - 1) j := by
  unfold aboveEntry at h
  split_ifs at h with h1 h2 h3 h4
  injection h with h
  exact ⟨h1, by simpa using h2, h3, h4, h.symm⟩

theorem aboveEntry_eq_block {g : Nat → Nat → Bool} {R j : Nat}
    (h : aboveEntry k g R j = .block) :
    0 < R ∧ g (R - 1) j = true ∧
      (((0 < j ∧ g (R - 1) (j - 1) = true) ∨ g (R - 1) (j + 1) = true) ∨
        vlen g (R - 1) j = k) := by
  unfold aboveEntry at h
  split_ifs at h with h1 h2 h3 h4
  · exact ⟨h1, by simpa using h2, Or.inl h3⟩
  · exact ⟨h1, by simpa using h2, Or.inr h4⟩

theorem aboveEntry_of_vert {g : Nat → Nat → Bool} {R j : Nat} (hR : 0 < R)
    (h1 : g (R - 1) j = true)
    (h2 : ¬ ((0 < j ∧ g (R - 1) (j - 1) = true) ∨ g (R - 1) (j + 1) = true))
    (h3 : vlen g (R - 1) j ≠ k) : aboveEntry k g R j = .vert (vlen g (R - 1) j) := by
  unfold aboveEntry
  rw [if_pos hR, if_neg (by simp [h1]), if_neg h2, if_neg h3]

theorem aboveEntry_of_block {g : Nat → Nat → Bool} {R j : Nat} (hR : 0 < R)
    (h1 : g (R - 1) j = true)
    (h2 : ((0 < j ∧ g (R - 1) (j - 1) = true) ∨ g (R - 1) (j + 1) = true) ∨
        vlen g (R - 1) j = k) : aboveEntry k g R j = .block := by
  unfold aboveEntry
  rw [if_pos hR, if_neg (by simp [h1])]
  rcases h2 with h2 | h2
  · rw [if_pos h2]
  · by_cases h3 : (0 < j ∧ g (R - 1) (j - 1) = true) ∨ g (R - 1) (j + 1) = true
    · rw [if_pos h3]
    · rw [if_neg h3, if_pos h2]

theorem aboveEntry_of_free {g : Nat → Nat → Bool} {R j : Nat}
    (h : ¬ (0 < R ∧ g (R - 1) j = true)) : aboveEntry k g R j = .free := by
  unfold aboveEntry
  by_cases hR : 0 < R
  · rw [if_pos hR, if_pos (by simpa [hR] using h)]
  · rw [if_neg hR]

theorem aboveEntry_ne_free {g : Nat → Nat → Bool} {R j : Nat} (hR : 0 < R)
    (h1 : g (R - 1) j = true) : aboveEntry k g R j ≠ .free := by
  unfold aboveEntry
  rw [if_pos hR, if_neg (by simp [h1])]
  split_ifs <;> simp

theorem leftReg_eq_horiz {g : Nat → Nat → Bool} {R C m : Nat} (h : leftReg k g R C = .horiz m) :
    0 < C ∧ g R (C - 1) = true ∧ ¬ (0 < R ∧ g (R - 1) (C - 1) = true) ∧
      hlen g R (C - 1) ≠ 1 ∧ hlen g R (C - 1) ≠ k ∧ m = hlen g R (C - 1) := by
  unfold leftReg at h
  split_ifs at h with h1 h2 h3 h4 h5
  injection h with h
  exact ⟨Nat.pos_of_ne_zero h1, by simpa using h2, h3, h4, h5, h.symm⟩

theorem leftReg_eq_block {g : Nat → Nat → Bool} {R C : Nat} (h : leftReg k g R C = .block) :
    0 < C ∧ g R (C - 1) = true ∧
      ((0 < R ∧ g (R - 1) (C - 1) = true) ∨ hlen g R (C - 1) = k) := by
  unfold leftReg at h
  split_ifs at h with h1 h2 h3 h4 h5
  · exact ⟨Nat.pos_of_ne_zero h1, by simpa using h2, Or.inl h3⟩
  · exact ⟨Nat.pos_of_ne_zero h1, by simpa using h2, Or.inr h5⟩

theorem leftReg_eq_pend {g : Nat → Nat → Bool} {R C : Nat} (h : leftReg k g R C = .pend) :
    0 < C ∧ g R (C - 1) = true ∧ hlen g R (C - 1) = 1 := by
  unfold leftReg at h
  split_ifs at h with h1 h2 h3 h4
  exact ⟨Nat.pos_of_ne_zero h1, by simpa using h2, h4⟩

theorem leftReg_ne_free {g : Nat → Nat → Bool} {R C : Nat} (hC : 0 < C)
    (h1 : g R (C - 1) = true) : leftReg k g R C ≠ .free := by
  unfold leftReg
  rw [if_neg (by omega), if_neg (by simp [h1])]
  split_ifs <;> simp

theorem leftReg_of_horiz {g : Nat → Nat → Bool} {R C : Nat} (hC : 0 < C)
    (h1 : g R (C - 1) = true) (h2 : ¬ (0 < R ∧ g (R - 1) (C - 1) = true))
    (h3 : hlen g R (C - 1) ≠ 1) (h4 : hlen g R (C - 1) ≠ k) :
    leftReg k g R C = .horiz (hlen g R (C - 1)) := by
  unfold leftReg
  rw [if_neg (by omega), if_neg (by simp [h1]), if_neg h2, if_neg h3, if_neg h4]

theorem leftReg_of_block {g : Nat → Nat → Bool} {R C : Nat} (hk : 2 ≤ k) (hC : 0 < C)
    (h1 : g R (C - 1) = true)
    (h2 : (0 < R ∧ g (R - 1) (C - 1) = true) ∨ hlen g R (C - 1) = k) :
    leftReg k g R C = .block := by
  unfold leftReg
  rw [if_neg (by omega), if_neg (by simp [h1])]
  rcases h2 with h2 | h2
  · rw [if_pos h2]
  · by_cases h3 : 0 < R ∧ g (R - 1) (C - 1) = true
    · rw [if_pos h3]
    · rw [if_neg h3, if_neg (by omega), if_pos h2]

theorem leftReg_of_pend {g : Nat → Nat → Bool} {R C : Nat} (hC : 0 < C)
    (h1 : g R (C - 1) = true) (h2 : ¬ (0 < R ∧ g (R - 1) (C - 1) = true))
    (h3 : hlen g R (C - 1) = 1) : leftReg k g R C = .pend := by
  unfold leftReg
  rw [if_neg (by omega), if_neg (by simp [h1]), if_neg h2, if_pos h3]

theorem leftReg_of_free {g : Nat → Nat → Bool} {R C : Nat}
    (h : ¬ (0 < C ∧ g R (C - 1) = true)) : leftReg k g R C = .free := by
  unfold leftReg
  by_cases hC : C = 0
  · rw [if_pos hC]
  · rw [if_neg hC, if_pos (by simpa [Nat.pos_of_ne_zero hC] using h)]

theorem false_of_le_col {g : Nat → Nat → Bool} (hg : ∀ r c, g r c = true → r < n ∧ c < n)
    {r c : Nat} (hc : n ≤ c) : g r c = false := by
  cases h : g r c
  · rfl
  · have := (hg r c h).2
    omega

theorem false_of_le_row {g : Nat → Nat → Bool} (hg : ∀ r c, g r c = true → r < n ∧ c < n)
    {r c : Nat} (hr : n ≤ r) : g r c = false := by
  cases h : g r c
  · rfl
  · have := (hg r c h).1
    omega

/-! ### One step of the automaton as a per-cell condition -/

/-- `place` does not reject, and at a row end the new left register is not `horiz`. -/
def PlaceOK (k : Nat) (a : Col) (l : Left) (b : Bool) (last : Prop) : Prop :=
  if b then
    l ≠ .block ∧ a ≠ .block ∧ (∀ m, a = .vert m → l = .free) ∧
      (last → a = .free → l = .pend → k = 2) ∧
      (last → a = .free → ∀ m, l = .horiz m → m + 1 = k)
  else (∀ m, a ≠ .vert m) ∧ (∀ m, l ≠ .horiz m)

theorem placeOK_iff (a : Col) (l : Left) (b : Bool) (last : Prop) :
    PlaceOK k a l b last ↔
      (match place k a l (sym b) with
       | none => False
       | some (_, _, l') => (last → ∀ m, l' ≠ .horiz m)) := by
  cases a <;> cases l <;> cases b <;> simp [place, PlaceOK, sym] <;>
    split_ifs with hh <;> simp [hh]

theorem mstep_ne_none_iff' {i : Nat} (hc : i % n < n) (st : MState n) (s : Fin 2) :
    mstep n k i st s ≠ none ↔
      (match place k (st.1 ⟨i % n, hc⟩) st.2 s with
       | none => False
       | some (_, _, l') => (i % n + 1 = n → ∀ m, l' ≠ .horiz m)) := by
  unfold mstep
  rw [dif_pos hc]
  simp only
  rcases place k (st.1 ⟨i % n, hc⟩) st.2 s with _ | ⟨e, e', l'⟩
  · simp
  · simp only
    by_cases h : i % n + 1 = n
    · simp only [h, if_true]
      cases l' <;> simp
    · simp [h]

theorem mstep_ne_none_iff {i : Nat} (hc : i % n < n) (st : MState n) (b : Bool) :
    mstep n k i st (sym b) ≠ none ↔ PlaceOK k (st.1 ⟨i % n, hc⟩) st.2 b (i % n + 1 = n) := by
  rw [mstep_ne_none_iff', placeOK_iff]

/-- The per-cell condition: reading cell `(R, C)` from the described frontier does not reject. -/
def CellOK (n k : Nat) (g : Nat → Nat → Bool) (R C : Nat) : Prop :=
  PlaceOK k (aboveEntry k g R C) (leftReg k g R C) (g R C) (C + 1 = n)

theorem step_ne_none_iff_cellOK (hn : 0 < n) (w : Word (n * n) 2) (i : Nat) (hi : i < n * n) :
    mstep n k i (front n k (grid n (toArray n w)) i) (w ⟨i, hi⟩) ≠ none ↔
      CellOK n k (grid n (toArray n w)) (i / n) (i % n) := by
  rw [word_eq_sym w i hi, mstep_ne_none_iff (Nat.mod_lt i hn)]
  unfold CellOK
  have h1 : (front n k (grid n (toArray n w)) i).1 ⟨i % n, Nat.mod_lt i hn⟩ =
      aboveEntry k (grid n (toArray n w)) (i / n) (i % n) :=
    colEntry_of_not_lt _ (lt_irrefl _)
  rw [h1]
  rfl

theorem front_zero (g : Nat → Nat → Bool) : front n k g 0 = (mspec n k).root := by
  refine Prod.ext (funext fun j => ?_) ?_ <;> simp [front, colEntry, leftReg, mspec]

/-- `front` describes the run of the automaton on `w`. -/
theorem isFront_front (hn : 0 < n) (hk : 2 ≤ k) (w : Word (n * n) 2) :
    (mspec n k).IsFront w (front n k (grid n (toArray n w))) where
  zero := front_zero _
  step i hi st' h := front_step n k hn hk w i hi st' h

theorem acceptsB_iff (hn : 0 < n) (hk : 2 ≤ k) (w : Word (n * n) 2) :
    (mspec n k).acceptsB w = true ↔
      (∀ i (hi : i < n * n), (mspec n k).StepOK w (front n k (grid n (toArray n w))) i hi) ∧
        ∀ j : Fin n, ((front n k (grid n (toArray n w)) (n * n)).1 j).done = true := by
  rw [← Spec.Accepts, (mspec n k).accepts_iff_front (isFront_front hn hk w)]
  simp [mspec]

theorem forall_stepOK_iff (hn : 0 < n) (w : Word (n * n) 2) :
    (∀ i (hi : i < n * n), (mspec n k).StepOK w (front n k (grid n (toArray n w))) i hi) ↔
      ∀ R C, R < n → C < n → CellOK n k (grid n (toArray n w)) R C := by
  constructor
  · intro h R C hR hC
    have hi : n * R + C < n * n := by
      have := Nat.mul_le_mul_left n (show R + 1 ≤ n from hR)
      rw [Nat.mul_succ] at this
      omega
    have := (step_ne_none_iff_cellOK hn w _ hi).mp (h _ hi)
    rwa [Nat.mul_add_div hn, Nat.div_eq_of_lt hC, Nat.add_zero, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hC] at this
  · intro h j hj
    exact (step_ne_none_iff_cellOK hn w j hj).mpr
      (h _ _ (div_lt_of_lt_mul n hn hj) (Nat.mod_lt j hn))

theorem front_final_iff (hn : 0 < n) (g : Nat → Nat → Bool) :
    (∀ j : Fin n, ((front n k g (n * n)).1 j).done = true) ↔
      ∀ j, j < n → (aboveEntry k g n j).done = true := by
  have h1 : n * n / n = n := Nat.mul_div_cancel n hn
  have h2 : n * n % n = 0 := Nat.mul_mod_left n n
  have e : ∀ j : Fin n, (front n k g (n * n)).1 j = aboveEntry k g n j.val := by
    intro j
    show colEntry k g (n * n / n) (n * n % n) j.val = _
    rw [h1, h2]
    exact colEntry_of_not_lt g (Nat.not_lt_zero _)
  simp only [e]
  exact ⟨fun h j hj => h ⟨j, hj⟩, fun h j => h j.val j.isLt⟩

/-! ### Local bar arrays pass every step -/

theorem cellOK_of_local {g : Nat → Nat → Bool}
    (hg : ∀ r c, g r c = true → r < n ∧ c < n) (L : IsBarArrayLocal k g)
    {R C : Nat} : CellOK n k g R C := by
  unfold CellOK PlaceOK
  cases hG : g R C
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun m hv => ?_, fun m hl => ?_⟩
    · obtain ⟨hR0, h1, h2, h3, -⟩ := aboveEntry_eq_vert hv
      have hL := L (R - 1) C h1
      have hv' : IsVert g (R - 1) C := hL.1.resolve_left (fun h => h2 h.2)
      have hb : g (R - 1 + 1) C = false := by rw [Nat.sub_add_cancel hR0]; exact hG
      exact h3 (hL.2.2.2 hv' hb)
    · obtain ⟨hC0, h1, -, h3, h4, -⟩ := leftReg_eq_horiz hl
      have hL := L R (C - 1) h1
      have hh : IsHoriz g R (C - 1) := ⟨h1, Or.inl (left_of_hlen_ne_one g h1 h3)⟩
      have hb : g R (C - 1 + 1) = false := by rw [Nat.sub_add_cancel hC0]; exact hG
      exact h4 (hL.2.2.1 hh hb)
  · simp only [↓reduceIte]
    have hLc := L R C hG
    refine ⟨fun hl => ?_, fun ha => ?_, fun m ha => ?_, fun hlast _ hl => ?_,
      fun hlast _ m hl => ?_⟩
    · obtain ⟨hC0, h1, h2⟩ := leftReg_eq_block hl
      have hL := L R (C - 1) h1
      rcases h2 with h2 | h2
      · apply hL.2.1
        refine ⟨⟨h1, Or.inr ?_⟩, ⟨h1, Or.inl h2⟩⟩
        rw [Nat.sub_add_cancel hC0]
        exact hG
      · have e := hlen_of_left g hC0 hG
        have hh : IsHoriz g R C := ⟨hG, Or.inl ⟨hC0, h1⟩⟩
        have := hlen_le_of_local hg L n R C (by omega) hh
        omega
    · obtain ⟨hR0, h1, h2⟩ := aboveEntry_eq_block ha
      have hL := L (R - 1) C h1
      rcases h2 with h2 | h2
      · apply hL.2.1
        refine ⟨⟨h1, h2⟩, ⟨h1, Or.inr ?_⟩⟩
        rw [Nat.sub_add_cancel hR0]
        exact hG
      · have e := vlen_of_above g hR0 hG
        have hv : IsVert g R C := ⟨hG, Or.inl ⟨hR0, h1⟩⟩
        have := vlen_le_of_local hg L n R C (by omega) hv
        omega
    · obtain ⟨hR0, h1, -⟩ := aboveEntry_eq_vert ha
      by_contra hl
      have hl' : 0 < C ∧ g R (C - 1) = true := by
        by_contra hc
        exact hl (leftReg_of_free hc)
      exact hLc.2.1 ⟨⟨hG, Or.inl hl'⟩, ⟨hG, Or.inl ⟨hR0, h1⟩⟩⟩
    · obtain ⟨hC0, h1, h2⟩ := leftReg_eq_pend hl
      have e := hlen_of_left g hC0 hG
      have hb : g R (C + 1) = false := false_of_le_col hg (by omega)
      have := hLc.2.2.1 ⟨hG, Or.inl ⟨hC0, h1⟩⟩ hb
      omega
    · obtain ⟨hC0, h1, -, -, -, hm⟩ := leftReg_eq_horiz hl
      have e := hlen_of_left g hC0 hG
      have hb : g R (C + 1) = false := false_of_le_col hg (by omega)
      have := hLc.2.2.1 ⟨hG, Or.inl ⟨hC0, h1⟩⟩ hb
      omega

theorem final_of_local {g : Nat → Nat → Bool}
    (hg : ∀ r c, g r c = true → r < n ∧ c < n) (L : IsBarArrayLocal k g)
    {j : Nat} : (aboveEntry k g n j).done = true := by
  rcases hv : aboveEntry k g n j with _ | _ | m
  · rfl
  · rfl
  · exfalso
    obtain ⟨hn, h1, h2, h3, -⟩ := aboveEntry_eq_vert hv
    have hL := L (n - 1) j h1
    have hv' : IsVert g (n - 1) j := hL.1.resolve_left (fun h => h2 h.2)
    have hb : g (n - 1 + 1) j = false := false_of_le_row hg (by omega)
    exact h3 (hL.2.2.2 hv' hb)

/-! ### Passing every step gives a local bar array -/

section FromOK

variable {g : Nat → Nat → Bool} (H : ∀ R C, R < n → C < n → CellOK n k g R C)
include H

/-- At a zero cell, a pending vertical run above must have length `k`. -/
theorem vlen_eq_of_ok_zero {R C : Nat} (hR : R < n) (hC : C < n) (hG : g R C = false)
    (hR0 : 0 < R) (h1 : g (R - 1) C = true)
    (h2 : ¬ ((0 < C ∧ g (R - 1) (C - 1) = true) ∨ g (R - 1) (C + 1) = true)) :
    vlen g (R - 1) C = k := by
  by_contra h3
  have hok := H R C hR hC
  unfold CellOK PlaceOK at hok
  simp only [hG, Bool.false_eq_true, ↓reduceIte] at hok
  exact hok.1 _ (aboveEntry_of_vert hR0 h1 h2 h3)

/-- At a zero cell, a horizontal run to the left of length `≥ 2` must have length `k`. -/
theorem hlen_eq_of_ok_zero {R C : Nat} (hR : R < n) (hC : C < n) (hG : g R C = false)
    (hC0 : 0 < C) (h1 : g R (C - 1) = true) (h2 : ¬ (0 < R ∧ g (R - 1) (C - 1) = true))
    (h3 : hlen g R (C - 1) ≠ 1) : hlen g R (C - 1) = k := by
  by_contra h4
  have hok := H R C hR hC
  unfold CellOK PlaceOK at hok
  simp only [hG, Bool.false_eq_true, ↓reduceIte] at hok
  exact hok.2 _ (leftReg_of_horiz hC0 h1 h2 h3 h4)

theorem ok_one {R C : Nat} (hR : R < n) (hC : C < n) (hG : g R C = true) :
    leftReg k g R C ≠ .block ∧ aboveEntry k g R C ≠ .block ∧
      (∀ m, aboveEntry k g R C = .vert m → leftReg k g R C = .free) ∧
      (C + 1 = n → aboveEntry k g R C = .free → leftReg k g R C = .pend → k = 2) ∧
      (C + 1 = n → aboveEntry k g R C = .free → ∀ m, leftReg k g R C = .horiz m → m + 1 = k) := by
  have hok := H R C hR hC
  unfold CellOK PlaceOK at hok
  simp only [hG, ↓reduceIte] at hok
  exact hok

/-- A one with a one to its left: the left one has no one above and its run is shorter than `k`. -/
theorem ok_one_left (hk : 2 ≤ k) {R C : Nat} (hR : R < n) (hC : C < n) (hG : g R C = true)
    (hC0 : 0 < C) (h1 : g R (C - 1) = true) :
    ¬ (0 < R ∧ g (R - 1) (C - 1) = true) ∧ hlen g R (C - 1) ≠ k := by
  have hok := (ok_one H hR hC hG).1
  exact ⟨fun h => hok (leftReg_of_block hk hC0 h1 (Or.inl h)),
    fun h => hok (leftReg_of_block hk hC0 h1 (Or.inr h))⟩

/-- A one with a one above: the upper one has no horizontal neighbour and its run is shorter
than `k`. -/
theorem ok_one_above {R C : Nat} (hR : R < n) (hC : C < n) (hG : g R C = true)
    (hR0 : 0 < R) (h1 : g (R - 1) C = true) :
    ¬ ((0 < C ∧ g (R - 1) (C - 1) = true) ∨ g (R - 1) (C + 1) = true) ∧
      vlen g (R - 1) C ≠ k := by
  have hok := (ok_one H hR hC hG).2.1
  exact ⟨fun h => hok (aboveEntry_of_block hR0 h1 (Or.inl h)),
    fun h => hok (aboveEntry_of_block hR0 h1 (Or.inr h))⟩

/-- A one with a one above has no one to its left. -/
theorem ok_one_above_left {R C : Nat} (hR : R < n) (hC : C < n) (hG : g R C = true)
    (hR0 : 0 < R) (h1 : g (R - 1) C = true) : ¬ (0 < C ∧ g R (C - 1) = true) := by
  rintro ⟨hC0, hl⟩
  have hok := ok_one H hR hC hG
  rcases ha : aboveEntry k g R C with _ | _ | m
  · exact aboveEntry_ne_free hR0 h1 ha
  · exact hok.2.1 ha
  · exact leftReg_ne_free hC0 hl (hok.2.2.1 m ha)

/-- At the end of a row, a horizontal run has length `k`. -/
theorem hlen_eq_of_ok_last {R C : Nat} (hk : 2 ≤ k) (hR : R < n) (hC : C < n)
    (hG : g R C = true) (hlast : C + 1 = n) (hC0 : 0 < C) (h1 : g R (C - 1) = true) :
    hlen g R C = k := by
  obtain ⟨hna, hnk⟩ := ok_one_left H hk hR hC hG hC0 h1
  have hok := ok_one H hR hC hG
  have ha : aboveEntry k g R C = .free :=
    aboveEntry_of_free (fun h => ok_one_above_left H hR hC hG h.1 h.2 ⟨hC0, h1⟩)
  have e := hlen_of_left g hC0 hG
  by_cases h3 : hlen g R (C - 1) = 1
  · have := hok.2.2.2.1 hlast ha (leftReg_of_pend hC0 h1 hna h3)
    omega
  · have := hok.2.2.2.2 hlast ha _ (leftReg_of_horiz hC0 h1 hna h3 hnk)
    omega

end FromOK

theorem local_of_cellOK (hk : 2 ≤ k) {g : Nat → Nat → Bool}
    (hg : ∀ r c, g r c = true → r < n ∧ c < n)
    (H : ∀ R C, R < n → C < n → CellOK n k g R C)
    (F : ∀ j, j < n → (aboveEntry k g n j).done = true) : IsBarArrayLocal k g := by
  -- a one without horizontal neighbour and with a zero below closes a vertical run of length `k`
  have V : ∀ r c, g r c = true → ¬ ((0 < c ∧ g r (c - 1) = true) ∨ g r (c + 1) = true) →
      g (r + 1) c = false → vlen g r c = k := by
    intro r c hrc hnh hbl
    have hb := hg r c hrc
    by_cases hr1 : r + 1 < n
    · exact vlen_eq_of_ok_zero H hr1 hb.2 hbl (Nat.succ_pos r) hrc hnh
    · have hr : r = n - 1 := by omega
      subst hr
      by_contra h3
      have := F c hb.2
      rw [aboveEntry_of_vert (by omega) hrc hnh h3] at this
      simp [Col.done] at this
  intro r c hrc
  have hb := hg r c hrc
  have P2 : ¬ (IsHoriz g r c ∧ IsVert g r c) := by
    rintro ⟨⟨_, hl | hr⟩, ⟨_, ha | hbl⟩⟩
    · exact ok_one_above_left H hb.1 hb.2 hrc ha.1 ha.2 hl
    · have hb1 := hg _ _ hbl
      exact (ok_one_above H hb1.1 hb1.2 hbl (Nat.succ_pos r) hrc).1 (Or.inl hl)
    · have hb1 := hg _ _ hr
      exact (ok_one_left H hk hb1.1 hb1.2 hr (Nat.succ_pos c) hrc).1 ha
    · have hb1 := hg _ _ hbl
      exact (ok_one_above H hb1.1 hb1.2 hbl (Nat.succ_pos r) hrc).1 (Or.inr hr)
  refine ⟨?_, P2, ?_, ?_⟩
  · by_contra hno
    have hnh : ¬ ((0 < c ∧ g r (c - 1) = true) ∨ g r (c + 1) = true) :=
      fun h => hno (Or.inl ⟨hrc, h⟩)
    have hna : ¬ (0 < r ∧ g (r - 1) c = true) := fun h => hno (Or.inr ⟨hrc, Or.inl h⟩)
    have hnb : g (r + 1) c = false := by
      cases h : g (r + 1) c
      · rfl
      · exact absurd (Or.inr ⟨hrc, Or.inr h⟩) hno
    have := V r c hrc hnh hnb
    rw [vlen_eq_one g hrc hna] at this
    omega
  · intro hh hr
    obtain ⟨hc0, hl⟩ : 0 < c ∧ g r (c - 1) = true := by
      rcases hh.2 with h | h
      · exact h
      · rw [hr] at h
        cases h
    have hna : ¬ (0 < r ∧ g (r - 1) c = true) := fun h => P2 ⟨hh, ⟨hrc, Or.inl h⟩⟩
    by_cases hc1 : c + 1 = n
    · exact hlen_eq_of_ok_last H hk hb.1 hb.2 hrc hc1 hc0 hl
    · have hc1' : c + 1 < n := by omega
      have e := hlen_of_left g hc0 hrc
      have hp := hlen_pos g _ _ hl
      exact hlen_eq_of_ok_zero H hb.1 hc1' hr (Nat.succ_pos c) hrc hna
        (show hlen g r c ≠ 1 by omega)
  · intro hv hbl
    exact V r c hrc (fun h => P2 ⟨⟨hrc, h⟩, hv⟩) hbl

end Accept

/-- A bar array is accepted. -/
theorem acceptsB_of_local (n k : Nat) (hk : 2 ≤ k) (w : Word (n * n) 2)
    (h : IsBarArrayLocal k (grid n (toArray n w))) : (mspec n k).acceptsB w = true := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Spec.acceptsB, Spec.acceptsFrom, List.ofFn_zero, mspec]
  · rw [acceptsB_iff hn hk, forall_stepOK_iff hn, front_final_iff hn]
    exact ⟨fun _ _ _ _ => cellOK_of_local (fun r c => grid_lt) h,
      fun _ _ => final_of_local (fun r c => grid_lt) h⟩

/-- An accepted word is a bar array. -/
theorem local_of_accepts (n k : Nat) (hk : 2 ≤ k) (w : Word (n * n) 2)
    (h : (mspec n k).acceptsB w = true) : IsBarArrayLocal k (grid n (toArray n w)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    intro r c hrc
    exact absurd (grid_lt hrc).1 (Nat.not_lt_zero r)
  · rw [acceptsB_iff hn hk, forall_stepOK_iff hn, front_final_iff hn] at h
    exact local_of_cellOK hk (fun r c => grid_lt) h.1 h.2

end Tally.BarArray

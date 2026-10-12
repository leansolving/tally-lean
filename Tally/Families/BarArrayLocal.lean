import Tally.Families.BarArray

/-!
# The local characterization of bar arrays

`isBarArrayLocal_iff : IsBarArrayLocal k (grid n f) ↔ IsBarArray n k f` for `k ≥ 2`.

The proof works on total grids `g : Nat → Nat → Bool` and coordinate pairs. The vertical case
is reduced to the horizontal one by transposing the grid (`transp`) and the bars (`Bar.tr`).
-/

namespace Tally.BarArray

open Tally Tally.Grid

/-! ### Run lengths -/

/-- Transposed grid. -/
def transp (g : Nat → Nat → Bool) : Nat → Nat → Bool := fun a b => g b a

theorem transp_transp (g : Nat → Nat → Bool) : transp (transp g) = g := rfl

theorem vlen_eq_hlen (g : Nat → Nat → Bool) (r c : Nat) : vlen g r c = hlen (transp g) c r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [vlen, hlen, ih]; rfl

theorem hlen_transp (g : Nat → Nat → Bool) (r c : Nat) : hlen (transp g) c r = vlen g r c :=
  (vlen_eq_hlen g r c).symm

theorem vlen_transp (g : Nat → Nat → Bool) (r c : Nat) : vlen (transp g) c r = hlen g r c := by
  rw [vlen_eq_hlen, transp_transp]

/-- The run ending at `(r, c)`: its length is at most `c + 1`, all its cells are ones, and the
cell before it (if any) is a zero. -/
theorem hlen_spec (g : Nat → Nat → Bool) (r c : Nat) :
    hlen g r c ≤ c + 1 ∧ (∀ j, c + 1 - hlen g r c ≤ j → j ≤ c → g r j = true) ∧
      (hlen g r c ≤ c → g r (c - hlen g r c) = false) := by
  induction c with
  | zero =>
    cases h : g r 0
    · refine ⟨by simp [hlen, h], fun j h1 h2 => by simp [hlen, h] at h1; omega,
        fun _ => by simp [hlen, h]⟩
    · refine ⟨by simp [hlen, h], fun j _ hj => ?_, fun h' => by simp [hlen, h] at h'⟩
      rw [Nat.le_zero.mp hj]; exact h
  | succ c ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    cases h : g r (c + 1)
    · refine ⟨by simp [hlen, h], fun j h1 h2 => by simp [hlen, h] at h1; omega,
        fun _ => by simp [hlen, h]⟩
    · have e : hlen g r (c + 1) = hlen g r c + 1 := by simp [hlen, h]
      rw [e]
      refine ⟨by omega, fun j hj1 hj2 => ?_, fun h' => ?_⟩
      · rcases Nat.lt_or_ge j (c + 1) with hj | hj
        · exact ih2 j (by omega) (by omega)
        · rw [show j = c + 1 by omega]; exact h
      · have := ih3 (by omega)
        rwa [show c + 1 - (hlen g r c + 1) = c - hlen g r c by omega]

/-- A maximal-to-the-left run of ones from `c0` to `c` has `hlen = c + 1 - c0`. -/
theorem hlen_eq_of_run (g : Nat → Nat → Bool) (r c0 c : Nat) (hc : c0 ≤ c)
    (hones : ∀ j, c0 ≤ j → j ≤ c → g r j = true) (hstart : c0 = 0 ∨ g r (c0 - 1) = false) :
    hlen g r c = c + 1 - c0 := by
  induction c with
  | zero =>
    have h0 : c0 = 0 := by omega
    subst h0
    simp [hlen, hones 0 le_rfl le_rfl]
  | succ c ih =>
    have h1 : g r (c + 1) = true := hones (c + 1) hc le_rfl
    simp only [hlen, h1, if_true]
    rcases Nat.lt_or_ge c c0 with h | h
    · have e : c0 = c + 1 := by omega
      subst e
      have hz : g r c = false := by
        rcases hstart with h' | h'
        · omega
        · simpa using h'
      have : hlen g r c = 0 := by
        cases c with
        | zero => simp [hlen, hz]
        | succ c => simp [hlen, hz]
      omega
    · rw [ih h (fun j h1 h2 => hones j h1 (by omega))]
      omega

/-! ### Coordinates -/

/-- Grid adjacency on coordinate pairs. -/
def NAdj (a c a' c' : Nat) : Prop :=
  (a = a' ∧ (c + 1 = c' ∨ c' + 1 = c)) ∨ (c = c' ∧ (a + 1 = a' ∨ a' + 1 = a))

theorem nadj_swap (a c a' c' : Nat) : NAdj c a c' a' ↔ NAdj a c a' c' := by
  unfold NAdj; tauto

theorem adj_iff_nadj (n : Nat) (u w : V n) :
    Adj n u w ↔ NAdj u.1.val u.2.val w.1.val w.2.val := by
  unfold Adj NAdj
  simp only [Fin.ext_iff]

theorem mem_cells_true (k a b r c : Nat) :
    (a, b) ∈ Bar.cells k ⟨true, r, c⟩ ↔ a = r ∧ c ≤ b ∧ b < c + k := by
  simp only [Bar.cells, List.mem_map, List.mem_range, if_true, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, h1, h2⟩; omega
  · rintro ⟨h1, h2, h3⟩; exact ⟨b - c, by omega, h1.symm, by omega⟩

theorem mem_cells_false (k a b r c : Nat) :
    (a, b) ∈ Bar.cells k ⟨false, r, c⟩ ↔ b = c ∧ r ≤ a ∧ a < r + k := by
  simp only [Bar.cells, List.mem_map, List.mem_range, Bool.false_eq_true, if_false,
    Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, h1, h2⟩; omega
  · rintro ⟨h1, h2, h3⟩; exact ⟨a - r, by omega, by omega, h1.symm⟩

/-- Transposed bar. -/
def Bar.tr (b : Bar) : Bar := ⟨!b.horizontal, b.c, b.r⟩

theorem Bar.tr_tr (b : Bar) : b.tr.tr = b := by
  cases b; simp [Bar.tr]

theorem mem_cells_tr (k a c : Nat) (b : Bar) :
    (a, c) ∈ Bar.cells k b.tr ↔ (c, a) ∈ Bar.cells k b := by
  obtain ⟨h, r, c'⟩ := b
  cases h <;> simp only [Bar.tr, Bool.not_false, Bool.not_true, mem_cells_true, mem_cells_false]

/-- The bar property on coordinates. -/
def BarOK (k : Nat) (g : Nat → Nat → Bool) (b : Bar) : Prop :=
  (∀ a c, (a, c) ∈ Bar.cells k b → g a c = true) ∧
  (∀ a c a' c', (a, c) ∈ Bar.cells k b → NAdj a c a' c' → g a' c' = true →
    (a', c') ∈ Bar.cells k b)

theorem barOK_tr {k : Nat} {g : Nat → Nat → Bool} {b : Bar} (h : BarOK k g b) :
    BarOK k (transp g) b.tr := by
  refine ⟨fun a c hm => h.1 c a ((mem_cells_tr k a c b).mp hm), fun a c a' c' hm hadj hg => ?_⟩
  rw [mem_cells_tr] at hm ⊢
  exact h.2 c a c' a' hm ((nadj_swap a c a' c').mpr hadj) hg

/-- The coordinate version of `IsBarArray`. -/
def BarProp (k : Nat) (g : Nat → Nat → Bool) : Prop :=
  ∀ r c, g r c = true → ∃ b : Bar, (r, c) ∈ Bar.cells k b ∧ BarOK k g b

/-- The local condition at one cell. -/
def LocalAt (k : Nat) (g : Nat → Nat → Bool) (r c : Nat) : Prop :=
  (IsHoriz g r c ∨ IsVert g r c) ∧ ¬ (IsHoriz g r c ∧ IsVert g r c) ∧
    (IsHoriz g r c → g r (c + 1) = false → hlen g r c = k) ∧
    (IsVert g r c → g (r + 1) c = false → vlen g r c = k)

theorem localAt_transp (k : Nat) (g : Nat → Nat → Bool) (r c : Nat) :
    LocalAt k (transp g) c r ↔ LocalAt k g r c := by
  unfold LocalAt
  rw [hlen_transp, vlen_transp]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1.symm, fun h => h2 ⟨h.2, h.1⟩, h4, h3⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1.symm, fun h => h2 ⟨h.2, h.1⟩, h4, h3⟩

/-! ### The horizontal case -/

/-- (→) A horizontal one lies in a horizontal bar with the bar property. -/
theorem horiz_bar (k : Nat) (hk : 2 ≤ k) (g : Nat → Nat → Bool) (N : Nat)
    (hN : ∀ r c, g r c = true → c < N) (hloc : ∀ r c, g r c = true → LocalAt k g r c)
    (r c : Nat) (hrc : g r c = true) (hh : IsHoriz g r c) :
    ∃ b : Bar, (r, c) ∈ Bar.cells k b ∧ BarOK k g b := by
  classical
  have hex : ∃ j, c ≤ j ∧ g r (j + 1) = false := by
    refine ⟨max c N, le_max_left _ _, ?_⟩
    cases h : g r (max c N + 1)
    · rfl
    · exact absurd (hN _ _ h) (by omega)
  obtain ⟨hc1, hf1⟩ := Nat.find_spec hex
  have hmin : ∀ j, c ≤ j → j < Nat.find hex → g r (j + 1) = true := by
    intro j h1 h2
    have := Nat.find_min hex h2
    cases h : g r (j + 1)
    · exact absurd ⟨h1, h⟩ this
    · rfl
  set c1 := Nat.find hex with hc1def
  have hones : ∀ j, c ≤ j → j ≤ c1 → g r j = true := by
    intro j h1 h2
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · rw [← h]; exact hrc
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact hmin j' (by omega) (by omega)
  have hg1 : g r c1 = true := hones c1 hc1 le_rfl
  have hh1 : IsHoriz g r c1 := by
    rcases Nat.eq_or_lt_of_le hc1 with h | h
    · rw [← h]; exact hh
    · exact ⟨hg1, Or.inl ⟨by omega, hones _ (by omega) (by omega)⟩⟩
  have hlen1 : hlen g r c1 = k := (hloc r c1 hg1).2.2.1 hh1 hf1
  obtain ⟨hle, hrun, hleft⟩ := hlen_spec g r c1
  rw [hlen1] at hle hrun hleft
  refine ⟨⟨true, r, c1 + 1 - k⟩, ?_, ?_, ?_⟩
  · rw [mem_cells_true]
    refine ⟨rfl, ?_, by omega⟩
    by_contra hlt
    have h1 := hleft (by omega)
    rw [hones (c1 - k) (by omega) (by omega)] at h1
    exact Bool.noConfusion h1
  · intro a b hm
    rw [mem_cells_true] at hm
    obtain ⟨rfl, h1, h2⟩ := hm
    exact hrun b (by omega) (by omega)
  · intro a b a' b' hm hadj hg
    rw [mem_cells_true] at hm ⊢
    obtain ⟨rfl, h1, h2⟩ := hm
    rcases hadj with ⟨rfl, h | h⟩ | ⟨rfl, h⟩
    · refine ⟨rfl, by omega, ?_⟩
      by_contra hlt
      have e : b' = c1 + 1 := by omega
      rw [e, hf1] at hg
      exact Bool.noConfusion hg
    · refine ⟨rfl, ?_, by omega⟩
      by_contra hlt
      have h3 := hleft (by omega)
      rw [show c1 - k = b' by omega, hg] at h3
      exact Bool.noConfusion h3
    · exfalso
      have hb : g a b = true := hrun b (by omega) (by omega)
      have hhb : IsHoriz g a b := by
        refine ⟨hb, ?_⟩
        rcases Nat.lt_or_ge b c1 with h' | h'
        · exact Or.inr (hrun (b + 1) (by omega) (by omega))
        · exact Or.inl ⟨by omega, hrun (b - 1) (by omega) (by omega)⟩
      have hvb : IsVert g a b := by
        refine ⟨hb, ?_⟩
        rcases h with h | h
        · subst h; exact Or.inr hg
        · subst h; exact Or.inl ⟨by omega, by simpa using hg⟩
      exact (hloc a b hb).2.1 ⟨hhb, hvb⟩

/-- (←) A cell of a horizontal bar with the bar property satisfies the local condition. -/
theorem horiz_local (k : Nat) (hk : 2 ≤ k) (g : Nat → Nat → Bool) (r0 c0 r c : Nat)
    (hmem : (r, c) ∈ Bar.cells k ⟨true, r0, c0⟩) (hok : BarOK k g ⟨true, r0, c0⟩) :
    LocalAt k g r c := by
  rw [mem_cells_true] at hmem
  obtain ⟨rfl, h1, h2⟩ := hmem
  have hin : ∀ j, c0 ≤ j → j < c0 + k → g r j = true := fun j h1 h2 =>
    hok.1 r j ((mem_cells_true k r j r c0).mpr ⟨rfl, h1, h2⟩)
  have hmemc : (r, c) ∈ Bar.cells k ⟨true, r, c0⟩ := (mem_cells_true k r c r c0).mpr ⟨rfl, h1, h2⟩
  have hnv : ¬ IsVert g r c := by
    rintro ⟨_, ⟨h0, h⟩ | h⟩
    · have := hok.2 r c (r - 1) c hmemc (Or.inr ⟨rfl, Or.inr (by omega)⟩) h
      rw [mem_cells_true] at this
      omega
    · have := hok.2 r c (r + 1) c hmemc (Or.inr ⟨rfl, Or.inl rfl⟩) h
      rw [mem_cells_true] at this
      omega
  have hh : IsHoriz g r c := by
    refine ⟨hin c h1 h2, ?_⟩
    rcases Nat.lt_or_ge (c + 1) (c0 + k) with h' | h'
    · exact Or.inr (hin (c + 1) (by omega) h')
    · exact Or.inl ⟨by omega, hin (c - 1) (by omega) (by omega)⟩
  refine ⟨Or.inl hh, fun h => hnv h.2, fun _ hf => ?_, fun h => absurd h hnv⟩
  have hc : c + 1 = c0 + k := by
    by_contra hne
    rw [hin (c + 1) (by omega) (by omega)] at hf
    exact Bool.noConfusion hf
  have hstart : c0 = 0 ∨ g r (c0 - 1) = false := by
    rcases Nat.eq_zero_or_pos c0 with h0 | h0
    · exact Or.inl h0
    · right
      cases hg : g r (c0 - 1)
      · rfl
      · have := hok.2 r c0 r (c0 - 1) ((mem_cells_true k r c0 r c0).mpr ⟨rfl, le_rfl, by omega⟩)
          (Or.inl ⟨rfl, Or.inr (by omega)⟩) hg
        rw [mem_cells_true] at this
        omega
  rw [hlen_eq_of_run g r c0 c h1 (fun j h1 h2 => hin j h1 (by omega)) hstart]
  omega

/-! ### Assembly -/

theorem local_iff_barProp (k : Nat) (hk : 2 ≤ k) (g : Nat → Nat → Bool) (N : Nat)
    (hb : ∀ r c, g r c = true → r < N ∧ c < N) :
    (∀ r c, g r c = true → LocalAt k g r c) ↔ BarProp k g := by
  constructor
  · intro hloc r c hrc
    rcases (hloc r c hrc).1 with hh | hv
    · exact horiz_bar k hk g N (fun r c h => (hb r c h).2) hloc r c hrc hh
    · have hlocT : ∀ r c, transp g r c = true → LocalAt k (transp g) r c :=
        fun r c h => (localAt_transp k g c r).mpr (hloc c r h)
      obtain ⟨b, hm, hok⟩ :=
        horiz_bar k hk (transp g) N (fun r c h => (hb c r h).1) hlocT c r hrc hv
      refine ⟨b.tr, (mem_cells_tr k r c b).mpr hm, ?_⟩
      have := barOK_tr hok
      rwa [transp_transp] at this
  · intro hbp r c hrc
    obtain ⟨⟨h, r0, c0⟩, hm, hok⟩ := hbp r c hrc
    cases h
    · have hm' : (c, r) ∈ Bar.cells k ⟨true, c0, r0⟩ :=
        (mem_cells_tr k c r ⟨false, r0, c0⟩).mpr hm
      exact (localAt_transp k g r c).mp (horiz_local k hk (transp g) c0 r0 c r hm' (barOK_tr hok))
    · exact horiz_local k hk g r0 c0 r c hm hok

theorem onBoard_cells {n k : Nat} {b : Bar} (hon : Bar.OnBoard n k b) {a c : Nat}
    (hm : (a, c) ∈ Bar.cells k b) : a < n ∧ c < n := by
  obtain ⟨h, r0, c0⟩ := b
  cases h
  · simp only [Bar.OnBoard, Bool.false_eq_true, if_false] at hon
    rw [mem_cells_false] at hm
    omega
  · simp only [Bar.OnBoard, if_true] at hon
    rw [mem_cells_true] at hm
    omega

theorem onBoard_of_cells {n k : Nat} (hk : 1 ≤ k) {b : Bar}
    (h : ∀ a c, (a, c) ∈ Bar.cells k b → a < n ∧ c < n) : Bar.OnBoard n k b := by
  obtain ⟨hz, r0, c0⟩ := b
  cases hz
  · have h0 := h r0 c0 ((mem_cells_false k r0 c0 r0 c0).mpr ⟨rfl, le_rfl, by omega⟩)
    have h1 := h (r0 + k - 1) c0 ((mem_cells_false k _ c0 r0 c0).mpr ⟨rfl, by omega, by omega⟩)
    simp only [Bar.OnBoard, Bool.false_eq_true, if_false]
    omega
  · have h0 := h r0 c0 ((mem_cells_true k r0 c0 r0 c0).mpr ⟨rfl, le_rfl, by omega⟩)
    have h1 := h r0 (c0 + k - 1) ((mem_cells_true k r0 _ r0 c0).mpr ⟨rfl, by omega, by omega⟩)
    simp only [Bar.OnBoard, if_true]
    omega

theorem isBarArray_iff_barProp (n k : Nat) (hk : 1 ≤ k) (f : V n → Bool) :
    IsBarArray n k f ↔ BarProp k (grid n f) := by
  constructor
  · intro h r c hrc
    obtain ⟨hr, hc⟩ := grid_lt hrc
    obtain ⟨b, hon, hmem, hones, hcl⟩ := h (⟨r, hr⟩, ⟨c, hc⟩) (by rw [← grid_mk f hr hc]; exact hrc)
    refine ⟨b, hmem, fun a c' hm => ?_, fun a c' a' c'' hm hadj hg => ?_⟩
    · obtain ⟨ha, hc'⟩ := onBoard_cells hon hm
      rw [grid_mk f ha hc']
      exact hones _ hm
    · obtain ⟨ha, hc'⟩ := onBoard_cells hon hm
      obtain ⟨ha', hc''⟩ := grid_lt hg
      exact hcl (⟨a, ha⟩, ⟨c', hc'⟩) (⟨a', ha'⟩, ⟨c'', hc''⟩) hm
        ((adj_iff_nadj n _ _).mpr hadj) (by rw [← grid_mk f ha' hc'']; exact hg)
  · intro h v hv
    obtain ⟨b, hm, hones, hcl⟩ := h v.1.val v.2.val (by rw [grid_val]; exact hv)
    refine ⟨b, onBoard_of_cells hk (fun a c hm => grid_lt (hones a c hm)), hm,
      fun u hu => ?_, fun u w hu hadj hw => ?_⟩
    · rw [← grid_val f u]; exact hones _ _ hu
    · exact hcl _ _ _ _ hu ((adj_iff_nadj n u w).mp hadj) (by rw [grid_val]; exact hw)

/-- **The local characterization** of bar arrays (`k ≥ 2`). -/
theorem isBarArrayLocal_iff (n k : Nat) (hk : 2 ≤ k) (f : V n → Bool) :
    IsBarArrayLocal k (grid n f) ↔ IsBarArray n k f := by
  rw [isBarArray_iff_barProp n k (by omega) f]
  exact local_iff_barProp k hk (grid n f) n (fun r c h => grid_lt h)

end Tally.BarArray

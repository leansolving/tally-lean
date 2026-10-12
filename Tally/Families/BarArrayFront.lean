import Tally.Families.BarArray

namespace Tally.BarArray

open Tally Tally.Grid

variable (n k : Nat)

theorem vlen_eq (g : Nat → Nat → Bool) (r c : Nat) :
    vlen g r c = if g r c = true then
      (if 0 < r ∧ g (r - 1) c = true then vlen g (r - 1) c + 1 else 1) else 0 := by
  cases r with
  | zero => simp [vlen]
  | succ r =>
    cases h1 : g (r + 1) c <;> cases h2 : g r c <;> simp [vlen, h1, h2]
    cases r <;> simp [vlen, h2]

theorem hlen_eq (g : Nat → Nat → Bool) (r c : Nat) :
    hlen g r c = if g r c = true then
      (if 0 < c ∧ g r (c - 1) = true then hlen g r (c - 1) + 1 else 1) else 0 := by
  cases c with
  | zero => simp [hlen]
  | succ c =>
    cases h1 : g r (c + 1) <;> cases h2 : g r c <;> simp [hlen, h1, h2]
    cases c <;> simp [hlen, h2]


theorem hlen_pos (g : Nat → Nat → Bool) (r c : Nat) (h : g r c = true) : 0 < hlen g r c := by
  rw [hlen_eq]; simp only [h, if_true]; split <;> omega

theorem vlen_pos (g : Nat → Nat → Bool) (r c : Nat) (h : g r c = true) : 0 < vlen g r c := by
  rw [vlen_eq]; simp only [h, if_true]; split <;> omega

theorem place_cases (a : Col) (l : Left) (s : Fin 2) (e : Col) (e' : Option Col) (l' : Left)
    (h : place k a l s = some (e, e', l')) :
    (s.val = 0 ∧ (∀ m, a ≠ .vert m) ∧ (∀ m, l ≠ .horiz m) ∧ e = .free ∧ e' = none ∧ l' = .free) ∨
    (s.val = 1 ∧ (∃ m, a = .vert m ∧ l = .free ∧ e = (if m + 1 = k then .block else .vert (m + 1)) ∧
        e' = none ∧ l' = .block)) ∨
    (s.val = 1 ∧ a = .free ∧ l = .free ∧ e = .vert 1 ∧ e' = none ∧ l' = .pend) ∨
    (s.val = 1 ∧ a = .free ∧ l = .pend ∧ e = .block ∧ e' = some .block ∧
        l' = (if k = 2 then .block else .horiz 2)) ∨
    (s.val = 1 ∧ ∃ m, a = .free ∧ l = .horiz m ∧ e = .block ∧ e' = none ∧
        l' = (if m + 1 = k then .block else .horiz (m + 1))) := by
  fin_cases s <;> cases a <;> cases l <;> simp [place] at h ⊢ <;> grind

theorem colCur_free (g : Nat → Nat → Bool) (R C : Nat) (h : colEntry k g R C C = .free) :
    ¬ (0 < R ∧ g (R - 1) C = true) := by
  unfold colEntry at h
  simp only [lt_irrefl, if_false] at h
  rintro ⟨hR, hg⟩
  simp only [hR, if_true, hg, Bool.true_eq_false, if_false] at h
  split_ifs at h

theorem colCur_vert (g : Nat → Nat → Bool) (R C m : Nat) (h : colEntry k g R C C = .vert m) :
    0 < R ∧ g (R - 1) C = true ∧ vlen g (R - 1) C = m := by
  unfold colEntry at h
  simp only [lt_irrefl, if_false] at h
  split_ifs at h with h1 h2 h3 h4
  · injection h with h; exact ⟨h1, by simpa using h2, h⟩

theorem leftReg_free (g : Nat → Nat → Bool) (R C : Nat) (h : leftReg k g R C = .free) :
    ¬ (0 < C ∧ g R (C - 1) = true) := by
  unfold leftReg at h
  rintro ⟨hC, hg⟩
  simp only [Nat.pos_iff_ne_zero.mp hC, if_false, hg, Bool.true_eq_false] at h
  split_ifs at h

theorem leftReg_pend (g : Nat → Nat → Bool) (R C : Nat) (h : leftReg k g R C = .pend) :
    0 < C ∧ g R (C - 1) = true ∧ ¬ (0 < R ∧ g (R - 1) (C - 1) = true) ∧ hlen g R (C - 1) = 1 := by
  unfold leftReg at h
  split_ifs at h with h1 h2 h3 h4
  exact ⟨Nat.pos_of_ne_zero h1, by simpa using h2, h3, h4⟩

theorem leftReg_horiz (g : Nat → Nat → Bool) (R C m : Nat) (h : leftReg k g R C = .horiz m) :
    0 < C ∧ g R (C - 1) = true ∧ ¬ (0 < R ∧ g (R - 1) (C - 1) = true) ∧ hlen g R (C - 1) = m ∧
      m ≠ 1 ∧ m ≠ k := by
  unfold leftReg at h
  split_ifs at h with h1 h2 h3 h4 h5
  injection h with h
  exact ⟨Nat.pos_of_ne_zero h1, by simpa using h2, h3, h, h ▸ h4, h ▸ h5⟩

theorem colEntry_new_cur (g : Nat → Nat → Bool) (R C : Nat) :
    colEntry k g R (C + 1) C =
      if g R C = false then .free
      else if 0 < C ∧ g R (C - 1) = true then .block
      else if vlen g R C = k then .block else .vert (vlen g R C) := by
  simp [colEntry]

theorem leftReg_new (g : Nat → Nat → Bool) (R C : Nat) :
    leftReg k g R (C + 1) =
      if g R C = false then .free
      else if 0 < R ∧ g (R - 1) C = true then .block
      else if hlen g R C = 1 then .pend
      else if hlen g R C = k then .block else .horiz (hlen g R C) := by
  simp [leftReg]

theorem colEntry_new_prev (g : Nat → Nat → Bool) (R c : Nat) :
    colEntry k g R (c + 2) c =
      if g R c = false then .free
      else if (0 < c ∧ g R (c - 1) = true) ∨ g R (c + 1) = true then .block
      else if vlen g R c = k then .block else .vert (vlen g R c) := by
  simp [colEntry]

theorem colEntry_old_prev (g : Nat → Nat → Bool) (R c : Nat) :
    colEntry k g R (c + 1) c =
      if g R c = false then .free
      else if 0 < c ∧ g R (c - 1) = true then .block
      else if vlen g R c = k then .block else .vert (vlen g R c) := by
  simp [colEntry]

theorem place_spec (hk : 2 ≤ k) (g : Nat → Nat → Bool) (R C : Nat) (s : Fin 2)
    (hs : s.val = 1 ↔ g R C = true) (e : Col) (e' : Option Col) (l' : Left)
    (h : place k (colEntry k g R C C) (leftReg k g R C) s = some (e, e', l')) :
    e = colEntry k g R (C + 1) C ∧ l' = leftReg k g R (C + 1) ∧
      (∀ c, C = c + 1 → e'.getD (colEntry k g R (c + 1) c) = colEntry k g R (c + 2) c) := by
  rw [colEntry_new_cur, leftReg_new]
  rcases place_cases k _ _ s e e' l' h with
    ⟨hs0, -, -, rfl, rfl, rfl⟩ | ⟨hs1, m, ha, hl, rfl, rfl, rfl⟩ | ⟨hs1, ha, hl, rfl, rfl, rfl⟩ |
    ⟨hs1, ha, hl, rfl, rfl, rfl⟩ | ⟨hs1, m, ha, hl, rfl, rfl, rfl⟩
  · have hx : g R C = false := by simpa [hs0] using hs
    refine ⟨by simp [hx], by simp [hx], ?_⟩
    rintro c rfl
    rw [Option.getD_none, colEntry_old_prev, colEntry_new_prev]
    simp [hx]
  · have hx : g R C = true := hs.mp hs1
    obtain ⟨hR, hu, hv⟩ := colCur_vert k g R C m ha
    have hlf := leftReg_free k g R C hl
    refine ⟨?_, by simp [hx, hR, hu], ?_⟩
    · rw [vlen_eq g R C]; simp [hx, hR, hu, hlf, hv]
    · rintro c rfl
      have : g R c = false := by simpa using hlf
      rw [Option.getD_none, colEntry_old_prev, colEntry_new_prev]
      simp [this]
  · have hx : g R C = true := hs.mp hs1
    have hu := colCur_free k g R C ha
    have hlf := leftReg_free k g R C hl
    refine ⟨?_, ?_, ?_⟩
    · rw [vlen_eq g R C]; simp only [hx, hu, hlf, if_false, if_true, Bool.true_eq_false]
      rw [if_neg (by omega)]
    · rw [hlen_eq g R C]; simp [hx, hu, hlf]
    · rintro c rfl
      have : g R c = false := by simpa using hlf
      rw [Option.getD_none, colEntry_old_prev, colEntry_new_prev]
      simp [this]
  · have hx : g R C = true := hs.mp hs1
    have hu := colCur_free k g R C ha
    obtain ⟨hC, hlf, -, hh⟩ := leftReg_pend k g R C hl
    refine ⟨by simp [hx, hC, hlf], ?_, ?_⟩
    · rw [hlen_eq g R C]; simp only [hx, hu, hC, hlf, hh, if_true, if_false, and_self,
        Bool.true_eq_false]
      split_ifs <;> first | rfl | (exfalso; omega)
    · rintro c rfl
      simp only [Nat.add_sub_cancel] at hlf
      rw [Option.getD_some, colEntry_new_prev]
      simp [hx, hlf]
  · have hx : g R C = true := hs.mp hs1
    have hu := colCur_free k g R C ha
    obtain ⟨hC, hlf, -, hh, hm1, -⟩ := leftReg_horiz k g R C m hl
    have hpos := hlen_pos g R (C - 1) hlf
    refine ⟨by simp [hx, hC, hlf], ?_, ?_⟩
    · rw [hlen_eq g R C]; simp only [hx, hu, hC, hlf, hh, if_true, if_false, and_self,
        Bool.true_eq_false]
      split_ifs <;> first | rfl | (exfalso; omega)
    · rintro c rfl
      have h2 := hlen_eq g R c
      simp only [Nat.add_sub_cancel] at hh hlf
      rw [hlf, if_pos rfl, hh] at h2
      have hprev : 0 < c ∧ g R (c - 1) = true := by
        by_contra hc; rw [if_neg hc] at h2; exact hm1 h2
      rw [Option.getD_none, colEntry_old_prev, colEntry_new_prev]
      simp [hlf, hprev]

theorem colEntry_other (g : Nat → Nat → Bool) (R C j : Nat) (h1 : j ≠ C) (h2 : j + 1 ≠ C) :
    colEntry k g R C j = colEntry k g R (C + 1) j := by
  unfold colEntry
  by_cases hj : j < C
  · simp [hj, show j < C + 1 by omega, show (j + 1 < C ↔ j + 1 < C + 1) by omega]
  · simp [hj, show ¬ j < C + 1 by omega]

theorem colEntry_wrap (g : Nat → Nat → Bool) (R j : Nat) (hj : j < n) (hg : g R n = false) :
    colEntry k g R n j = colEntry k g (R + 1) 0 j := by
  unfold colEntry
  by_cases hj1 : j + 1 < n
  · simp [hj, hj1]
  · have : j + 1 = n := by omega
    simp [hj, this, hg]

theorem cols_step (g : Nat → Nat → Bool) (R C : Nat) (hC : C < n) (e : Col) (e' : Option Col)
    (he : e = colEntry k g R (C + 1) C)
    (hprev : ∀ c, C = c + 1 → e'.getD (colEntry k g R (c + 1) c) = colEntry k g R (c + 2) c) :
    (match (motive := Option Col → Fin n → Col) e' with
      | none => Function.update (fun j : Fin n => colEntry k g R C j.val) ⟨C, hC⟩ e
      | some e' =>
        if h : 0 < C then
          Function.update (Function.update (fun j : Fin n => colEntry k g R C j.val) ⟨C, hC⟩ e)
            ⟨C - 1, by omega⟩ e'
        else Function.update (fun j : Fin n => colEntry k g R C j.val) ⟨C, hC⟩ e) =
      fun j => colEntry k g R (C + 1) j.val := by
  -- columns other than `C` and `C - 1` are unchanged
  have hoth : ∀ j : Fin n, j.val ≠ C → j.val + 1 ≠ C →
      colEntry k g R C j.val = colEntry k g R (C + 1) j.val :=
    fun j h1 h2 => colEntry_other k g R C j.val h1 h2
  cases e' with
  | none =>
    dsimp only
    funext j
    rw [Function.update_apply]
    split
    · rename_i hj; subst hj; exact he
    · rename_i hj
      have hj' : j.val ≠ C := fun h => hj (Fin.ext h)
      by_cases h2 : j.val + 1 = C
      · have := hprev j.val h2.symm
        rw [Option.getD_none] at this
        rw [← h2]; exact this
      · exact hoth j hj' h2
  | some x =>
    dsimp only
    by_cases hc0 : 0 < C
    · obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
      have hx := hprev c rfl
      rw [Option.getD_some] at hx
      simp only [hc0, dif_pos]
      funext j
      rw [Function.update_apply, Function.update_apply]
      split
      · rename_i hj
        have : j.val = c := by rw [hj]; simp
        rw [this, hx]
      · rename_i hj
        have hj1 : j.val ≠ c := fun h => hj (Fin.ext (by simp [h]))
        split
        · rename_i hj2; subst hj2; exact he
        · rename_i hj2
          have hj2' : j.val ≠ c + 1 := fun h => hj2 (Fin.ext h)
          exact hoth j hj2' (by omega)
    · simp only [hc0, dif_neg, not_false_eq_true]
      funext j
      rw [Function.update_apply]
      split
      · rename_i hj; subst hj; exact he
      · rename_i hj
        exact hoth j (fun h => hj (Fin.ext h)) (by omega)

theorem front_step (n k : Nat) (hn : 0 < n) (hk : 2 ≤ k) (w : Word (n * n) 2) (i : Nat)
    (hi : i < n * n) (st' : MState n)
    (h : mstep n k i (front n k (grid n (toArray n w)) i) (w ⟨i, hi⟩) = some st') :
    st' = front n k (grid n (toArray n w)) (i + 1) := by
  have hs := grid_cur n hn w i hi
  have hoff : ∀ r, grid n (toArray n w) r n = false := fun r => grid_off n _ r
  generalize grid n (toArray n w) = g at hs h hoff ⊢
  have hmod := Nat.mod_lt i hn
  unfold mstep at h
  rw [dif_pos hmod] at h
  simp only [front] at h
  generalize hp : place k (colEntry k g (i / n) (i % n) (i % n)) (leftReg k g (i / n) (i % n))
    (w ⟨i, hi⟩) = p at h
  rcases p with _ | ⟨e, e', l'⟩
  · simp at h
  obtain ⟨he, hl', hprev⟩ := place_spec k hk g _ _ _ hs e e' l' hp
  have hcols := cols_step n k g (i / n) (i % n) hmod e e' he hprev
  dsimp only at h
  have hwrap : (fun j : Fin n => colEntry k g (i / n) n j.val) =
      fun j : Fin n => colEntry k g (i / n + 1) 0 j.val := by
    funext j
    exact colEntry_wrap n k g (i / n) j.val j.isLt (hoff _)
  rcases succ_div_mod n hn i with ⟨hlt, hd, hm⟩ | ⟨heq, hd, hm⟩
  · rw [if_neg (by omega)] at h
    cases h
    show _ = (fun j : Fin n => colEntry k g ((i + 1) / n) ((i + 1) % n) j.val,
      leftReg k g ((i + 1) / n) ((i + 1) % n))
    rw [hd, hm]
    exact Prod.ext hcols hl'
  · rw [if_pos heq] at h
    split at h
    · exact absurd h (by simp)
    · cases h
      show _ = (fun j : Fin n => colEntry k g ((i + 1) / n) ((i + 1) % n) j.val,
        leftReg k g ((i + 1) / n) ((i + 1) % n))
      rw [hd, hm]
      refine Prod.ext ?_ ?_
      · rw [heq] at hcols
        exact hcols.trans hwrap
      · simp [leftReg]
end Tally.BarArray

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Layered state specifications

A `Spec S L k` describes a deterministic layered automaton reading words of
length `L` over the alphabet `Fin k`. It is purely mathematical: no equality
or hash instances are required here; the engine (`Tally.Engine`) adds them.

* `step i s a` is the transition at layer `i` (0-based) from state `s` on
  symbol `a`; `none` rejects.
* `final s` decides acceptance of the state reached after all `L` layers.

A word `w : Fin L → Fin k` is accepted iff running `step` from `root` over
`w` never rejects and `final` holds at the end. The number of accepted words
is `Fintype.card σ.Accepted`; it is the quantity every engine theorem refers
to, and the quantity each OEIS family relates to its objects.
-/

namespace Tally

/-- A deterministic layered automaton with states `S`, reading words of length `L`
over the alphabet `Fin k`. -/
structure Spec (S : Type) (L k : Nat) where
  /-- The start state, before layer `0`. -/
  root : S
  /-- `step i s a` is the transition at layer `i` from state `s` on symbol `a`; `none` rejects. -/
  step : Nat → S → Fin k → Option S
  /-- Acceptance of the state reached after all `L` layers. -/
  final : S → Bool

/-- Words of length `L` over the alphabet `Fin k`. -/
abbrev Word (L k : Nat) := Fin L → Fin k

namespace Spec

variable {S : Type} {L k : Nat} (σ : Spec S L k)

/-- Run from state `s` at layer `i` over a list of symbols. -/
def runFrom (s : S) (i : Nat) : List (Fin k) → Option S
  | [] => some s
  | a :: as =>
    match σ.step i s a with
    | none => none
    | some t => runFrom t (i + 1) as

/-- Acceptance of a suffix word of any length `m`, starting at state `s` in layer `i`. -/
def acceptsFrom (s : S) (i : Nat) {m : Nat} (w : Fin m → Fin k) : Bool :=
  match σ.runFrom s i (List.ofFn w) with
  | none => false
  | some t => σ.final t

/-- Executable acceptance of a full word. -/
def acceptsB (w : Word L k) : Bool := σ.acceptsFrom σ.root 0 w

/-- Acceptance as a proposition. -/
def Accepts (w : Word L k) : Prop := σ.acceptsB w = true

instance (w : Word L k) : Decidable (σ.Accepts w) :=
  inferInstanceAs (Decidable (σ.acceptsB w = true))

/-- The accepted words. -/
def Accepted : Type := {w : Word L k // σ.Accepts w}

instance : Fintype σ.Accepted := inferInstanceAs (Fintype {w : Word L k // σ.Accepts w})

@[simp] theorem runFrom_nil (s : S) (i : Nat) : σ.runFrom s i [] = some s := rfl

theorem runFrom_cons (s : S) (i : Nat) (a : Fin k) (as : List (Fin k)) :
    σ.runFrom s i (a :: as) =
      match σ.step i s a with
      | none => none
      | some t => σ.runFrom t (i + 1) as := by
  simp [runFrom]

/-- Running over a concatenation: run the first part, then the second from where it ends. -/
theorem runFrom_append (s : S) (i : Nat) (xs ys : List (Fin k)) :
    σ.runFrom s i (xs ++ ys) =
      match σ.runFrom s i xs with
      | none => none
      | some t => σ.runFrom t (i + xs.length) ys := by
  induction xs generalizing s i with
  | nil => simp
  | cons a as ih =>
    rw [List.cons_append, runFrom_cons, runFrom_cons]
    cases σ.step i s a with
    | none => rfl
    | some t =>
      simp only [ih, List.length_cons]
      rw [Nat.add_comm as.length 1, ← Nat.add_assoc]

/-- The empty suffix is accepted iff the current state is final. -/
theorem acceptsFrom_zero (s : S) (i : Nat) (w : Fin 0 → Fin k) :
    σ.acceptsFrom s i w = σ.final s := by
  simp [acceptsFrom, List.ofFn_zero]

/-- Peeling off the first symbol of a suffix. -/
theorem acceptsFrom_cons (s : S) (i : Nat) {m : Nat} (a : Fin k) (w : Fin m → Fin k) :
    σ.acceptsFrom s i (Fin.cons a w) =
      match σ.step i s a with
      | none => false
      | some t => σ.acceptsFrom t (i + 1) w := by
  unfold acceptsFrom
  rw [List.ofFn_succ, Fin.cons_zero, runFrom_cons]
  simp only [Fin.cons_succ]
  cases σ.step i s a <;> rfl

/-! ### Completions

`compl m s i` counts the accepted suffixes of length `m` from state `s` at
layer `i`. It satisfies the backward recurrence used by the engine proof. -/

/-- Number of accepted suffixes of length `m` from state `s` at layer `i`. -/
def compl (m : Nat) (s : S) (i : Nat) : Nat :=
  (Finset.univ.filter fun w : Fin m → Fin k => σ.acceptsFrom s i w = true).card

theorem compl_zero (s : S) (i : Nat) : σ.compl 0 s i = if σ.final s then 1 else 0 := by
  unfold compl
  simp only [acceptsFrom_zero]
  by_cases h : σ.final s = true <;> simp [h]

/-- Splitting the words of length `m + 1` by their first symbol. -/
private theorem card_filter_succ {m : Nat} (P : (Fin (m + 1) → Fin k) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ a : Fin k, (Finset.univ.filter fun w : Fin m → Fin k => P (Fin.cons a w)).card := by
  rw [← Fintype.card_subtype]
  simp_rw [← Fintype.card_subtype]
  rw [← Fintype.card_sigma]
  refine Fintype.card_congr ?_
  refine (Equiv.subtypeEquiv (Fin.consEquiv fun _ => Fin k).symm ?_).trans
    (Equiv.subtypeProdEquivSigmaSubtype fun a (w : Fin m → Fin k) => P (Fin.cons a w))
  intro w
  simp [Fin.consEquiv]

theorem compl_succ (m : Nat) (s : S) (i : Nat) :
    σ.compl (m + 1) s i = ∑ a : Fin k, (σ.step i s a).elim 0 fun t => σ.compl m t (i + 1) := by
  unfold compl
  rw [card_filter_succ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases h : σ.step i s a with _ | t
  · simp [acceptsFrom_cons, h]
  · simp [acceptsFrom_cons, h]

/-! ### Frontier descriptions

A family proof describes the run of a word explicitly: a function
`front : Nat → S` (depending on the word) with `front 0 = root` such that every
non-rejecting step from `front i` on the `i`-th symbol lands in `front (i + 1)`
(`IsFront`). Then the run over the first `i` symbols reaches `front i` unless an
earlier step rejected (`runFrom_take_eq`), and acceptance reduces to a
per-position condition ("no step rejects") plus the final check on `front L`
(`accepts_iff_front`). This is the only induction over the word a family needs. -/

section Front

variable (w : Word L k) (front : Nat → S)

/-- `front` describes the run of `w`: it starts at the root, and each
non-rejecting step from `front i` reads symbol `i` into `front (i + 1)`. -/
structure IsFront : Prop where
  zero : front 0 = σ.root
  step : ∀ i (hi : i < L) (s' : S), σ.step i (front i) (w ⟨i, hi⟩) = some s' → s' = front (i + 1)

/-- The step at position `i`, read from the described frontier, does not reject. -/
def StepOK (i : Nat) (hi : i < L) : Prop := σ.step i (front i) (w ⟨i, hi⟩) ≠ none

/-- No step among the first `i` rejects. -/
def NoRejectBelow (i : Nat) : Prop := ∀ j (hj : j < L), j < i → σ.StepOK w front j hj

variable {w front}

theorem noRejectBelow_zero : σ.NoRejectBelow w front 0 :=
  fun _ _ hj => absurd hj (Nat.not_lt_zero _)

theorem noRejectBelow_of_succ {i : Nat} (h : σ.NoRejectBelow w front (i + 1)) :
    σ.NoRejectBelow w front i :=
  fun j hj hji => h j hj (Nat.lt_succ_of_lt hji)

theorem noRejectBelow_succ_iff {i : Nat} (hi : i < L) :
    σ.NoRejectBelow w front (i + 1) ↔ σ.NoRejectBelow w front i ∧ σ.StepOK w front i hi := by
  constructor
  · intro h
    exact ⟨σ.noRejectBelow_of_succ h, h i hi (Nat.lt_succ_self i)⟩
  · rintro ⟨h, hok⟩ j hj hji
    rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hlt | heq
    · exact h j hj hlt
    · subst heq; exact hok

open Classical in
/-- The run over the first `i` symbols: the described frontier unless a step rejected. -/
theorem runFrom_take_eq (hf : σ.IsFront w front) (i : Nat) (hi : i ≤ L) :
    σ.runFrom σ.root 0 ((List.ofFn w).take i) =
      if σ.NoRejectBelow w front i then some (front i) else none := by
  induction i with
  | zero =>
    rw [if_pos σ.noRejectBelow_zero]
    simp only [List.take_zero, runFrom_nil, hf.zero]
  | succ i ih =>
    have hi' : i < L := hi
    rw [List.take_add_one, List.getElem?_ofFn, dif_pos hi', Option.toList_some,
      runFrom_append, ih (Nat.le_of_lt hi'),
      List.length_take, List.length_ofFn, Nat.min_eq_left (Nat.le_of_lt hi'), Nat.zero_add]
    by_cases hnr : σ.NoRejectBelow w front i
    · rw [if_pos hnr]
      simp only [runFrom_cons, runFrom_nil]
      rcases hm : σ.step i (front i) (w ⟨i, hi'⟩) with _ | s'
      · have : ¬ σ.NoRejectBelow w front (i + 1) :=
          fun h => h i hi' (Nat.lt_succ_self i) hm
        rw [if_neg this]
      · rw [hf.step i hi' s' hm]
        have : σ.NoRejectBelow w front (i + 1) :=
          (σ.noRejectBelow_succ_iff hi').mpr
            ⟨hnr, by unfold StepOK; rw [hm]; exact Option.some_ne_none s'⟩
        rw [if_pos this]
    · rw [if_neg hnr]
      rw [if_neg fun h => hnr (σ.noRejectBelow_of_succ h)]

/-- **Acceptance through a frontier description.** A word is accepted iff no step
rejects (read from the described frontier) and the final frontier passes `final`. -/
theorem accepts_iff_front (hf : σ.IsFront w front) :
    σ.Accepts w ↔ (∀ i (hi : i < L), σ.StepOK w front i hi) ∧ σ.final (front L) = true := by
  have key := σ.runFrom_take_eq hf L le_rfl
  rw [List.take_of_length_le (by simp)] at key
  unfold Accepts acceptsB acceptsFrom
  rw [key]
  by_cases h : σ.NoRejectBelow w front L
  · rw [if_pos h]
    exact ⟨fun hfin => ⟨fun i hi => h i hi hi, hfin⟩, fun hh => hh.2⟩
  · rw [if_neg h]
    exact ⟨fun hfin => absurd hfin Bool.false_ne_true,
      fun hh => absurd (fun j hj _ => hh.1 j hj) h⟩

end Front

/-! ### Simulation

The specification the engine runs is a packed one (`σ`, states `S`, typically
`UInt64`); the family's mathematical specification is `τ` (states `T`). A relation
`Rel : S → T → Prop` that relates the roots, is preserved by every step below layer
`L` with simultaneous rejection (`StepRel`), and makes `final` agree is a
simulation (`IsSim`). Then both specifications accept the same words
(`accepts_iff_sim`) and have the same number of accepted words
(`card_accepted_eq_of_sim`); `Tally.Engine` adds `count_eq_of_sim`. A family proves
`IsSim` by giving `Rel`, the root case and its one-step lemma; the induction over
the word is done here once. -/

section Sim

variable {T : Type} (τ : Spec T L k) (Rel : S → T → Prop)

/-- The shape of a one-step simulation claim at layer `i`: both steps reject,
or both succeed into related states. -/
def StepRel (i : Nat) (s : S) (t : T) (a : Fin k) : Prop :=
  match σ.step i s a, τ.step i t a with
  | none, none => True
  | some s', some t' => Rel s' t'
  | _, _ => False

/-- `σ` simulates `τ` through `Rel`. -/
structure IsSim : Prop where
  root : Rel σ.root τ.root
  step : ∀ i, i < L → ∀ (s : S) (t : T) (a : Fin k), Rel s t → σ.StepRel τ Rel i s t a
  final : ∀ (s : S) (t : T), Rel s t → σ.final s = τ.final t

variable {σ τ Rel}

/-- Related states stay related along any run that ends at or before layer `L`. -/
theorem runFrom_rel (h : σ.IsSim τ Rel) (xs : List (Fin k)) :
    ∀ (i : Nat), i + xs.length ≤ L → ∀ (s : S) (t : T), Rel s t →
    match σ.runFrom s i xs, τ.runFrom t i xs with
    | none, none => True
    | some s', some t' => Rel s' t'
    | _, _ => False := by
  induction xs with
  | nil => intro i _ s t hr; simpa using hr
  | cons a as ih =>
    intro i hi s t hr
    have hs := h.step i (by simp only [List.length_cons] at hi; omega) s t a hr
    rw [runFrom_cons, runFrom_cons]
    unfold StepRel at hs
    rcases hf : σ.step i s a with _ | s' <;> rcases hm : τ.step i t a with _ | t' <;>
      simp only [hf, hm] at hs ⊢
    exact ih (i + 1) (by simp only [List.length_cons] at hi; omega) s' t' hs

/-- **Acceptance through a simulation.** -/
theorem accepts_iff_sim (h : σ.IsSim τ Rel) (w : Word L k) : σ.Accepts w ↔ τ.Accepts w := by
  have hr := runFrom_rel h (List.ofFn w) 0 (by simp) σ.root τ.root h.root
  unfold Accepts acceptsB acceptsFrom
  revert hr
  rcases σ.runFrom σ.root 0 (List.ofFn w) with _ | s' <;>
    rcases τ.runFrom τ.root 0 (List.ofFn w) with _ | t'
  · exact fun _ => Iff.rfl
  · exact fun hr => False.elim hr
  · exact fun hr => False.elim hr
  · intro hr
    show σ.final s' = true ↔ τ.final t' = true
    rw [h.final s' t' hr]

theorem card_accepted_eq_of_sim (h : σ.IsSim τ Rel) :
    Fintype.card σ.Accepted = Fintype.card τ.Accepted :=
  Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun w => accepts_iff_sim h w))

end Sim

end Spec

end Tally

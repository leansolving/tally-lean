import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Tally.Spec

/-!
# The generic counting engine

`Spec.count` runs a forward pass over the `L` layers of a specification,
keeping one hash map from states to counts per layer and merging equal
states by adding their counts. The main theorem `Spec.count_eq` states that
the result is the number of accepted words.

Proof idea: for a layer map `m` at layer `i`, the weighted sum
`∑ s ∈ keys m, m[s] * compl i s`, where `compl i s` is the number of accepted
completions from state `s` at layer `i`, is invariant under `advance`. At
layer 0 it is `compl 0 root`, the number of accepted words; at layer `L` the
weights are `1` on final states and `0` otherwise, which is what `finalSum`
computes. Only lookup-level facts about `Std.HashMap` are used.
-/

namespace Tally

open Std

variable {S : Type} {L k : Nat} [BEq S] [Hashable S]

/-- Add `v` to the count stored for `t` (inserting `t` if absent). -/
def addCount (m : HashMap S Nat) (t : S) (v : Nat) : HashMap S Nat :=
  m.alter t fun
    | none => some v
    | some w => some (w + v)

namespace Spec

variable (σ : Spec S L k)

/-- Transitions of one state with count `v` at layer `i`, pushed into `nxt`. -/
def pushState (i : Nat) (syms : List (Fin k)) (s : S) (v : Nat) (nxt : HashMap S Nat) :
    HashMap S Nat :=
  syms.foldl (fun nxt a =>
    match σ.step i s a with
    | none => nxt
    | some t => addCount nxt t v) nxt

/-- Push all counts of layer `i` forward to layer `i + 1`. -/
def advance (i : Nat) (cur : HashMap S Nat) : HashMap S Nat :=
  let syms := List.finRange k
  cur.fold (init := (∅ : HashMap S Nat)) fun nxt s v => σ.pushState i syms s v nxt

/-- Apply `advance` to layers `i, i + 1, …, i + j - 1`. -/
def layers : (j : Nat) → (i : Nat) → HashMap S Nat → HashMap S Nat
  | 0, _, m => m
  | j + 1, i, m => layers j (i + 1) (σ.advance i m)

/-- Total count of the final states. -/
def finalSum (m : HashMap S Nat) : Nat :=
  m.fold (init := 0) fun acc s v => if σ.final s then acc + v else acc

/-- The engine: number of accepted words of `σ`, computed by the forward pass. -/
def count : Nat :=
  σ.finalSum (σ.layers L 0 ((∅ : HashMap S Nat).insert σ.root 1))

/-! ### Correctness -/

section Correctness

variable [LawfulBEq S] [LawfulHashable S]

/-- Decidable equality derived from the lawful `BEq` (proof-side only). -/
abbrev decEqOfLawfulBEq : DecidableEq S := instDecidableEqOfLawfulBEq

attribute [local instance] decEqOfLawfulBEq

/-! #### Weighted sums of layer maps -/

/-- Weighted sum of a layer map: `∑ s, m[s] * g s` over the keys of `m`. -/
def wsum (m : HashMap S Nat) (g : S → Nat) : Nat :=
  ∑ s ∈ m.keys.toFinset, m.getD s 0 * g s

omit [LawfulHashable S] in
theorem wsum_empty (g : S → Nat) : wsum (∅ : HashMap S Nat) g = 0 := by
  simp [wsum, HashMap.keys_empty]

theorem getD_addCount (m : HashMap S Nat) (t s : S) (v : Nat) :
    (addCount m t v).getD s 0 = m.getD s 0 + if s = t then v else 0 := by
  unfold addCount
  rw [HashMap.getD_alter, HashMap.getD_eq_getD_getElem?]
  by_cases hts : t = s
  · subst hts
    simp only [beq_self_eq_true, if_true]
    cases m[t]? <;> simp
  · have : (t == s) = false := beq_eq_false_iff_ne.mpr hts
    simp [this, Ne.symm hts]

theorem mem_addCount (m : HashMap S Nat) (t s : S) (v : Nat) :
    s ∈ addCount m t v ↔ s ∈ m ∨ s = t := by
  unfold addCount
  rw [HashMap.mem_alter]
  by_cases hts : t = s
  · subst hts
    simp only [beq_self_eq_true, if_true, or_true, iff_true]
    cases m[t]? <;> simp
  · have : (t == s) = false := beq_eq_false_iff_ne.mpr hts
    simp [this, Ne.symm hts]

theorem keys_toFinset_addCount (m : HashMap S Nat) (t : S) (v : Nat) :
    (addCount m t v).keys.toFinset = insert t m.keys.toFinset := by
  ext s
  simp only [List.mem_toFinset, HashMap.mem_keys, mem_addCount, Finset.mem_insert]
  tauto

theorem wsum_addCount (m : HashMap S Nat) (t : S) (v : Nat) (g : S → Nat) :
    wsum (addCount m t v) g = wsum m g + v * g t := by
  unfold wsum
  rw [keys_toFinset_addCount]
  simp_rw [getD_addCount, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq']
  simp only [Finset.mem_insert, true_or, if_true]
  by_cases ht : t ∈ m.keys.toFinset
  · rw [Finset.insert_eq_of_mem ht]
  · rw [Finset.sum_insert ht]
    have : m.getD t 0 = 0 := HashMap.getD_eq_fallback (by simpa [HashMap.mem_keys] using ht)
    simp [this]

/-- Nodup keys, from `distinct_keys`. -/
theorem keys_nodup (m : HashMap S Nat) : m.keys.Nodup :=
  HashMap.distinct_keys.imp fun h => beq_eq_false_iff_ne.mp h

theorem sum_toList_eq_wsum (m : HashMap S Nat) (h : S → Nat) :
    (m.toList.map fun p => p.2 * h p.1).sum = wsum m h := by
  unfold wsum
  rw [List.sum_toFinset _ (keys_nodup m), ← HashMap.map_fst_toList_eq_keys, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hget := HashMap.mem_toList_iff_getElem?_eq_some.mp hp
  simp [Function.comp, HashMap.getD_eq_getD_getElem?, hget]

/-! #### The engine implements the completion recurrence -/

theorem wsum_pushState (i : Nat) (syms : List (Fin k)) (s : S) (v : Nat) (nxt : HashMap S Nat)
    (g : S → Nat) :
    wsum (σ.pushState i syms s v nxt) g =
      wsum nxt g + v * (syms.map fun a => (σ.step i s a).elim 0 g).sum := by
  induction syms generalizing nxt with
  | nil => simp [pushState]
  | cons a as ih =>
    simp only [pushState, List.foldl_cons, List.map_cons, List.sum_cons] at *
    rw [ih]
    rcases σ.step i s a with _ | t
    · simp
    · simp [wsum_addCount, Nat.mul_add]
      omega

theorem wsum_advance (i : Nat) (m : HashMap S Nat) (g : S → Nat) :
    wsum (σ.advance i m) g = wsum m fun s => ∑ a : Fin k, (σ.step i s a).elim 0 g := by
  unfold advance
  rw [HashMap.fold_eq_foldl_toList]
  have key : ∀ (l : List (S × Nat)) (init : HashMap S Nat),
      wsum (l.foldl (fun nxt p => σ.pushState i (List.finRange k) p.1 p.2 nxt) init) g =
        wsum init g + (l.map fun p => p.2 * ∑ a : Fin k, (σ.step i p.1 a).elim 0 g).sum := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons p l ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, wsum_pushState, Fin.sum_univ_def]
      omega
  rw [key, wsum_empty, zero_add]
  exact sum_toList_eq_wsum m fun s => ∑ a : Fin k, (σ.step i s a).elim 0 g

theorem finalSum_eq_wsum (m : HashMap S Nat) :
    σ.finalSum m = wsum m fun s => if σ.final s then 1 else 0 := by
  unfold finalSum
  rw [HashMap.fold_eq_foldl_toList, ← sum_toList_eq_wsum]
  have key : ∀ (l : List (S × Nat)) (init : Nat),
      l.foldl (fun acc p => if σ.final p.1 then acc + p.2 else acc) init =
        init + (l.map fun p => p.2 * if σ.final p.1 then 1 else 0).sum := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons p l ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      split <;> simp
      omega
  rw [key, zero_add]

theorem wsum_layers (j i : Nat) (m : HashMap S Nat) :
    wsum (σ.layers j i m) (fun s => if σ.final s then 1 else 0) =
      wsum m fun s => σ.compl j s i := by
  induction j generalizing i m with
  | zero =>
    simp only [layers]
    congr 1
    funext s
    rw [compl_zero]
  | succ j ih =>
    simp only [layers]
    rw [ih, wsum_advance]
    congr 1
    funext s
    rw [compl_succ]

theorem wsum_single (g : S → Nat) :
    wsum ((∅ : HashMap S Nat).insert σ.root 1) g = g σ.root := by
  unfold wsum
  have hk : ((∅ : HashMap S Nat).insert σ.root 1).keys.toFinset = {σ.root} := by
    ext s
    simp only [List.mem_toFinset, HashMap.mem_keys, HashMap.mem_insert, HashMap.not_mem_empty,
      or_false, beq_iff_eq, Finset.mem_singleton]
    exact eq_comm
  rw [hk, Finset.sum_singleton, HashMap.getD_insert_self, one_mul]

/-- **Main theorem.** The engine returns the number of accepted words. -/
theorem count_eq : σ.count = Fintype.card σ.Accepted := by
  unfold count
  rw [finalSum_eq_wsum, wsum_layers, wsum_single]
  unfold compl
  exact (Fintype.card_subtype _).symm

theorem count_eq_card_filter :
    σ.count = (Finset.univ.filter fun w : Word L k => σ.Accepts w).card := by
  rw [count_eq]
  exact Fintype.card_subtype _

/-- **Simulation transport.** If the packed specification `σ` run by the engine
simulates the mathematical specification `τ` (`Spec.IsSim`), the engine returns the
number of words `τ` accepts. -/
theorem count_eq_of_sim {T : Type} {τ : Spec T L k} {Rel : S → T → Prop} (h : σ.IsSim τ Rel) :
    σ.count = Fintype.card τ.Accepted := by
  rw [count_eq]
  exact card_accepted_eq_of_sim h

end Correctness

end Spec

end Tally

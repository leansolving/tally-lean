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

end Spec

/-! ### Parallel engine (sharded layers)

The same forward pass with each layer split into `P` shards (an `Array` of hash maps).
A family supplies a partition `part : Nat → S → Nat` (layer index, state) that decides
the shard of a state; `advancePar` lets `P` tasks emit the successors of their shard into
`P` buckets each (bucket of `t` at layer `i + 1` is `part (i + 1) t % P`), and then `P`
tasks merge bucket `b` of every worker into the new shard `b`, adopting the largest map
and inserting the others. With a partition that the step preserves in most layers (for a
row-major grid: the top bits of the frontier while the current column is below them, the
low bits otherwise), almost all successors stay in their worker's own bucket and the merge
is nearly free. The partition is a performance choice only: the correctness proof
(`countPar_eq`) is the weighted-sum invariant of the sequential engine lifted to a list of
maps and holds for every partition and `P`. `Task.spawn`/`Task.get` are pure functions whose
reference implementation the kernel sees (`Task.spawn fn = ⟨fn ()⟩`), so the trust base of
a value theorem through `countPar` is the same as through `count`. -/

/-- Add `v` to the count of `t` in bucket `b` (no-op if `b` is out of range). -/
def addCountB (bk : Array (HashMap S Nat)) (b : Nat) (t : S) (v : Nat) :
    Array (HashMap S Nat) :=
  bk.modify b fun m => addCount m t v

/-- Merge the counts of `m` into `acc`. -/
def mergeInto (acc m : HashMap S Nat) : HashMap S Nat :=
  m.fold (init := acc) fun acc t v => addCount acc t v

/-- The hash-based partition (no structure assumed). -/
def hashPart (_ : Nat) (s : S) : Nat := (hash s).toNat

namespace Spec

variable (σ : Spec S L k)

/-- Transitions of one state with count `v` at layer `i`, pushed into the buckets of
layer `i + 1`. -/
def pushStateB (part : Nat → S → Nat) (P : Nat) (i : Nat) (syms : List (Fin k)) (s : S)
    (v : Nat) (bk : Array (HashMap S Nat)) : Array (HashMap S Nat) :=
  syms.foldl (fun bk a =>
    match σ.step i s a with
    | none => bk
    | some t => addCountB bk (part (i + 1) t % P) t v) bk

/-- One worker `j`: the successors of shard `j` in `P` buckets, returned as the worker's own
bucket `j` (paired with `j`, and handed to the merge task by ownership so that its inserts are
in place) and the array of the other buckets (with `∅` at position `j`). -/
def emit (part : Nat → S → Nat) (P : Nat) (i : Nat) (j : Nat) (shard : HashMap S Nat) :
    (Nat × HashMap S Nat) × Array (HashMap S Nat) :=
  let syms := List.finRange k
  let bk := shard.fold (init := Array.replicate P (∅ : HashMap S Nat)) fun bk s v =>
    σ.pushStateB part P i syms s v bk
  ((j, bk.getD j ∅), bk.set! j ∅)

/-- Parallel `advance`: `P` emitting tasks, then `P` merging tasks. Worker `j` uses its own
spec and partition objects `mkσ j`, `mkPart j` (every closure object shared between threads
costs an atomic reference-count update per transition on one cache line, which is what
prevented any speedup in the first version); merge task `b` starts from worker `b`'s own
bucket and inserts the bucket-`b` maps of the other workers. (`Array.map` moves the
elements of a uniquely referenced array into the closures, `mapIdx` does not.) -/
def advancePar (mkσ : Nat → Spec S L k) (mkPart : Nat → Nat → S → Nat) (P : Nat) (i : Nat)
    (cur : Array (HashMap S Nat)) : Array (HashMap S Nat) :=
  let res : Array ((Nat × HashMap S Nat) × Array (HashMap S Nat)) :=
    (cur.mapIdx fun j shard => Task.spawn fun _ => (mkσ j).emit (mkPart j) P i j shard).map
      Task.get
  let (owns, foreigns) := res.unzip
  (owns.map fun (b, own) => Task.spawn fun _ =>
    foreigns.foldl (fun acc out => mergeInto acc (out.getD b ∅)) own).map Task.get

/-- Apply `advancePar` to layers `i, i + 1, …, i + j - 1`. -/
def layersPar (mkσ : Nat → Spec S L k) (mkPart : Nat → Nat → S → Nat) (P : Nat) :
    (j : Nat) → (i : Nat) → Array (HashMap S Nat) → Array (HashMap S Nat)
  | 0, _, ms => ms
  | j + 1, i, ms => layersPar mkσ mkPart P j (i + 1) (advancePar mkσ mkPart P i ms)

/-- Total count of the final states over all shards. -/
def finalSumAll (ms : Array (HashMap S Nat)) : Nat :=
  ms.foldl (fun acc m => acc + σ.finalSum m) 0

/-- The parallel engine with `P` shards (`P = 0` is treated as `1`): the spec is `mkσ 0`
(root, final), worker `j` runs `mkσ j` with partition `mkPart j`; a family passes
constructors that return the same spec for every `j` (`countPar_eq` assumes
`∀ j, mkσ j = mkσ 0`). -/
def countPar (mkσ : Nat → Spec S L k) (mkPart : Nat → Nat → S → Nat) (P : Nat) : Nat :=
  let P := max P 1
  (mkσ 0).finalSumAll (layersPar mkσ mkPart P L 0
    (#[(∅ : HashMap S Nat).insert (mkσ 0).root 1] ++ Array.replicate (P - 1) (∅ : HashMap S Nat)))

end Spec

namespace Spec

variable (σ : Spec S L k)

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


/-! #### The parallel engine -/

private theorem getD_of_lt {α : Type} {xs : Array α} {i : Nat} {d : α} (h : i < xs.size) :
    xs.getD i d = xs[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

private theorem list_sum_map_eq_range {α : Type} (l : List α) (h : α → Nat) (d : α) :
    (l.map h).sum = ∑ j ∈ Finset.range l.length, h (l.getD j d) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ', add_comm]
    simp

private theorem array_sum_map_eq_range {α : Type} (xs : Array α) (h : α → Nat) (d : α) :
    (xs.toList.map h).sum = ∑ j ∈ Finset.range xs.size, h (xs.getD j d) := by
  rw [list_sum_map_eq_range _ h d, Array.length_toList]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- Weighted sum of a sharded layer: the sum of `wsum` over its shards. -/
def wsumAll (ms : Array (HashMap S Nat)) (g : S → Nat) : Nat :=
  ∑ b ∈ Finset.range ms.size, wsum (ms.getD b ∅) g

theorem wsum_mergeInto (acc m : HashMap S Nat) (g : S → Nat) :
    wsum (mergeInto acc m) g = wsum acc g + wsum m g := by
  unfold mergeInto
  rw [HashMap.fold_eq_foldl_toList, ← sum_toList_eq_wsum m g]
  generalize m.toList = l
  induction l generalizing acc with
  | nil => simp
  | cons p l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, wsum_addCount]
    omega

omit [LawfulBEq S] [LawfulHashable S] in
theorem size_addCountB (bk : Array (HashMap S Nat)) (b : Nat) (t : S) (v : Nat) :
    (addCountB bk b t v).size = bk.size :=
  Array.size_modify

theorem wsumAll_addCountB (bk : Array (HashMap S Nat)) (b : Nat) (t : S) (v : Nat)
    (g : S → Nat) :
    wsumAll (addCountB bk b t v) g = wsumAll bk g + if b < bk.size then v * g t else 0 := by
  unfold wsumAll
  rw [size_addCountB]
  have h : ∀ c ∈ Finset.range bk.size, wsum ((addCountB bk b t v).getD c ∅) g =
      wsum (bk.getD c ∅) g + if c = b then v * g t else 0 := by
    intro c hc
    have hc' : c < bk.size := Finset.mem_range.mp hc
    rw [getD_of_lt hc']
    unfold addCountB
    rw [getD_of_lt (by simpa using hc'), Array.getElem_modify]
    by_cases hcb : c = b
    · subst hcb
      simp [wsum_addCount]
    · simp [Ne.symm hcb, hcb]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp [Finset.mem_range]

omit [LawfulBEq S] [LawfulHashable S] in
theorem size_pushStateB (part : Nat → S → Nat) (P i : Nat) (syms : List (Fin k)) (s : S)
    (v : Nat) (bk : Array (HashMap S Nat)) :
    (σ.pushStateB part P i syms s v bk).size = bk.size := by
  induction syms generalizing bk with
  | nil => rfl
  | cons a as ih =>
    simp only [pushStateB, List.foldl_cons] at *
    rw [ih]
    rcases σ.step i s a with _ | t
    · rfl
    · exact size_addCountB _ _ _ _

theorem wsumAll_pushStateB (part : Nat → S → Nat) (P i : Nat) (syms : List (Fin k)) (s : S)
    (v : Nat) (bk : Array (HashMap S Nat)) (hP : 0 < P) (hsz : bk.size = P) (g : S → Nat) :
    wsumAll (σ.pushStateB part P i syms s v bk) g =
      wsumAll bk g + v * (syms.map fun a => (σ.step i s a).elim 0 g).sum := by
  induction syms generalizing bk with
  | nil => simp [pushStateB]
  | cons a as ih =>
    simp only [pushStateB, List.foldl_cons, List.map_cons, List.sum_cons] at *
    rcases σ.step i s a with _ | t
    · rw [ih bk hsz]
      simp
    · rw [ih _ (by rw [size_addCountB, hsz]), wsumAll_addCountB,
        if_pos (by rw [hsz]; exact Nat.mod_lt _ hP)]
      simp [Nat.mul_add]
      omega

omit [LawfulHashable S] in
theorem wsumAll_replicate (P : Nat) (g : S → Nat) :
    wsumAll (Array.replicate P (∅ : HashMap S Nat)) g = 0 := by
  unfold wsumAll
  refine Finset.sum_eq_zero fun c hc => ?_
  rw [getD_of_lt (by simpa using hc), Array.getElem_replicate, wsum_empty]

omit [LawfulHashable S] in
theorem wsum_getD_add_wsumAll_set (bk : Array (HashMap S Nat)) (j : Nat) (g : S → Nat) :
    wsum (bk.getD j ∅) g + wsumAll (bk.set! j ∅) g = wsumAll bk g := by
  unfold wsumAll
  have hsz : (bk.set! j ∅).size = bk.size := Array.size_setIfInBounds
  rw [hsz]
  have h : ∀ c ∈ Finset.range bk.size, wsum (bk.getD c ∅) g =
      wsum ((bk.set! j ∅).getD c ∅) g + if c = j then wsum (bk.getD j ∅) g else 0 := by
    intro c hc
    have hc' : c < bk.size := Finset.mem_range.mp hc
    have hc2 : c < (bk.setIfInBounds j ∅).size := by rwa [Array.size_setIfInBounds]
    rw [getD_of_lt hc', Array.set!, getD_of_lt hc2, Array.getElem_setIfInBounds hc']
    by_cases hcj : c = j
    · subst hcj
      simp [wsum_empty, getD_of_lt hc']
    · simp [Ne.symm hcj, hcj]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq', add_comm]
  by_cases hj : j < bk.size
  · simp [hj]
  · have : bk.getD j ∅ = ∅ := by
      unfold Array.getD
      rw [dif_neg hj]
    simp [hj, this, wsum_empty]

omit [LawfulBEq S] [LawfulHashable S] in
theorem size_emit (part : Nat → S → Nat) (P i j : Nat) (shard : HashMap S Nat) :
    (σ.emit part P i j shard).2.size = P := by
  simp only [emit]
  rw [Array.set!, Array.size_setIfInBounds, HashMap.fold_eq_foldl_toList]
  generalize shard.toList = l
  suffices ∀ init : Array (HashMap S Nat), init.size = P →
      (l.foldl (fun bk p => σ.pushStateB part P i (List.finRange k) p.1 p.2 bk) init).size = P
    from this _ Array.size_replicate
  induction l with
  | nil => exact fun _ h => h
  | cons _ _ ih =>
    intro init h
    exact ih _ (by rw [size_pushStateB, h])

theorem wsum_emit (part : Nat → S → Nat) (P i j : Nat) (shard : HashMap S Nat) (hP : 0 < P)
    (g : S → Nat) :
    wsum (σ.emit part P i j shard).1.2 g + wsumAll (σ.emit part P i j shard).2 g =
      wsum shard fun s => ∑ a : Fin k, (σ.step i s a).elim 0 g := by
  simp only [emit]
  rw [wsum_getD_add_wsumAll_set, HashMap.fold_eq_foldl_toList, ← sum_toList_eq_wsum]
  generalize shard.toList = l
  suffices ∀ init : Array (HashMap S Nat), init.size = P →
      wsumAll (l.foldl (fun bk p => σ.pushStateB part P i (List.finRange k) p.1 p.2 bk) init) g =
        wsumAll init g + (l.map fun p => p.2 * ∑ a : Fin k, (σ.step i p.1 a).elim 0 g).sum by
    rw [this _ Array.size_replicate, wsumAll_replicate, zero_add]
  induction l with
  | nil => intro init _; simp
  | cons p l ih =>
    intro init h
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih _ (by rw [size_pushStateB, h]), wsumAll_pushStateB σ part P i _ _ _ init hP h,
      Fin.sum_univ_def]
    omega

private theorem task_get_spawn {α : Type} (f : Unit → α) (prio : Task.Priority) :
    (Task.spawn f prio).get = f () := rfl

private theorem map_mapIdx {α β γ : Type} (xs : Array α) (f : Nat → α → β) (g : β → γ) :
    (xs.mapIdx f).map g = xs.mapIdx fun i a => g (f i a) := by
  ext i h1 h2 <;> simp

omit [LawfulBEq S] [LawfulHashable S] in
/-- `advancePar` without the tasks and the tuple patterns (definitional unfolding). -/
private theorem advancePar_eq (mkσ : Nat → Spec S L k) (mkPart : Nat → Nat → S → Nat)
    (P i : Nat) (cur : Array (HashMap S Nat)) :
    advancePar mkσ mkPart P i cur =
      ((cur.mapIdx fun j shard => (mkσ j).emit (mkPart j) P i j shard).map Prod.fst).map
        fun e =>
          ((cur.mapIdx fun j shard => (mkσ j).emit (mkPart j) P i j shard).map Prod.snd).foldl
            (fun acc out => mergeInto acc (out.getD e.1 ∅)) e.2 := by
  simp only [advancePar, Array.fst_unzip, Array.snd_unzip, map_mapIdx, task_get_spawn]

omit [LawfulBEq S] [LawfulHashable S] in
theorem size_advancePar (mkσ : Nat → Spec S L k) (mkPart : Nat → Nat → S → Nat)
    (P i : Nat) (cur : Array (HashMap S Nat)) :
    (advancePar mkσ mkPart P i cur).size = cur.size := by
  simp [advancePar_eq]

omit [LawfulBEq S] [LawfulHashable S] in
private theorem emit_fst_fst (part : Nat → S → Nat) (P i j : Nat) (shard : HashMap S Nat) :
    (σ.emit part P i j shard).1.1 = j := rfl

omit [LawfulBEq S] [LawfulHashable S] in
theorem getD_advancePar (mkσ : Nat → Spec S L k) (mkPart : Nat → Nat → S → Nat)
    (P i : Nat) (cur : Array (HashMap S Nat)) (b : Nat) (hb : b < cur.size) :
    (advancePar mkσ mkPart P i cur).getD b ∅ =
      ((cur.mapIdx fun j shard => (mkσ j).emit (mkPart j) P i j shard).map Prod.snd).foldl
        (fun acc out => mergeInto acc (out.getD b ∅))
        ((mkσ b).emit (mkPart b) P i b (cur.getD b ∅)).1.2 := by
  rw [advancePar_eq, getD_of_lt (by simpa using hb)]
  simp [getD_of_lt hb, emit_fst_fst]

theorem wsum_foldl_mergeInto (xs : Array (Array (HashMap S Nat))) (b : Nat)
    (init : HashMap S Nat) (g : S → Nat) :
    wsum (xs.foldl (fun acc out => mergeInto acc (out.getD b ∅)) init) g =
      wsum init g + ∑ j ∈ Finset.range xs.size, wsum ((xs.getD j #[]).getD b ∅) g := by
  rw [← Array.foldl_toList, ← array_sum_map_eq_range xs (fun out => wsum (out.getD b ∅) g) #[]]
  generalize xs.toList = l
  induction l generalizing init with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, wsum_mergeInto]
    omega

theorem wsumAll_advancePar (mkσ : Nat → Spec S L k) (mkPart : Nat → Nat → S → Nat)
    (h : ∀ j, mkσ j = σ) (P i : Nat) (cur : Array (HashMap S Nat))
    (hP : 0 < P) (hsz : cur.size = P) (g : S → Nat) :
    wsumAll (advancePar mkσ mkPart P i cur) g =
      wsumAll cur fun s => ∑ a : Fin k, (σ.step i s a).elim 0 g := by
  have hF : ∀ j ∈ Finset.range cur.size,
      ((cur.mapIdx fun j shard => (mkσ j).emit (mkPart j) P i j shard).map Prod.snd).getD j #[] =
        ((mkσ j).emit (mkPart j) P i j (cur.getD j ∅)).2 := by
    intro j hj
    have hj' : j < cur.size := Finset.mem_range.mp hj
    rw [getD_of_lt (by simpa using hj')]
    simp [getD_of_lt hj']
  unfold wsumAll
  rw [size_advancePar]
  calc ∑ b ∈ Finset.range cur.size, wsum ((advancePar mkσ mkPart P i cur).getD b ∅) g
      = ∑ b ∈ Finset.range cur.size, (wsum ((mkσ b).emit (mkPart b) P i b (cur.getD b ∅)).1.2 g +
          ∑ j ∈ Finset.range cur.size,
            wsum (((mkσ j).emit (mkPart j) P i j (cur.getD j ∅)).2.getD b ∅) g) := by
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [getD_advancePar mkσ mkPart P i cur b (Finset.mem_range.mp hb), wsum_foldl_mergeInto,
          Array.size_map, Array.size_mapIdx]
        refine congrArg (_ + ·) (Finset.sum_congr rfl fun j hj => ?_)
        rw [hF j hj]
    _ = ∑ j ∈ Finset.range cur.size, (wsum ((mkσ j).emit (mkPart j) P i j (cur.getD j ∅)).1.2 g +
          wsumAll ((mkσ j).emit (mkPart j) P i j (cur.getD j ∅)).2 g) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold wsumAll
        rw [size_emit, hsz]
    _ = ∑ j ∈ Finset.range cur.size,
          wsum (cur.getD j ∅) fun s => ∑ a : Fin k, (σ.step i s a).elim 0 g := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [wsum_emit (mkσ j) (mkPart j) P i j (cur.getD j ∅) hP g, h j]

omit [LawfulBEq S] [LawfulHashable S] in
theorem size_layersPar (mkσ : Nat → Spec S L k) (mkPart : Nat → Nat → S → Nat)
    (P j i : Nat) (ms : Array (HashMap S Nat)) :
    (layersPar mkσ mkPart P j i ms).size = ms.size := by
  induction j generalizing i ms with
  | zero => rfl
  | succ j ih =>
    simp only [layersPar]
    rw [ih, size_advancePar]

theorem wsumAll_layersPar (mkσ : Nat → Spec S L k) (mkPart : Nat → Nat → S → Nat)
    (h : ∀ j, mkσ j = σ) (P : Nat) (hP : 0 < P) (j i : Nat)
    (ms : Array (HashMap S Nat)) (hsz : ms.size = P) :
    wsumAll (layersPar mkσ mkPart P j i ms) (fun s => if σ.final s then 1 else 0) =
      wsumAll ms fun s => σ.compl j s i := by
  induction j generalizing i ms with
  | zero =>
    simp only [layersPar]
    congr 1
    funext s
    rw [compl_zero]
  | succ j ih =>
    simp only [layersPar]
    rw [ih _ _ (by rw [size_advancePar, hsz]), wsumAll_advancePar σ mkσ mkPart h P i ms hP hsz]
    congr 1
    funext s
    rw [compl_succ]

theorem finalSumAll_eq_wsumAll (ms : Array (HashMap S Nat)) :
    σ.finalSumAll ms = wsumAll ms fun s => if σ.final s then 1 else 0 := by
  unfold finalSumAll wsumAll
  rw [← Array.foldl_toList,
    ← array_sum_map_eq_range ms (fun m => wsum m fun s => if σ.final s then 1 else 0) ∅]
  simp only [← finalSum_eq_wsum]
  generalize ms.toList = l
  suffices ∀ init, l.foldl (fun acc m => acc + σ.finalSum m) init = init + (l.map σ.finalSum).sum
    by rw [this, zero_add]
  induction l with
  | nil => intro init; simp
  | cons m l ih =>
    intro init
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    omega

theorem wsumAll_init (n : Nat) (g : S → Nat) :
    wsumAll (#[(∅ : HashMap S Nat).insert σ.root 1] ++ Array.replicate n (∅ : HashMap S Nat)) g =
      g σ.root := by
  unfold wsumAll
  rw [Array.size_append, Array.size_replicate, List.size_toArray, List.length_singleton,
    add_comm, Finset.sum_range_succ']
  have h0 : ∀ b ∈ Finset.range n,
      wsum ((#[(∅ : HashMap S Nat).insert σ.root 1] ++ Array.replicate n ∅).getD (b + 1) ∅) g =
        0 := by
    intro b hb
    have hb' : b < n := Finset.mem_range.mp hb
    rw [getD_of_lt (by simp; omega), Array.getElem_append, dif_neg (by simp),
      Array.getElem_replicate, wsum_empty]
  rw [Finset.sum_eq_zero h0, zero_add, getD_of_lt (by simp; omega), Array.getElem_append,
    dif_pos (by simp)]
  exact σ.wsum_single g

/-- **Main theorem, parallel engine.** If every worker's spec is `mkσ 0`, then for every family
of partitions `mkPart` and shard count `P` the parallel engine returns the number of words
accepted by `mkσ 0`. -/
theorem countPar_eq (mkσ : Nat → Spec S L k) (mkPart : Nat → Nat → S → Nat) (P : Nat)
    (h : ∀ j, mkσ j = mkσ 0) :
    Spec.countPar mkσ mkPart P = Fintype.card (mkσ 0).Accepted := by
  unfold countPar
  have hP : 0 < max P 1 := lt_max_of_lt_right Nat.one_pos
  have hsz : (#[(∅ : HashMap S Nat).insert (mkσ 0).root 1] ++
      Array.replicate (max P 1 - 1) (∅ : HashMap S Nat)).size = max P 1 := by
    simp only [Array.size_append, Array.size_replicate, List.size_toArray, List.length_singleton]
    omega
  rw [finalSumAll_eq_wsumAll, wsumAll_layersPar (mkσ 0) mkσ mkPart h _ hP _ _ _ hsz,
    wsumAll_init]
  unfold compl
  exact (Fintype.card_subtype _).symm

end Correctness

end Spec

end Tally

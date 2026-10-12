/-!
# `UInt64` bit lemmas for packed frontier states

Facts about single-bit masks (`1 <<< c`, used by the one-bit-per-column state of
`GridIndep`) and about 3-bit fields (`getField`, `setField`, used by the
three-bits-per-column state of `BarArray`), stated through
`UInt64.toBitVec.getLsbD`. Field positions are `3 * c` for `c ≤ 20`, so every
field lies in the 64 bits of the word.
-/

namespace Tally.Bits

/-! ### Single bits -/

theorem bit_getLsbD (c : Nat) (hc : c < 64) (j : Nat) :
    ((1 : UInt64) <<< c.toUInt64).toBitVec.getLsbD j = (decide (j < 64) && decide (j = c)) := by
  simp [UInt64.toBitVec_shiftLeft, BitVec.getLsbD_shiftLeft, Nat.mod_eq_of_lt hc]
  by_cases h1 : j < 64 <;> by_cases h2 : j = c <;> simp_all <;> omega

theorem bitr_getLsbD (c : Nat) (hc : c < 64) (hc0 : 0 < c) (j : Nat) (hj : j < 64) :
    (((1 : UInt64) <<< c.toUInt64) >>> 1).toBitVec.getLsbD j = decide (j = c - 1) := by
  simp [UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft, BitVec.getLsbD_shiftLeft,
    Nat.mod_eq_of_lt hc]
  by_cases h1 : 1 + j < 64 <;> by_cases h2 : j = c - 1 <;> simp_all <;> omega

theorem and_single_ne_zero (s x : UInt64) (d : Nat) (hd : d < 64)
    (hx : ∀ j, j < 64 → x.toBitVec.getLsbD j = decide (j = d)) :
    ((s &&& x) != 0) = s.toBitVec.getLsbD d := by
  cases h : s.toBitVec.getLsbD d
  · simp only [bne_eq_false_iff_eq]
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [UInt64.toBitVec_and, BitVec.getLsbD_and, hx j hj, UInt64.toBitVec_zero, BitVec.getLsbD_zero]
    by_cases hjd : j = d
    · subst hjd; simp [h]
    · simp [hjd]
  · simp only [bne_iff_ne, ne_eq]
    intro h0
    have := congrArg (fun y : UInt64 => y.toBitVec.getLsbD d) h0
    simp [UInt64.toBitVec_and, BitVec.getLsbD_and, hx d hd, h] at this

theorem or_bit_getLsbD (s : UInt64) (c : Nat) (hc : c < 64) (j : Nat) (hj : j < 64) :
    (s ||| ((1 : UInt64) <<< c.toUInt64)).toBitVec.getLsbD j =
      (s.toBitVec.getLsbD j || decide (j = c)) := by
  rw [UInt64.toBitVec_or, BitVec.getLsbD_or, bit_getLsbD c hc j]
  simp [hj]

theorem andnot_bit_getLsbD (s : UInt64) (c : Nat) (hc : c < 64) (j : Nat) (hj : j < 64) :
    (s &&& ~~~((1 : UInt64) <<< c.toUInt64)).toBitVec.getLsbD j =
      (s.toBitVec.getLsbD j && !decide (j = c)) := by
  rw [UInt64.toBitVec_and, BitVec.getLsbD_and, UInt64.toBitVec_not, BitVec.getLsbD_not,
    bit_getLsbD c hc j]
  simp [hj]

/-! ### 3-bit fields -/

/-- Set the 3-bit field `c` of `s` to `v`. -/
def setField (s : UInt64) (c : Nat) (v : UInt64) : UInt64 :=
  (s &&& ~~~((7 : UInt64) <<< (3 * c).toUInt64)) ||| (v <<< (3 * c).toUInt64)

/-- The 3-bit field `c` of `s`. -/
def getField (s : UInt64) (c : Nat) : UInt64 := (s >>> (3 * c).toUInt64) &&& 7

theorem testBit_small (x q : Nat) (hx : x < 8) (hq : 3 ≤ q) : x.testBit q = false :=
  Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le hx (by simpa using Nat.pow_le_pow_right (show 0 < 2 by omega) hq))

theorem small_getLsbD (v : UInt64) (hv : v.toNat < 8) (q : Nat) (hq : 3 ≤ q) :
    v.toBitVec.getLsbD q = false := by
  rw [← BitVec.testBit_toNat]
  exact testBit_small _ _ hv hq

theorem seven_getLsbD (j : Nat) : (7#64).getLsbD j = decide (j < 3) := by
  by_cases hj : j < 3
  · obtain h | h | h : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    all_goals subst h; rfl
  · rw [BitVec.getLsbD_ofNat]
    simp [testBit_small 7 j (by omega) (by omega), hj]

theorem getField_getLsbD (x : UInt64) (c : Nat) (hc : c ≤ 20) (j : Nat) :
    (getField x c).toBitVec.getLsbD j = (decide (j < 3) && x.toBitVec.getLsbD (3 * c + j)) := by
  simp only [getField, UInt64.toBitVec_and, UInt64.toBitVec_shiftRight, BitVec.getLsbD_and]
  simp [Nat.mod_eq_of_lt (show 3 * c < 64 by omega), seven_getLsbD, Bool.and_comm]

theorem setField_getLsbD (s v : UInt64) (hv : v.toNat < 8) (c : Nat) (hc : c ≤ 20) (p : Nat)
    (hp : p < 64) :
    (setField s c v).toBitVec.getLsbD p =
      if 3 * c ≤ p ∧ p < 3 * c + 3 then v.toBitVec.getLsbD (p - 3 * c) else s.toBitVec.getLsbD p := by
  simp only [setField, UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_not, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not]
  simp [Nat.mod_eq_of_lt (show 3 * c < 64 by omega), seven_getLsbD]
  by_cases h1 : p < 3 * c
  · have : ¬ (3 * c ≤ p ∧ p < 3 * c + 3) := by omega
    simp [h1, this, hp]
  · by_cases h2 : p < 3 * c + 3
    · have : (3 * c ≤ p ∧ p < 3 * c + 3) := by omega
      have h3 : p - 3 * c < 3 := by omega
      simp [h1, this, hp, h3]
    · have : ¬ (3 * c ≤ p ∧ p < 3 * c + 3) := by omega
      have h3 : ¬ p - 3 * c < 3 := by omega
      simp [h1, this, hp, h3, small_getLsbD v hv (p - 3 * c) (by omega)]

theorem getField_setField (s v : UInt64) (hv : v.toNat < 8) (c c' : Nat) (hc : c ≤ 20)
    (hc' : c' ≤ 20) : getField (setField s c v) c' = if c' = c then v else getField s c' := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getField_getLsbD _ _ hc']
  by_cases hcc : c' = c
  · subst hcc
    rw [if_pos rfl]
    by_cases hj3 : j < 3
    · rw [setField_getLsbD s v hv c' hc _ (by omega), if_pos (by omega)]
      simp [hj3]
    · simp [hj3, small_getLsbD v hv j (by omega)]
  · rw [if_neg hcc, getField_getLsbD _ _ hc']
    by_cases hj3 : j < 3
    · rw [setField_getLsbD s v hv c hc _ (by omega), if_neg (by omega)]
    · simp [hj3]

theorem getField_zero (c : Nat) : getField 0 c = 0 := by simp [getField]

/-! ### Small values -/

theorem toUInt64_toNat_small (x : Nat) (hx : x < 8) : x.toUInt64.toNat = x := by
  simp; omega

theorem ne_of_toNat_ne {x y : UInt64} (h : x.toNat ≠ y.toNat) : x ≠ y :=
  fun e => h (congrArg UInt64.toNat e)

end Tally.Bits

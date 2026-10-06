import Mathlib.Tactic

/-!
# The exact small-power Schur arithmetic at eight and sixteen blocks

This file isolates the integer arithmetic in the noncentral binary row of
the degree-four zero-core argument.  For one simple binary type, `h` is its
ground-field dimension, `e` its dimension over the Schur division ring,
and `mE`, `mT` are its multiplicities in the translation and top terms of
the socle filtration.

The crude dimension bounds close every row except `(h,e)=(3,1)` and
`(h,e)=(2,1)`.  The former uses the cyclic-seven/derangement improvement
`3*mE <= s`; the latter uses the cyclic-three local analysis
`8*mE <= 3*s`.  Keeping this arithmetic separate prevents the group and
module transports from carrying a large Presburger proof.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- At the two finite frames, five-eighths of the block degree is exactly
the available integral slot count. -/
def degreeFourZeroCoreSchurSlots (s : ℕ) : ℕ :=
  if s = 8 then 5 else 10

theorem degreeFourZeroCoreSchurSlots_eq_five_eighths
    {s : ℕ} (hs : s = 8 ∨ s = 16) :
    8 * degreeFourZeroCoreSchurSlots s = 5 * s := by
  rcases hs with rfl | rfl <;>
    norm_num [degreeFourZeroCoreSchurSlots]

/-- The exact arithmetic behind the audited `d >= 4`, `d=3`, and `d=2`
split.  `hediv` is Schur's dimension-tower divisibility.  The two sharpened
translation premises are required only in the exceptional scalar rows;
they are stated conditionally so callers may pass their literal cyclic
kernel arguments without manufacturing unused estimates in the other rows.
-/
theorem degreeFourZeroCore_schurMultiplicity_add_le_slots_mul
    {s h e mE mT : ℕ}
    (hs : s = 8 ∨ s = 16)
    (hh : 2 ≤ h)
    (he : 1 ≤ e)
    (hediv : e ∣ h)
    (htranslation : h * mE ≤ 2 * s)
    (htop : 2 * h * mT ≤ s)
    (hthree : h = 3 → e = 1 → 3 * mE ≤ s)
    (htwo : h = 2 → e = 1 → 8 * mE ≤ 3 * s) :
    mE + mT ≤ degreeFourZeroCoreSchurSlots s * e := by
  have hslots := degreeFourZeroCoreSchurSlots_eq_five_eighths hs
  by_cases hh4 : 4 ≤ h
  · have hE4 : 4 * mE ≤ 2 * s :=
      (Nat.mul_le_mul_right mE hh4).trans htranslation
    have hT4 : 8 * mT ≤ s := by
      have h4 : 4 * mT ≤ h * mT := Nat.mul_le_mul_right mT hh4
      calc
        8 * mT = 2 * (4 * mT) := by omega
        _ ≤ 2 * (h * mT) := Nat.mul_le_mul_left 2 h4
        _ = 2 * h * mT := by simp [Nat.mul_assoc]
        _ ≤ s := htop
    have hsum : 8 * (mE + mT) ≤ 5 * s := by omega
    have hslot : mE + mT ≤ degreeFourZeroCoreSchurSlots s := by
      omega
    exact hslot.trans (Nat.le_mul_of_pos_right _ he)
  have hh_le : h ≤ 3 := by omega
  have hh_cases : h = 2 ∨ h = 3 := by omega
  rcases hh_cases with rfl | rfl
  · by_cases he1 : e = 1
    · have hE := htwo rfl he1
      have hT : 4 * mT ≤ s := by omega
      have hsum : 8 * (mE + mT) ≤ 5 * s := by omega
      rw [he1, Nat.mul_one]
      omega
    · have he2 : e = 2 := by
        have he_le : e ≤ 2 := Nat.le_of_dvd (by norm_num) hediv
        omega
      rw [he2]
      have hsum : 4 * (mE + mT) ≤ 5 * s := by omega
      omega
  · by_cases he1 : e = 1
    · have hE := hthree rfl he1
      have hT : 6 * mT ≤ s := by omega
      rw [he1, Nat.mul_one]
      have hsum : 6 * (mE + mT) ≤ 3 * s := by omega
      rcases hs with rfl | rfl <;>
        norm_num [degreeFourZeroCoreSchurSlots] at hsum ⊢ <;>
        omega
    · have he3 : e = 3 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hediv with h | h
        · exact (he1 h).elim
        · exact h
      rw [he3]
      have hsum : 6 * (mE + mT) ≤ 5 * s := by omega
      rcases hs with rfl | rfl <;>
        norm_num [degreeFourZeroCoreSchurSlots] at hsum ⊢ <;>
        omega

end SymmetricSubgroupAsymptotics

import SymmetricSubgroupAsymptotics.TernaryLocalWidth
import Mathlib.Algebra.Order.Ring.Nat

/-! Arithmetic for the self-proved ternary width route. All divisions are
natural-number divisions, taken before the fibre dimension is multiplied.
The exponent and coprime denominator are explicit: this file assumes no
induced-module theorem and does not import a Gaussian envelope. -/
set_option autoImplicit false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

def ternaryWidthCore (s t : ℕ) : ℕ :=
  if t = 0 then s else if t ≤ 2 then s / 3 else 7 * s / 27

def ternaryWidthEnvelope (s t L : ℕ) : ℕ :=
  min (ternaryWidthCore s t) (s / L)

@[simp] theorem ternaryWidthCore_zero (s : ℕ) : ternaryWidthCore s 0 = s := rfl

theorem ternaryWidthCore_eq_third (s t : ℕ) (h0 : t ≠ 0) (h2 : t ≤ 2) :
    ternaryWidthCore s t = s / 3 := by simp [ternaryWidthCore, h0, h2]

theorem ternaryWidthCore_eq_seven_twentyseven (s t : ℕ) (ht : 3 ≤ t) :
    ternaryWidthCore s t = 7 * s / 27 := by
  simp [ternaryWidthCore, show t ≠ 0 by omega, show ¬t ≤ 2 by omega]

theorem ternaryWidthEnvelope_le_core (s t L : ℕ) :
    ternaryWidthEnvelope s t L ≤ ternaryWidthCore s t := min_le_left _ _

theorem ternaryWidthEnvelope_le_coprime (s t L : ℕ) :
    ternaryWidthEnvelope s t L ≤ s / L := min_le_right _ _

theorem ternaryWidthEnvelope_mul_denominator_le (s t L : ℕ) :
    ternaryWidthEnvelope s t L * L ≤ s :=
  (Nat.mul_le_mul_right L (ternaryWidthEnvelope_le_coprime s t L)).trans
    (Nat.div_mul_le_self s L)

theorem ternaryWidthEnvelope_mul_four_le (s t L : ℕ) (hL : 4 ≤ L) :
    ternaryWidthEnvelope s t L * 4 ≤ s :=
  (Nat.mul_le_mul_left _ hL).trans
    (ternaryWidthEnvelope_mul_denominator_le s t L)

theorem ternaryWidthEnvelope_mul_twentyseven_le (s t L : ℕ) (ht : 3 ≤ t) :
    ternaryWidthEnvelope s t L * 27 ≤ 7 * s := by
  have h := ternaryWidthEnvelope_le_core s t L
  rw [ternaryWidthCore_eq_seven_twentyseven s t ht] at h
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mp h

theorem ternaryWidthEnvelope_mul_three_le_of_pos (s t L : ℕ) (ht : 1 ≤ t) :
    ternaryWidthEnvelope s t L * 3 ≤ s := by
  by_cases h3 : 3 ≤ t
  · have h := ternaryWidthEnvelope_mul_twentyseven_le s t L h3
    omega
  · have h := ternaryWidthEnvelope_le_core s t L
    rw [ternaryWidthCore_eq_third s t (by omega) (by omega)] at h
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mp h

/-- Mixed orbit sizes are allowed. Only the actual size sum and the lower
bound on every orbit exponent enter the coefficient. -/
theorem ternaryLocalWidth_sum_le_core {ι : Type*} [Fintype ι]
    (j : ι → ℕ) (s t : ℕ) (hj : ∀ i, t ≤ j i)
    (hs : ∑ i, 3 ^ j i = s) :
    ∑ i, ternaryLocalWidth (j i) ≤ ternaryWidthCore s t := by
  by_cases h0 : t = 0
  · subst t
    rw [ternaryWidthCore_zero, ← hs]
    exact Finset.sum_le_sum (fun i _ => ternaryLocalWidth_le_pow (j i))
  · by_cases h2 : t ≤ 2
    · rw [ternaryWidthCore_eq_third s t h0 h2]
      exact ternaryLocalWidth_sum_le_third j s (fun i => by have := hj i; omega) hs
    · rw [ternaryWidthCore_eq_seven_twentyseven s t (by omega)]
      exact (ternaryLocalWidth_sum_eq_seven_twentyseven j s
        (fun i => by have := hj i; omega) hs).le

theorem ternaryLocalWidth_weighted_sum_le_core {ι : Type*} [Fintype ι]
    (a : ℕ) (j : ι → ℕ) (s t : ℕ) (hj : ∀ i, t ≤ j i)
    (hs : ∑ i, 3 ^ j i = s) :
    ∑ i, a * ternaryLocalWidth (j i) ≤ a * ternaryWidthCore s t := by
  rw [← Finset.mul_sum]
  exact Nat.mul_le_mul_left a (ternaryLocalWidth_sum_le_core j s t hj hs)

/-- The precise factor information needed for the numerical endpoints.
For the canonical envelope, install `t = s.factorization 3`,
`m = ordCompl[3] s`, and `L = largestPrimePower m` separately. -/
structure TernaryWidthFactors (s t m L : ℕ) : Prop where
  eq_mul : s = 3 ^ t * m
  not_dvd : ¬3 ∣ m
  denominator_one : m = 1 → L = 1
  denominator_two : m = 2 → L = 2
  denominator_large : m ≠ 1 → m ≠ 2 → 4 ≤ L

theorem TernaryWidthFactors.part_pos {s t m L : ℕ}
    (h : TernaryWidthFactors s t m L) : 0 < m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  exact h.not_dvd (by simp [hm0])

theorem TernaryWidthFactors.exponent_le_two {s t m L : ℕ}
    (h : TernaryWidthFactors s t m L) (hs : s < 27) : t ≤ 2 := by
  have hp : 3 ^ t ≤ s := by
    rw [h.eq_mul]
    simpa using Nat.mul_le_mul_left (3 ^ t) (show 1 ≤ m by have := h.part_pos; omega)
  by_contra ht
  have h27 : 3 ^ 3 ≤ 3 ^ t := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at h27
  omega

/-- The one-third envelope includes all indices at least three, including
the scalar exceptional indices six and eighteen. -/
theorem ternaryWidthEnvelope_le_third {s t m L : ℕ}
    (h : TernaryWidthFactors s t m L) (hs : 3 ≤ s) :
    ternaryWidthEnvelope s t L ≤ s / 3 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
  by_cases ht : t = 0
  · have hm : s = m := by simpa [ht] using h.eq_mul
    have hL := h.denominator_large (by omega) (by omega)
    have hb := ternaryWidthEnvelope_mul_four_le s t L hL
    omega
  · exact ternaryWidthEnvelope_mul_three_le_of_pos s t L (by omega)

theorem ternaryWidthEnvelope_scalar_tail (s t L : ℕ) (ht : 3 ≤ t) :
    ternaryWidthEnvelope s t L + 5 * s / 27 ≤ 9 * s / 20 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 20)).mpr
  have hb := ternaryWidthEnvelope_mul_twentyseven_le s t L ht
  have hf := Nat.div_mul_le_self (5 * s) 27
  omega

theorem ternaryWidthEnvelope_scalar_quarter (s t L : ℕ) (hL : 4 ≤ L) :
    ternaryWidthEnvelope s t L + 5 * s / 27 ≤ 9 * s / 20 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 20)).mpr
  have hb := ternaryWidthEnvelope_mul_four_le s t L hL
  have hf := Nat.div_mul_le_self (5 * s) 27
  omega

/-- The scalar ternary endpoint leaves precisely three small indices;
their actual top-group refinements or finite bases remain separate inputs. -/
theorem ternaryWidthEnvelope_scalar {s t m L : ℕ}
    (h : TernaryWidthFactors s t m L) (hs : 2 ≤ s)
    (h2 : s ≠ 2) (h6 : s ≠ 6) (h18 : s ≠ 18) :
    ternaryWidthEnvelope s t L + 5 * s / 27 ≤ 9 * s / 20 := by
  by_cases ht : 3 ≤ t
  · exact ternaryWidthEnvelope_scalar_tail s t L ht
  have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  by_cases hm1 : m = 1
  · have hL := h.denominator_one hm1
    rcases ht' with rfl | rfl | rfl
    · have he : s = 1 := by simpa [hm1] using h.eq_mul
      omega
    · have he : s = 3 := by simpa [hm1] using h.eq_mul
      subst s
      norm_num [ternaryWidthEnvelope, ternaryWidthCore, hL]
    · have he : s = 9 := by simpa [hm1] using h.eq_mul
      subst s
      norm_num [ternaryWidthEnvelope, ternaryWidthCore, hL]
  · by_cases hm2 : m = 2
    · rcases ht' with rfl | rfl | rfl
      · have he : s = 2 := by simpa [hm2] using h.eq_mul
        exact (h2 he).elim
      · have he : s = 6 := by simpa [hm2] using h.eq_mul
        exact (h6 he).elim
      · have he : s = 18 := by simpa [hm2] using h.eq_mul
        exact (h18 he).elim
    · exact ternaryWidthEnvelope_scalar_quarter s t L (h.denominator_large hm1 hm2)

theorem ternaryWidthEnvelope_two {t m L : ℕ}
    (h : TernaryWidthFactors 2 t m L) : ternaryWidthEnvelope 2 t L = 1 := by
  have ht := h.exponent_le_two (by decide)
  have he := h.eq_mul
  have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases ht' with rfl | rfl | rfl
  · have hm : m = 2 := by simpa using he.symm
    norm_num [ternaryWidthEnvelope, ternaryWidthCore, h.denominator_two hm]
  · norm_num at he
    omega
  · norm_num at he
    omega

theorem ternaryWidthEnvelope_six {t m L : ℕ}
    (h : TernaryWidthFactors 6 t m L) : ternaryWidthEnvelope 6 t L = 2 := by
  have ht := h.exponent_le_two (by decide)
  have he := h.eq_mul
  have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases ht' with rfl | rfl | rfl
  · have hm : m = 6 := by simpa using he.symm
    exact (h.not_dvd (by simp [hm])).elim
  · have hm : m = 2 := by norm_num at he; omega
    norm_num [ternaryWidthEnvelope, ternaryWidthCore, h.denominator_two hm]
  · norm_num at he
    omega

theorem ternaryWidthEnvelope_eighteen {t m L : ℕ}
    (h : TernaryWidthFactors 18 t m L) : ternaryWidthEnvelope 18 t L = 6 := by
  have ht := h.exponent_le_two (by decide)
  have he := h.eq_mul
  have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases ht' with rfl | rfl | rfl
  · have hm : m = 18 := by simpa using he.symm
    exact (h.not_dvd (by simp [hm])).elim
  · have hm : m = 6 := by norm_num at he; omega
    exact (h.not_dvd (by simp [hm])).elim
  · have hm : m = 2 := by norm_num at he; omega
    norm_num [ternaryWidthEnvelope, ternaryWidthCore, h.denominator_two hm]

theorem ternaryWidthEnvelope_scalar_failure_iff {s t m L : ℕ}
    (h : TernaryWidthFactors s t m L) (hs : 2 ≤ s) :
    9 * s / 20 < ternaryWidthEnvelope s t L + 5 * s / 27 ↔
      s = 2 ∨ s = 6 ∨ s = 18 := by
  constructor
  · intro hf
    by_contra he
    have hb := ternaryWidthEnvelope_scalar h hs (by omega) (by omega) (by omega)
    omega
  · rintro (rfl | rfl | rfl)
    · rw [ternaryWidthEnvelope_two h]
      norm_num
    · rw [ternaryWidthEnvelope_six h]
      norm_num
    · rw [ternaryWidthEnvelope_eighteen h]
      norm_num

/-- An actual top head at most two closes the index-eighteen scalar seam. -/
theorem ternaryWidthEnvelope_eighteen_top_two {t m L : ℕ}
    (h : TernaryWidthFactors 18 t m L) :
    ternaryWidthEnvelope 18 t L + 2 ≤ 9 * 18 / 20 := by
  rw [ternaryWidthEnvelope_eighteen h]

end SymmetricSubgroupAsymptotics

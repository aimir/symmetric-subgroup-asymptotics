import SymmetricSubgroupAsymptotics.ChiefTernaryOrderBound
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.Coset.Card

/-! Bounds on the genuine weight of any chosen chief series of an actual
permutation subgroup. Lagrange's theorem bounds the original group-order
valuation by the factorial valuation of the original point set.

Only inequalities are asserted: neither the group-order valuation nor the
factorial valuation is identified with chief weight or composition length.
No primitivity, classification, or literature hypothesis is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {X : Type} [Finite X]

/-- The original subgroup's chosen chief weight is bounded by the ternary
valuation of the symmetric group on its actual point set. -/
theorem permutationChiefWeight_le_factorial
    (U : Subgroup (Equiv.Perm X)) (s : ActualChiefSeries U) :
    actualChiefSeriesTernaryWeight s ≤ ((Nat.card X).factorial).factorization 3 := by
  have hdvd : Nat.card U ∣ (Nat.card X).factorial := by
    simpa only [Nat.card_perm] using U.card_subgroup_dvd_card
  have hval : (Nat.card U).factorization ≤ ((Nat.card X).factorial).factorization :=
    (Nat.factorization_le_iff_dvd (Nat.card_pos (α := U)).ne'
      (Nat.factorial_ne_zero _)).mpr hdvd
  exact (actualChiefSeriesTernaryWeight_le_order s).trans (hval 3)

private theorem factorial_ternary_mono {r t : ℕ} (h : r ≤ t) :
    (r.factorial).factorization 3 ≤ (t.factorial).factorization 3 :=
  ((Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)).mpr
    (Nat.factorial_dvd_factorial h)) 3

private theorem factorial_two_ternary : ((2 : ℕ).factorial).factorization 3 = 0 := by
  decide +kernel

private theorem factorial_five_ternary : ((5 : ℕ).factorial).factorization 3 = 1 := by
  decide +kernel

private theorem factorial_eight_ternary : ((8 : ℕ).factorial).factorization 3 = 2 := by
  decide +kernel

theorem permutationChiefWeight_eq_zero_of_card_le_two
    (U : Subgroup (Equiv.Perm X)) (s : ActualChiefSeries U) (hX : Nat.card X ≤ 2) :
    actualChiefSeriesTernaryWeight s = 0 := by
  have h := (permutationChiefWeight_le_factorial U s).trans (factorial_ternary_mono hX)
  rw [factorial_two_ternary] at h
  exact Nat.eq_zero_of_le_zero h

/-- In particular, all actual degree-three, four, and five components have
chosen-chief ternary weight at most one. -/
theorem permutationChiefWeight_le_one_of_card_le_five
    (U : Subgroup (Equiv.Perm X)) (s : ActualChiefSeries U) (hX : Nat.card X ≤ 5) :
    actualChiefSeriesTernaryWeight s ≤ 1 := by
  have h := (permutationChiefWeight_le_factorial U s).trans (factorial_ternary_mono hX)
  simpa only [factorial_five_ternary] using h

theorem permutationChiefWeight_le_two_of_card_le_eight
    (U : Subgroup (Equiv.Perm X)) (s : ActualChiefSeries U) (hX : Nat.card X ≤ 8) :
    actualChiefSeriesTernaryWeight s ≤ 2 := by
  have h := (permutationChiefWeight_le_factorial U s).trans (factorial_ternary_mono hX)
  simpa only [factorial_eight_ternary] using h

/-- The ordinary component-weight premise throughout degrees three to eight. -/
theorem permutationChiefWeight_ordinary_small
    (U : Subgroup (Equiv.Perm X)) (s : ActualChiefSeries U)
    (hlo : 3 ≤ Nat.card X) (hhi : Nat.card X ≤ 8) :
    3 * actualChiefSeriesTernaryWeight s ≤ Nat.card X := by
  by_cases h5 : Nat.card X ≤ 5
  · have h := permutationChiefWeight_le_one_of_card_le_five U s h5
    omega
  · have h := permutationChiefWeight_le_two_of_card_le_eight U s hhi
    omega

/-- Strict density for the small degrees where the factorial bound suffices.
Degrees three, six, and nine are not asserted to satisfy this conclusion. -/
theorem permutationChiefWeight_strict_small
    (U : Subgroup (Equiv.Perm X)) (s : ActualChiefSeries U)
    (hX : Nat.card X = 2 ∨ Nat.card X = 4 ∨ Nat.card X = 5 ∨
      Nat.card X = 7 ∨ Nat.card X = 8) :
    10 * actualChiefSeriesTernaryWeight s < 3 * Nat.card X := by
  by_cases h2 : Nat.card X ≤ 2
  · have h := permutationChiefWeight_eq_zero_of_card_le_two U s h2
    omega
  · by_cases h5 : Nat.card X ≤ 5
    · have h := permutationChiefWeight_le_one_of_card_le_five U s h5
      omega
    · have h := permutationChiefWeight_le_two_of_card_le_eight U s (by omega)
      omega

end SymmetricSubgroupAsymptotics

import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
import SymmetricSubgroupAsymptotics.McIverNeumannPermutationSection
import SymmetricSubgroupAsymptotics.IntransitiveOrdinaryGeneratorInduction
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Shared-dependency reduction of sharp ordinary generation. The
already retained Tracey permutation input pays every transitive degree
at least 22. Only genuinely bounded transitive cases are left; the
intransitive branch is assembled by the proved smaller-action step.
The bounded input below is explicitly unresolved, not a published theorem
or a newly discharged parameter of T1. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.McIverNeumannFromTraceyBounded

theorem tracey_ceiling_le_half (n : ℕ) (hn : 22 ≤ n) :
    traceyPermutationGeneratorCeiling n ≤ n / 2 := by
  have hnR : (22 : ℝ) ≤ n := by exact_mod_cast hn
  have hpowN : (2 : ℕ)^441 ≤ 22^100 := by decide +kernel
  have hpow : (2 : ℝ)^441 ≤ (n : ℝ)^100 :=
    (show (2 : ℝ)^441 ≤ (22 : ℝ)^100 by exact_mod_cast hpowN).trans
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 22) hnR 100)
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 2^441) hpow
  rw [Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hl
  norm_num at hl
  have hs : (21 / 10 : ℝ) ≤ Real.sqrt (Real.logb 2 n) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hp : 0 < Real.sqrt (Real.logb 2 n) := lt_of_lt_of_le (by norm_num) hs
  have hqN : n ≤ 2*(n/2) + 1 := by omega
  have hq : (n : ℝ) ≤ 2*(n/2 : ℕ) + 1 := by exact_mod_cast hqN
  unfold traceyPermutationGeneratorCeiling
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hp).mpr
  have hnonneg : (0 : ℝ) ≤ (n/2 : ℕ) := Nat.cast_nonneg _
  nlinarith

/-- Even degrees have no ceiling-rounding loss once the logarithm reaches four. -/
theorem tracey_ceiling_le_half_of_even (n : ℕ) (hn : 16 ≤ n) (heven : Even n) :
    traceyPermutationGeneratorCeiling n ≤ n / 2 := by
  have hpow : (2 : ℝ)^4 ≤ (n : ℝ) := by norm_num; exact_mod_cast hn
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2^4) hpow
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hl
  norm_num at hl
  have hs : (2 : ℝ) ≤ Real.sqrt (Real.logb 2 n) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hp : 0 < Real.sqrt (Real.logb 2 n) := lt_of_lt_of_le (by norm_num) hs
  have heq : 2*(n/2) = n := by obtain ⟨k, hk⟩ := heven; omega
  have heqR : (n : ℝ) = 2*(n/2 : ℕ) := by exact_mod_cast heq.symm
  unfold traceyPermutationGeneratorCeiling
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hp).mpr
  have hnonneg : (0 : ℝ) ≤ (n/2 : ℕ) := Nat.cast_nonneg _
  nlinarith

/-- The remaining cases are literal transitive subgroups below 22,
with the full S3 exception unchanged. No classifier is assumed implicitly. -/
def BoundedTransitiveInput : Prop :=
  ∀ (n : ℕ), n < 22 → ∀ J : Subgroup (Equiv.Perm (Fin n)),
    MulAction.IsPretransitive J (Fin n) → (n = 3 → J ≠ ⊤) →
      ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2*S.card ≤ n

theorem mcIverNeumann_of_tracey_and_bounded_transitive
    (hTracey : TraceyPermutationGeneratorInput) (hsmall : BoundedTransitiveInput) :
    McIverNeumannPermutationGeneratorBound := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J hJ
    by_cases ht : MulAction.IsPretransitive J (Fin n)
    · by_cases hn : n < 22
      · exact hsmall n hn J ht hJ
      · obtain ⟨S, hS, hc⟩ := hTracey n J (by omega) ht
        refine ⟨S, hS, ?_⟩
        have hh := hc.trans (tracey_ceiling_le_half n (by omega))
        omega
    · exact IntransitiveOrdinaryGeneratorInduction.subgroup_half_degree_generators n J ht ih

/-- The sharper unpaid degree set after also using the even-degree bound.
This is still an unresolved bounded input, not a classification theorem. -/
def UnpaidTransitiveInput : Prop :=
  ∀ (n : ℕ), (n < 16 ∨ n = 17 ∨ n = 19 ∨ n = 21) →
    ∀ J : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPretransitive J (Fin n) → (n = 3 → J ≠ ⊤) →
        ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2*S.card ≤ n

theorem mcIverNeumann_of_tracey_and_unpaid_transitive
    (hTracey : TraceyPermutationGeneratorInput) (hsmall : UnpaidTransitiveInput) :
    McIverNeumannPermutationGeneratorBound := by
  apply mcIverNeumann_of_tracey_and_bounded_transitive hTracey
  intro n hn J ht hJ
  by_cases hlow : n < 16
  · exact hsmall n (Or.inl hlow) J ht hJ
  · by_cases hodd : n = 17 ∨ n = 19 ∨ n = 21
    · exact hsmall n (Or.inr hodd) J ht hJ
    · have heven : Even n := by
        have hn' : n = 16 ∨ n = 18 ∨ n = 20 := by omega
        rcases hn' with rfl | rfl | rfl <;> decide
      obtain ⟨S, hS, hc⟩ := hTracey n J (by omega) ht
      refine ⟨S, hS, ?_⟩
      have hh := hc.trans (tracey_ceiling_le_half_of_even n (by omega) heven)
      omega

end SymmetricSubgroupAsymptotics.McIverNeumannFromTraceyBounded

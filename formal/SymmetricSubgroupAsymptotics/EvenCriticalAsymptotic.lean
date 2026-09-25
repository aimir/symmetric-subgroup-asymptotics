import SymmetricSubgroupAsymptotics.WeightedCriticalAssembly
import SymmetricSubgroupAsymptotics.PerturbedQuartic
import SymmetricSubgroupAsymptotics.CriticalCanonicalProfiles

/-!
# Exponentially accurate even critical-family count

The literal labelled subgroup family is assembled with its original
normalizer weights. The canonical coordinate deficit and the complete
noncanonical incidence contribution are both included.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter

namespace SymmetricSubgroupAsymptotics

private theorem evenCriticalSubgroups_relative_error_assemble
    (hmodel : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ p : CriticalProfile, N ≤ p.rank →
        |(Nat.card (CriticalModelSubgroups p) : ℝ) / (binaryGaussianSum p.rank : ℝ) - 1| ≤
          C*((p.rank : ℝ)*(2 : ℝ)^(-(p.rank : ℝ)/2) +
            (2 : ℝ)^(-((p.c2 : ℝ)/2 + p.v4 + p.e8)))) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ R : ℕ, N ≤ R →
      |(Nat.card (EvenCriticalSubgroups R) : ℝ) / exactBenchmark (2*R) - 1| ≤
        K*(2 : ℝ)^(-(R : ℝ)/32) := by
  obtain ⟨C,hC,N,hN,hprofile⟩ := hmodel
  obtain ⟨M,hM,hperturb⟩ := perturbedProfileCoefficient_ratio_exponential
  have hlinear := eventually_rank_mul_exponential_le (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨L,hL⟩ := eventually_atTop.mp hlinear
  refine ⟨C*(1+256*Real.pi),by positivity,max N (max M L),by omega,?_⟩
  intro R hR
  have hRN : N ≤ R := by omega
  have hRM : M ≤ R := by omega
  have hRL : L ≤ R := by omega
  have hG : (binaryGaussianSum R : ℝ) = binarySubspaceCount R := by
    exact_mod_cast (binarySubspaceCount_eq_gaussianSum R).symm
  have hp (p : CriticalProfile) (hp : p ∈ criticalProfiles R) :
      |(Nat.card (CriticalModelSubgroups p) : ℝ) / binarySubspaceCount R - 1| ≤
        C*((R : ℝ)*(2 : ℝ)^(-(R : ℝ)/2)) +
          C*(2 : ℝ)^(-((p.c2 : ℝ)/2 + p.v4 + p.e8)) := by
    have hr := (mem_criticalProfiles R p).mp hp
    have hh := hprofile p (by omega)
    rw [hr,hG] at hh
    nlinarith
  have h := evenCriticalSubgroups_relative_error_of_profiles R
    (C*((R : ℝ)*(2 : ℝ)^(-(R : ℝ)/2)))
    (fun p ↦ C*(2 : ℝ)^(-((p.c2 : ℝ)/2 + p.v4 + p.e8))) hp
  have hsum : (∑ p : (criticalProfiles R), (p.1.weight : ℝ) *
      (C*(2 : ℝ)^(-((p.1.c2 : ℝ)/2 + p.1.v4 + p.1.e8)))) =
      C*perturbedProfileCoefficient R := by
    unfold perturbedProfileCoefficient
    calc
      _ = C*(∑ p : (criticalProfiles R), (p.1.weight : ℝ) *
          (2 : ℝ)^(-((p.1.c2 : ℝ)/2 + p.1.v4 + p.1.e8))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ = _ := by
        congr 1
        exact Finset.sum_coe_sort (criticalProfiles R)
          (fun p ↦ (p.weight : ℝ)*(2 : ℝ)^(-((p.c2 : ℝ)/2 + p.v4 + p.e8)))
  rw [hsum] at h
  have hlin : (R : ℝ)*(2 : ℝ)^(-(R : ℝ)/2) ≤ (2 : ℝ)^(-(R : ℝ)/32) := by
    calc
      _ ≤ (2 : ℝ)^(-(R : ℝ)/4) := by
        convert hL R hRL using 1 <;> congr 2 <;> ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) R])
  calc
    _ ≤ C*((R : ℝ)*(2 : ℝ)^(-(R : ℝ)/2)) +
        (C*perturbedProfileCoefficient R)/(criticalCoefficient R : ℝ) := h
    _ = C*((R : ℝ)*(2 : ℝ)^(-(R : ℝ)/2) +
        perturbedProfileCoefficient R/(criticalCoefficient R : ℝ)) := by ring
    _ ≤ C*((2 : ℝ)^(-(R : ℝ)/32) +
        (256*Real.pi)*(2 : ℝ)^(-(R : ℝ)/32)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hlin (hperturb R hRM)) hC.le
    _ = _ := by ring

/-- The complete even critical family has an unconditional exponentially
small relative error with respect to the approved exact benchmark. -/
theorem evenCriticalSubgroups_relative_error :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ R : ℕ, N ≤ R →
      |(Nat.card (EvenCriticalSubgroups R) : ℝ) / exactBenchmark (2*R) - 1| ≤
        K*(2 : ℝ)^(-(R : ℝ)/32) :=
  evenCriticalSubgroups_relative_error_assemble criticalModelSubgroups_relative_error

/-- The literal critical family supplies the same quantitative lower bound
for all labelled subgroups of the even-degree symmetric group. -/
theorem subgroupCount_even_lower :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ R : ℕ, N ≤ R →
      1-K*(2 : ℝ)^(-(R : ℝ)/32) ≤
        (subgroupCount (2*R) : ℝ)/exactBenchmark (2*R) := by
  obtain ⟨K,hK,N,hN,h⟩ := evenCriticalSubgroups_relative_error
  refine ⟨K,hK,N,hN,?_⟩
  intro R hR
  have hl := (abs_le.mp (h R hR)).1
  have hc : (Nat.card (EvenCriticalSubgroups R) : ℝ) ≤ subgroupCount (2*R) := by
    exact_mod_cast evenCriticalSubgroups_card_le_subgroupCount R
  have hd := div_le_div_of_nonneg_right hc (exactBenchmark_pos (2*R)).le
  linarith

end SymmetricSubgroupAsymptotics

import SymmetricSubgroupAsymptotics.EvenCriticalAsymptotic
import SymmetricSubgroupAsymptotics.OddCriticalProfiles
import SymmetricSubgroupAsymptotics.OddProfileAssembly

/-!
# Exponentially accurate odd critical-family count

The singleton and S3 sectors retain their original relative marker weight
`1/6`. Their model counts have common binary rank `R`; the S3 sector is
identified with the actual full binary model obtained by adding one C2 block.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter

namespace SymmetricSubgroupAsymptotics

/-- Exact normalization of the two actual odd marker sectors. -/
theorem oddCriticalSubgroups_normalized (R : ℕ) (hR : 0 < R) :
    (Nat.card (OddCriticalSubgroups R) : ℝ) / exactBenchmark (2*R+1) =
      ((∑ p : (criticalProfiles R), (p.1.weight : ℝ) * Nat.card (CriticalModelSubgroups p.1)) +
        (1/6 : ℝ)*(∑ p : (criticalProfiles (R-1)), (p.1.weight : ℝ) *
          Nat.card (CriticalModelSubgroups p.1.addC2))) /
      ((binarySubspaceCount R : ℝ)*(criticalCoefficient R : ℝ) +
        (1/6 : ℝ)*((binarySubspaceCount R : ℝ)*(criticalCoefficient (R-1) : ℝ))) := by
  have hc : (Nat.card (OddCriticalSubgroups R) : ℝ) =
      ((2*R+1).factorial : ℝ) *
        ((∑ p : (criticalProfiles R), (p.1.weight : ℝ) * Nat.card (CriticalModelSubgroups p.1)) +
          (∑ p : (criticalProfiles (R-1)), (p.1.weight : ℝ) *
            Nat.card (CriticalModelSubgroups p.1.addC2))/6) := by
    have h := oddCriticalSubgroups_card R hR
    simp_rw [oddSingletonModel_card,oddS3Model_card] at h
    exact_mod_cast h
  have hG : (binaryGaussianSum R : ℝ) = binarySubspaceCount R := by
    exact_mod_cast (binarySubspaceCount_eq_gaussianSum R).symm
  have hf : ((2*R+1).factorial : ℝ) ≠ 0 := by positivity
  have hh : halfDegree (2*R+1) = R := by unfold halfDegree; omega
  have hp : parity (2*R+1) = 1 := by unfold parity; omega
  rw [hc,exactBenchmark,hh,parityCoefficient,hp,hh]
  simp only [hR,true_and,↓reduceIte,hG]
  push_cast
  field_simp

private theorem criticalWeightedSector_relative_error
    (k R : ℕ) (f : CriticalProfile → ℕ) (C : ℝ)
    (hp : ∀ p ∈ criticalProfiles k,
      |(f p : ℝ)/(binarySubspaceCount R : ℝ)-1| ≤
        C*((R : ℝ)*(2 : ℝ)^(-(R : ℝ)/2) +
          (2 : ℝ)^(-((p.c2 : ℝ)/2+p.v4+p.e8)))) :
    |(∑ p : (criticalProfiles k), (p.1.weight : ℝ)*(f p.1 : ℝ)) /
      ((binarySubspaceCount R : ℝ)*(criticalCoefficient k : ℝ))-1| ≤
      C*((R : ℝ)*(2 : ℝ)^(-(R : ℝ)/2) +
        perturbedProfileCoefficient k/(criticalCoefficient k : ℝ)) := by
  have h := finite_weighted_relative_error
    (fun p : (criticalProfiles k) ↦ (p.1.weight : ℝ))
    (fun p ↦ (f p.1 : ℝ))
    (fun p ↦ C*(2 : ℝ)^(-((p.1.c2 : ℝ)/2+p.1.v4+p.1.e8)))
    (binarySubspaceCount R : ℝ) (C*((R : ℝ)*(2 : ℝ)^(-(R : ℝ)/2)))
    (fun p ↦ by change (0 : ℝ) ≤ (p.1.weight : ℝ); exact_mod_cast p.1.weight_pos.le)
    (by rw [criticalProfile_weight_sum_real]; exact_mod_cast criticalCoefficient_pos k)
    (by exact_mod_cast binarySubspaceCount_pos R)
    (fun p ↦ by simpa only [mul_add] using hp p.1 p.2)
  rw [criticalProfile_weight_sum_real] at h
  have hs : (∑ p : (criticalProfiles k), (p.1.weight : ℝ) *
      (C*(2 : ℝ)^(-((p.1.c2 : ℝ)/2+p.1.v4+p.1.e8)))) =
      C*perturbedProfileCoefficient k := by
    unfold perturbedProfileCoefficient
    calc
      _ = C*(∑ p : (criticalProfiles k), (p.1.weight : ℝ) *
          (2 : ℝ)^(-((p.1.c2 : ℝ)/2+p.1.v4+p.1.e8))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ = _ := by
        congr 1
        exact Finset.sum_coe_sort (criticalProfiles k)
          (fun p ↦ (p.weight : ℝ)*(2 : ℝ)^(-((p.c2 : ℝ)/2+p.v4+p.e8)))
  rw [hs] at h
  convert h using 1
  ring

private theorem markedCriticalSector_relative_error :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ R : ℕ, N ≤ R →
      |(∑ p : (criticalProfiles (R-1)), (p.1.weight : ℝ) *
          Nat.card (CriticalModelSubgroups p.1.addC2)) /
        ((binarySubspaceCount R : ℝ)*(criticalCoefficient (R-1) : ℝ))-1| ≤
        K*(2 : ℝ)^(-(R : ℝ)/32) := by
  obtain ⟨C,hC,N,hN,hmodel⟩ := criticalModelSubgroups_relative_error
  obtain ⟨M,hM,hperturb⟩ := perturbedProfileCoefficient_ratio_exponential
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    (eventually_rank_mul_exponential_le (by norm_num : (0 : ℝ) < 1/2))
  refine ⟨C*(1+512*Real.pi),by positivity,max N (max (M+1) L),by omega,?_⟩
  intro R hR
  have hRN : N ≤ R := by omega
  have hRM : M ≤ R-1 := by omega
  have hRL : L ≤ R := by omega
  have hR0 : 0 < R := by omega
  have hcast : ((R-1 : ℕ) : ℝ) = (R : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hG : (binaryGaussianSum R : ℝ) = binarySubspaceCount R := by
    exact_mod_cast (binarySubspaceCount_eq_gaussianSum R).symm
  have hp (p : CriticalProfile) (hp : p ∈ criticalProfiles (R-1)) :
      |(Nat.card (CriticalModelSubgroups p.addC2) : ℝ)/(binarySubspaceCount R : ℝ)-1| ≤
        C*((R : ℝ)*(2 : ℝ)^(-(R : ℝ)/2) +
          (2 : ℝ)^(-((p.c2 : ℝ)/2+p.v4+p.e8))) := by
    have hr : p.addC2.rank = R := by rw [CriticalProfile.addC2_rank,(mem_criticalProfiles _ p).mp hp]; omega
    have h := hmodel p.addC2 (by omega)
    rw [hr,hG] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply add_le_add le_rfl
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simp only [CriticalProfile.addC2,Nat.cast_add,Nat.cast_one]
    linarith
  have h := criticalWeightedSector_relative_error (R-1) R
    (fun p ↦ Nat.card (CriticalModelSubgroups p.addC2)) C hp
  have hlin : (R : ℝ)*(2 : ℝ)^(-(R : ℝ)/2) ≤ (2 : ℝ)^(-(R : ℝ)/32) := by
    calc
      _ ≤ (2 : ℝ)^(-(R : ℝ)/4) := by
        convert hL R hRL using 1 <;> congr 2 <;> ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by linarith [Nat.cast_nonneg (α := ℝ) R])
  have hshift : (2 : ℝ)^(-((R-1 : ℕ) : ℝ)/32) ≤ 2*(2 : ℝ)^(-(R : ℝ)/32) := by
    calc
      _ ≤ (2 : ℝ)^(1+(-(R : ℝ)/32)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hcast]; linarith)
      _ = _ := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),Real.rpow_one]
  have hperturb' : perturbedProfileCoefficient (R-1)/(criticalCoefficient (R-1) : ℝ) ≤
      (512*Real.pi)*(2 : ℝ)^(-(R : ℝ)/32) := by
    calc
      _ ≤ (256*Real.pi)*(2 : ℝ)^(-((R-1 : ℕ) : ℝ)/32) := hperturb (R-1) hRM
      _ ≤ (256*Real.pi)*(2*(2 : ℝ)^(-(R : ℝ)/32)) :=
        mul_le_mul_of_nonneg_left hshift (by positivity)
      _ = _ := by ring
  calc
    _ ≤ C*((R : ℝ)*(2 : ℝ)^(-(R : ℝ)/2) +
        perturbedProfileCoefficient (R-1)/(criticalCoefficient (R-1) : ℝ)) := h
    _ ≤ C*((2 : ℝ)^(-(R : ℝ)/32) + (512*Real.pi)*(2 : ℝ)^(-(R : ℝ)/32)) :=
      mul_le_mul_of_nonneg_left (add_le_add hlin hperturb') hC.le
    _ = _ := by ring

/-- The complete odd critical family retains both physical marker sectors
and has a uniform exponential relative error. -/
theorem oddCriticalSubgroups_relative_error :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ R : ℕ, N ≤ R →
      |(Nat.card (OddCriticalSubgroups R) : ℝ)/exactBenchmark (2*R+1)-1| ≤
        K*(2 : ℝ)^(-(R : ℝ)/32) := by
  obtain ⟨A,hA,N,hN,heven⟩ := evenCriticalSubgroups_relative_error
  obtain ⟨B,hB,M,hM,hmarked⟩ := markedCriticalSector_relative_error
  refine ⟨max A B,lt_of_lt_of_le hA (le_max_left _ _),max N M,by omega,?_⟩
  intro R hR
  have hRN : N ≤ R := by omega
  have hRM : M ≤ R := by omega
  have hR0 : 0 < R := by omega
  rw [oddCriticalSubgroups_normalized R hR0]
  apply relative_error_weighted_pair
    (mul_pos (by exact_mod_cast binarySubspaceCount_pos R)
      (by exact_mod_cast criticalCoefficient_pos R))
    (mul_pos (by exact_mod_cast binarySubspaceCount_pos R)
      (by exact_mod_cast criticalCoefficient_pos (R-1))) (by norm_num)
  · have h := heven R hRN
    rw [evenCriticalSubgroups_normalized] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left A B) (by positivity))
  · exact (hmarked R hRM).trans
      (mul_le_mul_of_nonneg_right (le_max_right A B) (by positivity))

end SymmetricSubgroupAsymptotics

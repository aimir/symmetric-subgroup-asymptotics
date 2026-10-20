import SymmetricSubgroupAsymptotics.ConjugacyOrbitMinimalNormal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-! A literal three-cycle of the nonidentity elements proves minimal
normality of the same actual subgroup. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

theorem minimalNormal_of_three_cycle {G : Type} [Group G]
    (D : Subgroup G) [D.Normal] (hD : D≠⊥)
    (a : G) (v : Fin 3 → G)
    (hcover : ∀ x∈D, x≠1 → ∃ i, x=v i)
    (hcycle : ∀ i, a*v i*a⁻¹=v (i+1)) : IsMinimalNormalSubgroup D := by
  apply minimalNormal_of_nonidentity_conjugacy_orbit D hD
  intro x hx hxne y hy hyne
  obtain ⟨i,rfl⟩ := hcover x hx hxne
  obtain ⟨j,rfl⟩ := hcover y hy hyne
  have htwo (k : Fin 3) : a^2*v k*(a^2)⁻¹=v (k+2) := by
    calc
      a^2*v k*(a^2)⁻¹=a*(a*v k*a⁻¹)*a⁻¹ := by simp [pow_two,mul_assoc]
      _=v ((k+1)+1) := by rw [hcycle,hcycle]
      _=v (k+2) := by congr 1; exact add_assoc k 1 1
  fin_cases i <;> fin_cases j
  · exact ⟨1,by simp⟩
  · exact ⟨a,hcycle 0⟩
  · exact ⟨a^2,htwo 0⟩
  · exact ⟨a^2,htwo 1⟩
  · exact ⟨1,by simp⟩
  · exact ⟨a,hcycle 1⟩
  · exact ⟨a,hcycle 2⟩
  · exact ⟨a^2,htwo 2⟩
  · exact ⟨1,by simp⟩

end SymmetricSubgroupAsymptotics

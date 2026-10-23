import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementFactor

/-! Uniqueness of the actual short-complement / outer-group factors.
The outer group preserves central degree while the complement strictly
raises it, so their intersection is the identity in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementUnique
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckShortComplement CFSGTrialityGeckShortComplementFactor
open CFSGTrialityFixedWeylWords CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckLatticeDegree CFSGGradedQuadraticUnit CFSGGradedMatrixSubgroups

theorem outer_simple_central_zero (i : Fin 3) :
    (Index (outerNode i) : CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)).val 1 = 0 := by
  change (Pi.single (outerNode i) (1 : ℤ) : Fin 4 → ℤ) 1 = 0
  fin_cases i <;> decide

theorem outerGroup_le_preserving (K : Type) [Field K] :
    outerGroup K ≤ preservingUnits
      (fun j => latticeWeight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base j 1) := by
  change (outerProductHom K).range ≤ _
  rw [outerProductHom, MonoidHom.noncommPiCoprod_range]
  apply iSup_le
  intro i
  rintro x ⟨t, rfl⟩
  exact preserves_of_height_zero
    (latticeWeight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base)
    (Index (outerNode i) : CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)).val
    (show (Fin 4 → ℤ) →ₗ[ℤ] ℤ from LinearMap.proj (1 : Fin 4)).toAddMonoidHom _
    (canonicalRoot_quadraticGrade (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K (outerNode i) t.toAdd)
    (outer_simple_central_zero i)

theorem shortComplement_inf_outer (K : Type) [Field K] :
    shortComplement K ⊓ outerGroup K = ⊥ := by
  apply le_antisymm _ bot_le
  exact (inf_le_inf (shortComplement_le_strict K) (outerGroup_le_preserving K)).trans
    (le_of_eq (strict_inf_preserving
      (fun j => latticeWeight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base j 1)))

theorem short_factor_unique (K : Type) [Field K]
    (c c' o o' : (Matrix GeckIndex GeckIndex K)ˣ)
    (hc : c ∈ shortComplement K) (hc' : c' ∈ shortComplement K)
    (ho : o ∈ outerGroup K) (ho' : o' ∈ outerGroup K)
    (he : c * o = c' * o') : c = c' ∧ o = o' := by
  have hh : c'⁻¹ * c = o' * o⁻¹ := by
    calc
      c'⁻¹ * c = c'⁻¹ * (c * o) * o⁻¹ := by group
      _ = o' * o⁻¹ := by rw [he]; group
  have hx : c'⁻¹ * c ∈ shortComplement K ⊓ outerGroup K := by
    refine ⟨(shortComplement K).mul_mem ((shortComplement K).inv_mem hc') hc, ?_⟩
    rw [hh]
    exact (outerGroup K).mul_mem ho' ((outerGroup K).inv_mem ho)
  rw [shortComplement_inf_outer, Subgroup.mem_bot] at hx
  have hcc : c = c' := (inv_mul_eq_one.mp hx).symm
  refine ⟨hcc, ?_⟩
  rw [hcc] at he
  exact mul_left_cancel he

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementUnique

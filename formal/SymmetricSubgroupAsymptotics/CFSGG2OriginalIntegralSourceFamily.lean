import SymmetricSubgroupAsymptotics.CFSGG2OriginalRationalSourceSpan
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice

/-! The SAME fourteen G2 source words belong to the SAME actual least
DP-stable integral Serre lattice. Rational coefficients occur only through
its genuine integral divided-power operations, before any base change. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGG2OriginalIntegralSourceFamily
open CFSG.Models.Chevalley CFSGSerreDiagram
open CFSGG2OriginalRationalSourceSpan

theorem root_mem (neg : Bool) (i : Fin 2) : rootVector CM neg i ∈ integralLattice CM := by
  cases neg
  · exact generator_mem_integralLattice CM (.E i)
  · exact generator_mem_integralLattice CM (.F i)

theorem v_mem (neg : Bool) (j : Fin 6) : v neg j ∈ integralLattice CM := by
  have ha : a neg ∈ integralLattice CM := root_mem neg 0
  have hb : b neg ∈ integralLattice CM := root_mem neg 1
  have hc : G2PositiveDividedPowerWords.c (a neg) (b neg) ∈ integralLattice CM := by
    have h := dividedPower_mem CM neg 0 1 (b neg) hb
    change (1:ℚ)⁻¹ • ((LieAlgebra.ad ℚ Source (a neg))^1) (b neg) ∈ integralLattice CM at h
    simpa only [inv_one,one_smul,pow_one,LieAlgebra.ad_apply] using h
  have hd : G2PositiveDividedPowerWords.d (a neg) (b neg) ∈ integralLattice CM := by
    have h := dividedPower_mem CM neg 0 2 (b neg) hb
    change (2:ℚ)⁻¹ • ((LieAlgebra.ad ℚ Source (a neg))^2) (b neg) ∈ integralLattice CM at h
    rw [←G2PositiveDividedPowerWords.d_eq_divided_square] at h
    exact h
  have he : G2PositiveDividedPowerWords.e (a neg) (b neg) ∈ integralLattice CM := by
    have h := dividedPower_mem CM neg 0 3 (b neg) hb
    change (6:ℚ)⁻¹ • ((LieAlgebra.ad ℚ Source (a neg))^3) (b neg) ∈ integralLattice CM at h
    rw [←G2PositiveDividedPowerWords.e_eq_divided_cube] at h
    exact h
  have hf : G2PositiveDividedPowerWords.f (a neg) (b neg) ∈ integralLattice CM := by
    have h := dividedPower_mem CM neg 1 1 (G2PositiveDividedPowerWords.e (a neg) (b neg)) he
    change (1:ℚ)⁻¹ • ((LieAlgebra.ad ℚ Source (b neg))^1)
      (G2PositiveDividedPowerWords.e (a neg) (b neg)) ∈ integralLattice CM at h
    simpa only [inv_one,one_smul,pow_one,LieAlgebra.ad_apply] using h
  fin_cases j
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he
  · exact hf

theorem family_mem (j : Fin 2 ⊕ (Bool × Fin 6)) : family j ∈ integralLattice CM := by
  cases j with
  | inl i => exact generator_mem_integralLattice CM (.H i)
  | inr w => exact v_mem w.1 w.2

def vector (j : Fin 2 ⊕ (Bool × Fin 6)) : integralLattice CM :=
  ⟨family j,family_mem j⟩

@[simp] theorem vector_val (j : Fin 2 ⊕ (Bool × Fin 6)) : (vector j).val = family j := rfl

/-- Rational spanning concerns exactly the values of these actual
integral source words, not a substituted native image family. -/
theorem vector_span_eq_top :
    Submodule.span ℚ (Set.range (fun j => (vector j).val)) = ⊤ :=
  CFSGG2OriginalRationalSourceSpan.span_eq_top

end SymmetricSubgroupAsymptotics.CFSGG2OriginalIntegralSourceFamily

import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A primitive rational coordinate system detects the integral part of
its finite rational span. No global spanning or injectivity is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.PrimitiveIntegralFamilyRationalSpan
variable {J L : Type*} [Fintype J] [DecidableEq J]
  [AddCommGroup L] [Module ℚ L] (S : Submodule ℤ L) (v : J→S)
  (c : L→ₗ[ℚ](J→ℚ)) (hcoord : ∀ j,c (v j).val=Pi.single j 1)

include hcoord

theorem integral_mem_of_rational_mem (x : S) (a : J→ℤ)
    (hcx : c x.val=fun j=>(a j:ℚ))
    (hx : x.val∈Submodule.span ℚ (Set.range (fun j=>(v j).val))) :
    x∈Submodule.span ℤ (Set.range v) := by
  obtain ⟨b,hb⟩:= (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  have hc : c (Fintype.linearCombination ℚ (fun j=>(v j).val) b)=b := by
    rw [Fintype.linearCombination_apply]
    simp only [map_sum,map_smul,hcoord]
    funext j
    simp [Finset.sum_apply,Pi.single_apply]
  have hba : b=fun j=>(a j:ℚ) := by
    rw [Fintype.linearCombination_apply,hb] at hc
    exact hc.symm.trans hcx
  have he : Fintype.linearCombination ℤ v a=x := by
    apply Subtype.ext
    rw [←hb,hba]
    simp only [Fintype.linearCombination_apply,Submodule.coe_sum,Submodule.coe_smul]
    apply Finset.sum_congr rfl
    intro j hj
    exact (Int.cast_smul_eq_zsmul ℚ (a j) (v j).val).symm
  rw [←he,Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)

end SymmetricSubgroupAsymptotics.PrimitiveIntegralFamilyRationalSpan

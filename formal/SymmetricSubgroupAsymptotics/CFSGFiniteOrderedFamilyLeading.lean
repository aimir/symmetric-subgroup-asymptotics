import SymmetricSubgroupAsymptotics.CFSGFiniteQuotientFamilyProduct
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixHighLayerProducts

/-! The leading coefficient of a fixed ordered finite family. No
commutativity of its matrix factors is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteOrderedFamilyLeading
open CFSGFiniteQuotientFamilyProduct CFSGGradedMatrixHighLayerProducts
open CFSGGradedMatrixSingleDegreeSpan

theorem map_orderedFamilyProduct {J G Q : Type*} [Fintype J] [Group G] [Group Q]
    (q : G→*Q) (f : J→G) :
    q (orderedFamilyProduct f)=orderedFamilyProduct (fun j=>q (f j)) := by
  classical
  simp only [orderedFamilyProduct,map_list_prod,List.map_map,Function.comp_def]

theorem finite_ordered_leading {I J K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [Field K] (weight : I→ℤ) (h : ℤ) (hh : 0<h)
    (f : J→(Matrix I I K)ˣ)
    (hf : ∀j,BelowCut weight h ((f j : Matrix I I K)-1)) :
    BelowCut weight h (((orderedFamilyProduct f : (Matrix I I K)ˣ) : Matrix I I K)-1) ∧
      degreePart weight h (((orderedFamilyProduct f : (Matrix I I K)ˣ) : Matrix I I K)-1)=
        ∑j,degreePart weight h ((f j : Matrix I I K)-1) := by
  classical
  have hl := ordered_leading_layer weight h hh (Finset.univ.toList.map f) (by
    intro u hu
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hu
    exact hf j)
  simpa only [orderedFamilyProduct,List.map_map,Function.comp_apply,Finset.sum_map_toList] using hl

end SymmetricSubgroupAsymptotics.CFSGFiniteOrderedFamilyLeading

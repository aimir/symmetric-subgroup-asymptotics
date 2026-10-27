import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveWeightIdentification

/-! On the finite span of the ACTUAL positive source family, natural
primitive coordinates recover every source coefficient. This is only a
restricted-span identity, not source realization injectivity. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveSpanCoefficients
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformPositiveProfile CFSGOrthogonalDUniformPositiveTables
open CFSGOrthogonalDOriginalPositiveSourceWeights
open CFSGOrthogonalDOriginalPositiveWeightIdentification
variable (r : ℕ) (hr : 4 ≤ r)
local instance : DecidableEq (PositiveIndex r) := Classical.decEq _

def span : Submodule ℚ (RationalLie (CartanMatrix.D r)) :=
  Submodule.span ℚ (Set.range (source r hr))

theorem coefficients_combination (a : PositiveIndex r → ℚ) :
    positiveCoordinates r hr (rationalOrthogonalRepresentation r hr
      (Fintype.linearCombination ℚ (source r hr) a))=a := by
  rw [Fintype.linearCombination_apply]
  simp only [map_sum,map_smul,source_image,positive_coordinates_matrix]
  funext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem source_eq_combination_of_mem
    (x : RationalLie (CartanMatrix.D r)) (hx : x∈span r hr) :
    x=Fintype.linearCombination ℚ (source r hr)
      (positiveCoordinates r hr (rationalOrthogonalRepresentation r hr x)) := by
  obtain ⟨a,ha⟩:= (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  have ha' : Fintype.linearCombination ℚ (source r hr) a=x := by
    simpa only [Fintype.linearCombination_apply] using ha
  rw [←ha',coefficients_combination]

private theorem rational_root_image (neg : Bool) (i : Fin r) :
    rationalOrthogonalRepresentation r hr (rootVector (CartanMatrix.D r) neg i)=
      rootMatrix ℚ r neg i := by
  cases neg <;> simp only [rootVector,rootMatrix,Bool.false_eq_true,if_false,if_true,
    rationalOrthogonalRepresentation_E,rationalOrthogonalRepresentation_F]

theorem raising_of_mem (i : Fin r) (j : PositiveIndex r)
    (hmem : ⁅rootVector (CartanMatrix.D r) false i,source r hr j⁆∈span r hr) :
    ⁅rootVector (CartanMatrix.D r) false i,source r hr j⁆=
      Fintype.linearCombination ℚ (source r hr) (raising r hr i j) := by
  have h:=source_eq_combination_of_mem r hr _ hmem
  simpa only [LieHom.map_lie,rational_root_image,
    source_image,rootMatrix,Bool.false_eq_true,if_false,raising] using h

theorem lowering_of_mem (i : Fin r) (j : PositiveIndex r)
    (hmem : ⁅oppositeVector (CartanMatrix.D r) false i,source r hr j⁆∈span r hr) :
    ⁅oppositeVector (CartanMatrix.D r) false i,source r hr j⁆=
      Fintype.linearCombination ℚ (source r hr) (lowering r hr i j) := by
  have h:=source_eq_combination_of_mem r hr _ hmem
  simpa only [oppositeVector,LieHom.map_lie,
    rational_root_image,
    source_image,rootMatrix,Bool.false_eq_true,if_true,lowering] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveSpanCoefficients

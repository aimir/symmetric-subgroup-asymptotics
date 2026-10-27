import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveWeightIdentification

/-! On the finite span of the ACTUAL positive source family, natural
primitive coordinates recover every source coefficient. This is only a
restricted-span identity, not source realization injectivity. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveSpanCoefficients
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGSymplecticSerreMatrices CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticUniformPositiveProfile CFSGSymplecticUniformPositiveTables
open CFSGSymplecticOriginalPositiveSourceWeights
open CFSGSymplecticOriginalPositiveWeightIdentification
variable (r : ℕ)
local instance : DecidableEq (PositiveIndex r) := Classical.decEq _

def span : Submodule ℚ (RationalLie (CartanMatrix.C r).transpose) :=
  Submodule.span ℚ (Set.range (source r))

theorem coefficients_combination (a : PositiveIndex r → ℚ) :
    positiveCoordinates r (rationalSymplecticRepresentation r
      (Fintype.linearCombination ℚ (source r) a))=a := by
  rw [Fintype.linearCombination_apply]
  simp only [map_sum,map_smul,source_image,positive_coordinates_matrix]
  funext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem source_eq_combination_of_mem
    (x : RationalLie (CartanMatrix.C r).transpose) (hx : x∈span r) :
    x=Fintype.linearCombination ℚ (source r)
      (positiveCoordinates r (rationalSymplecticRepresentation r x)) := by
  obtain ⟨a,ha⟩:= (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  have ha' : Fintype.linearCombination ℚ (source r) a=x := by
    simpa only [Fintype.linearCombination_apply] using ha
  rw [←ha',coefficients_combination]

theorem raising_of_mem (i : Fin r) (j : PositiveIndex r)
    (hmem : ⁅rootVector (CartanMatrix.C r).transpose false i,source r j⁆∈span r) :
    ⁅rootVector (CartanMatrix.C r).transpose false i,source r j⁆=
      Fintype.linearCombination ℚ (source r) (raising r i j) := by
  have h:=source_eq_combination_of_mem r _ hmem
  simpa only [LieHom.map_lie,rationalRepresentation_rootVector,
    source_image,rootMatrix,Bool.false_eq_true,if_false,raising] using h

theorem lowering_of_mem (i : Fin r) (j : PositiveIndex r)
    (hmem : ⁅oppositeVector (CartanMatrix.C r).transpose false i,source r j⁆∈span r) :
    ⁅oppositeVector (CartanMatrix.C r).transpose false i,source r j⁆=
      Fintype.linearCombination ℚ (source r) (lowering r i j) := by
  have h:=source_eq_combination_of_mem r _ hmem
  simpa only [oppositeVector,LieHom.map_lie,
    rationalRepresentation_rootVector,
    source_image,rootMatrix,Bool.false_eq_true,if_true,lowering] using h

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveSpanCoefficients

import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveActionTables
import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalIntegralSpanDetection
import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalChevalleyPaths
import SymmetricSubgroupAsymptotics.CFSGSerreSaturatedFirstActionSpan

/-! Actual all-rank original-C integral source spanning. Positive source
induction, primitive integral detection and the genuine Chevalley
involution prove first-action stability; saturation supplies all divided
powers. There is no source-table or faithfulness premise. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalFirstActionSpan
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGSerreLocalNilpotence CFSGSymplecticSerreMatrices
open CFSGSymplecticOriginalRootCandidates CFSGSymplecticOriginalCartanTail
open CFSGSymplecticOriginalPrimitiveFamily CFSGSymplecticUniformPositiveProfile
open CFSGSymplecticOriginalPositiveSourceWeights CFSGSymplecticOriginalChevalleyPaths
open CFSGSerreChevalleyInvolution
variable (r : ℕ)
local instance : DecidableEq (BasisIndex r) := Classical.decEq _

private theorem positive_combination_mem (a : PositiveIndex r→ℚ) :
    Fintype.linearCombination ℚ (source r) a∈
      Submodule.span ℚ (Set.range (fun j=>(primitiveVector r j).val)) := by
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨CFSGSymplecticUniformPositiveProfile.fullIndex r j,by cases j <;> rfl⟩

private theorem positive_root_first (neg : Bool) (i : Fin r) (j : RootIndex r) :
    integralOperator (CartanMatrix.C r).transpose neg i 1 (root r false j)∈
      Submodule.span ℤ (Set.range (primitiveVector r)) := by
  apply CFSGSymplecticOriginalIntegralSpanDetection.integral_mem_of_rational_mem
  rw [integralOperator_one_coe_apply]
  change ⁅rootVector (CartanMatrix.C r).transpose neg i,(root r false j).val⁆∈_
  have ht:=CFSGSymplecticOriginalPositiveActionTables.source_tables r
  cases neg
  · rw [show (root r false j).val=source r (.inr j) from rfl,ht.1]
    exact positive_combination_mem r _
  · have h:=ht.2 i (.inr j) (rootHeight_pos r j)
    change ⁅rootVector (CartanMatrix.C r).transpose true i,(root r false j).val⁆=_ at h
    rw [h]
    exact positive_combination_mem r _

private theorem positive_cartan_first (i b : Fin r) :
    integralOperator (CartanMatrix.C r).transpose false i 1 (tail r b.val)∈
      Submodule.span ℤ (Set.range (primitiveVector r)) := by
  apply CFSGSymplecticOriginalIntegralSpanDetection.integral_mem_of_rational_mem
  rw [integralOperator_one_coe_apply]
  change ⁅rootVector (CartanMatrix.C r).transpose false i,source r (.inl b)⁆∈_
  rw [(CFSGSymplecticOriginalPositiveActionTables.source_tables r).1]
  exact positive_combination_mem r _

private theorem negative_Hnat_first (i : Fin r) (b : ℕ) :
    integralOperator (CartanMatrix.C r).transpose true i 1 (Hnat r b)∈
      Submodule.span ℤ (Set.range (primitiveVector r)) := by
  unfold Hnat
  split_ifs with h
  · have he : integralOperator (CartanMatrix.C r).transpose true i 1
        (latticeGenerator (CartanMatrix.C r).transpose (.H ⟨b,h⟩))=
        (CartanMatrix.C r).transpose ⟨b,h⟩ i •
          latticeGenerator (CartanMatrix.C r).transpose (.F i) := by
      apply Subtype.ext
      rw [integralOperator_one_coe_apply]
      change ⁅generator (CartanMatrix.C r).transpose (.F i),
        generator (CartanMatrix.C r).transpose (.H ⟨b,h⟩)⁆=_
      rw [←lie_skew (generator (CartanMatrix.C r).transpose (.F i))
        (generator (CartanMatrix.C r).transpose (.H ⟨b,h⟩)),
        CFSGSerreLocalNilpotence.generator_HF]
      change - -((CartanMatrix.C r).transpose ⟨b,h⟩ i •
        generator (CartanMatrix.C r).transpose (.F i))=
          (CartanMatrix.C r).transpose ⟨b,h⟩ i •
            generator (CartanMatrix.C r).transpose (.F i)
      exact neg_neg _
    rw [he]
    exact Submodule.smul_mem _ _ (original_generators_mem r (.F i))
  · rw [map_zero]
    exact Submodule.zero_mem _

private theorem negative_cartan_first (i b : Fin r) :
    integralOperator (CartanMatrix.C r).transpose true i 1 (tail r b.val)∈
      Submodule.span ℤ (Set.range (primitiveVector r)) := by
  unfold tail
  rw [map_sum]
  apply Submodule.sum_mem
  intro a ha
  exact negative_Hnat_first r i (b.val+a)

private theorem negative_root_first (neg : Bool) (i : Fin r) (j : RootIndex r) :
    integralOperator (CartanMatrix.C r).transpose neg i 1 (root r true j)∈
      Submodule.span ℤ (Set.range (primitiveVector r)) := by
  have h:=map_operator r (!neg) i 1
    (integralMap (CartanMatrix.C r).transpose (root r true j))
  rw [Bool.not_not,integralMap_involutive] at h
  rw [←h]
  apply map_mem
  obtain ⟨z,hz⟩:=map_root_swap r true j
  rw [hz,map_smul]
  exact Submodule.smul_mem _ z (positive_root_first r (!neg) i j)

theorem first_action_mem (neg : Bool) (i : Fin r) (j : BasisIndex r) :
    integralOperator (CartanMatrix.C r).transpose neg i 1 (primitiveVector r j)∈
      Submodule.span ℤ (Set.range (primitiveVector r)) := by
  rcases j with b | ⟨sgn,j⟩
  · cases neg
    · exact positive_cartan_first r i b
    · exact negative_cartan_first r i b
  · cases sgn
    · exact positive_root_first r neg i j
    · exact negative_root_first r neg i j

theorem span_eq_top : Submodule.span ℤ (Set.range (primitiveVector r))=⊤ :=
  CFSGSerreSaturatedFirstActionSpan.span_eq_top (CartanMatrix.C r).transpose
    (integralSymplecticRepresentation r) (primitiveVector r) (matrixCoordinates r)
    (primitive_coordinates r) (first_action_mem r) (original_generators_mem r)

theorem realization_injective : Function.Injective (integralSymplecticRepresentation r) :=
  CFSGSerreSaturatedFirstActionSpan.realization_injective (CartanMatrix.C r).transpose
    (integralSymplecticRepresentation r) (primitiveVector r) (matrixCoordinates r)
    (primitive_coordinates r) (first_action_mem r) (original_generators_mem r)

theorem baseChange_injective (K : Type*) [CommRing K] :
    Function.Injective ((integralSymplecticRepresentation r).baseChange K) :=
  CFSGSerreSaturatedFirstActionSpan.baseChange_injective (CartanMatrix.C r).transpose
    (integralSymplecticRepresentation r) (primitiveVector r) (matrixCoordinates r)
    (primitive_coordinates r) (first_action_mem r) (original_generators_mem r) K

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalFirstActionSpan

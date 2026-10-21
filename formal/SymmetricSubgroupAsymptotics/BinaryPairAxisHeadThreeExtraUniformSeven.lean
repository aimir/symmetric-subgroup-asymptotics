import SymmetricSubgroupAsymptotics.BinaryPairHeadThreeLeadingGenerators
import SymmetricSubgroupAsymptotics.BinaryHeadThreeOriginalLeadingShears
import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule

/-! A literal head-three whole pair kernel, together with actual top
translations and the extra shear, generates every original natural
submodule by seven elements. No kernel vector is replaced by a monomial. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryBooleanFourPolynomialCoordinates
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

theorem uniform_generatedBy_seven_of_axis_head_three_extra
    (e : Equiv.Perm (Fin 16))
    (htranslations : ∀ i : Fin 4, ∃ u : U,
      ∀ j, (F.top u)⁻¹ (e.symm j) = e.symm (flipIndex i j))
    (hextra : ∃ u : U, ∀ j, (F.top u)⁻¹ (e.symm j) =
      e.symm (BinaryCommonEightExtraShearLeading.booleanPermutation.symm j))
    (hhead : 3 ≤ Module.finrank (ZMod 2)
      ((F.axisNaturalSubrepresentation F.top.ker).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) F.top.range (ZMod 2)))) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 7 := by
  have ht : ∀ i : Fin 4, ∃ g : F.top.range,
      ∀ j, g⁻¹ • e.symm j = e.symm (flipIndex i j) := by
    intro i
    obtain ⟨u, hu⟩ := htranslations i
    exact ⟨F.top.rangeRestrict u, hu⟩
  have he : ∃ g : F.top.range, ∀ j, g⁻¹ • e.symm j =
      e.symm (BinaryCommonEightExtraShearLeading.booleanPermutation.symm j) := by
    obtain ⟨u, hu⟩ := hextra
    exact ⟨F.top.rangeRestrict u, hu⟩
  obtain ⟨c, hs⟩ := binary_head_three_original_leading_shears
    (F.axisNaturalSubrepresentation F.top.ker) e ht he hhead
  intro W
  apply F.naturalSubrepresentation_generatedBy_seven_of_head_three_leading_shears
    c e htranslations hextra _ W
  intro k
  obtain ⟨a, ha, hm⟩ := hs k
  refine ⟨a, ha, ?_⟩
  change (fun x => evaluate a (e x)) ∈ F.ambientAxis F.top.ker at hm
  exact F.ambientAxis_le_kernelSpace F.top.ker hm

end SymmetricSubgroupAsymptotics.BinaryPairFrame

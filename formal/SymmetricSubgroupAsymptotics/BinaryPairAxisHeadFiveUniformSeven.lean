import SymmetricSubgroupAsymptotics.BinaryPairFiveQuadraticLeadingGenerators
import SymmetricSubgroupAsymptotics.BinaryBooleanFourActualLeadingShears
import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule

/-! The head of the literal whole pair kernel supplies the actual
leading shears used to generate every original natural submodule. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open BinaryBooleanFourPolynomialCoordinates
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

theorem uniform_generatedBy_seven_of_axis_head_five
    (e : Equiv.Perm (Fin 16))
    (htranslations : ∀ i : Fin 4, ∃ u : U,
      ∀ j, (F.top u)⁻¹ (e.symm j) = e.symm (flipIndex i j))
    (hhead : 5 ≤ Module.finrank (ZMod 2)
      ((F.axisNaturalSubrepresentation F.top.ker).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) F.top.range (ZMod 2)))) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 7 := by
  have htopTranslations : ∀ i : Fin 4, ∃ g : F.top.range,
      ∀ j, g⁻¹ • e.symm j = e.symm (flipIndex i j) := by
    intro i
    obtain ⟨u, hu⟩ := htranslations i
    exact ⟨F.top.rangeRestrict u, hu⟩
  obtain ⟨j, hshears⟩ := boolean_four_actual_translation_submodule_leading_shears
    (F.axisNaturalSubrepresentation F.top.ker) e htopTranslations hhead
  intro W
  apply F.naturalSubrepresentation_generatedBy_seven_of_five_quadratic_leading_shears
    j e htranslations _ W
  intro b hb
  obtain ⟨a, ha, hmem⟩ := hshears b hb
  refine ⟨a, ha, ?_⟩
  change (fun x => evaluate a (e x)) ∈ F.ambientAxis F.top.ker at hmem
  exact F.ambientAxis_le_kernelSpace F.top.ker hmem

end SymmetricSubgroupAsymptotics.BinaryPairFrame

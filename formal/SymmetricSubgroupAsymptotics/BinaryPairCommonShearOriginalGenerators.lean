import SymmetricSubgroupAsymptotics.BinaryPairCommonShearGenerators
import SymmetricSubgroupAsymptotics.BinaryCommonEightOriginalTranslations

/-! The common-shear generator bound on the original outer group.
Inner zero-model translations are lifted through the actual outer top
map. Their outer offsets are unrestricted and remain in the proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem uniform_generatedBy_six_of_original_common_shears
    (hzero : F.top.range = E.splitAffineAction)
    (hreg : ∀ j : Fin 3, BinaryMenuCayley8T3.generators j ∈ E.top.range)
    (hconst : (fun _ : Fin 8 => (1 : ZMod 2)) ∈ E.kernelSpace)
    (hmono : ∀ b : Fin 16, BinaryThreeVariablePairMonomialWidth.Allowed (support b) →
      E.originalPointMonomial b ∈ F.kernelSpace) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 6 := by
  let e := E.commonBooleanPointLabels
  have ht : ∀ i : Fin 4, ∃ u : U,
      ∀ j, (F.top u)⁻¹ (e.symm j) = e.symm (flipIndex i j) := by
    intro i
    let t := E.commonTranslationRow hzero hreg hconst i
    obtain ⟨u, hu⟩ := F.top.rangeRestrict_surjective t
    have heq : F.top u = t.val := congrArg Subtype.val hu
    have hf (x : Fin 16) : e (F.top u x) = flipIndex i (e x) := by
      rw [heq]
      exact E.commonTranslationRow_pointLabels hzero hreg hconst i x
    refine ⟨u, ?_⟩
    intro j
    apply (F.top u).injective
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    apply e.injective
    rw [hf, Equiv.apply_symm_apply, Equiv.apply_symm_apply, flipIndex_involutive]
  intro W
  apply F.naturalSubrepresentation_generatedBy_six_of_common_shears e ht _ W
  intro b hb
  have hm := hmono b hb
  change (fun x => monomial (support b) (e x)) ∈ F.kernelSpace at hm
  exact hm

end SymmetricSubgroupAsymptotics.BinaryPairFrame

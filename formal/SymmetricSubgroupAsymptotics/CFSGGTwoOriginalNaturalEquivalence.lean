import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFieldBasis
import SymmetricSubgroupAsymptotics.CFSGSerreFaithfulImageRepresentation
import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalImageFaithful

/-! The literal original G2 Model is the actual native folded root group,
without an ordinary-G2 simplicity assumption. Both faithful actions are
on the SAME original tensor image, and the checked generator identities
identify their action ranges and their signed root parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalNaturalEquivalence
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices CFSGSerreModelRootGeneration
open CFSGGTwoOriginalFieldBasis CFSGGTwoNaturalImageFaithful
variable (K : Type) [Field K]

theorem foldedImageRepresentation_injective : Function.Injective (foldedImageRepresentation K) :=
  CFSGSerreFaithfulImageRepresentation.imageRepresentation_injective realizationData K
    (foldedBaseChange_injective K)

def modelEquivNatural : Model CartanMatrix.G₂ K ≃* naturalGroup K :=
  (MonoidHom.ofInjective (foldedImageRepresentation_injective K)).trans
    ((MulEquiv.subgroupCongr (action_ranges_eq K)).trans
      (MonoidHom.ofInjective (naturalImageAction_injective K)).symm)

theorem modelEquivNatural_intertwines (g : Model CartanMatrix.G₂ K) :
    naturalImageAction K (modelEquivNatural K g)=foldedImageRepresentation K g := by
  change naturalImageAction K
    ((MonoidHom.ofInjective (naturalImageAction_injective K)).symm
      (MulEquiv.subgroupCongr (action_ranges_eq K)
        ((MonoidHom.ofInjective (foldedImageRepresentation_injective K)) g)))=_
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem modelEquivNatural_root (neg : Bool) (i : Fin 2) (t : K) :
    modelEquivNatural K (modelRoot CartanMatrix.G₂ K neg i t)=naturalRoot K neg i t := by
  apply naturalImageAction_injective K
  rw [modelEquivNatural_intertwines]
  exact CFSGSerreQuadraticMatrix.source_root_action_eq_elementary realizationData K
    (rootTransvection K) (rootTransvection_val_data K) (rootTransvection_inv_val_data K)
    (image_fourth_zero K) neg i t

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalNaturalEquivalence

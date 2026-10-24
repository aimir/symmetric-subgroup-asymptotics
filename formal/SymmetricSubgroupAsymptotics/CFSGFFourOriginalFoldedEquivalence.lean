import SymmetricSubgroupAsymptotics.CFSGFFourOriginalBaseChangeFaithful
import SymmetricSubgroupAsymptotics.CFSGFFourE6FoldedCenterTrivial

/-! A root-parameter-preserving correspondence between the literal
original F4 Model and the literal folded E6 matrix group in characteristic
two. Both sides act faithfully on the SAME original tensor image. No
ordinary F4 simplicity assumption is used, so this correspondence is
available for the ReeF4 and Tits ambient constructions.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalFoldedEquivalence
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreQuadraticMatrix
open CFSGFFourSerreMatrices CFSGFFourOriginalBaseChangeFaithful
open CFSGFFourE6FoldedCenterTrivial
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆):=Classical.decEq _
variable (K:Type) [Field K] [Finite K] [CharP K 2]

def modelEquivFolded : Model CartanMatrix.F₄ K≃*canonicalElementaryGroup realizationData K :=
  (MonoidHom.ofInjective (imageRepresentation_injective K)).trans
    ((MulEquiv.subgroupCongr (full_action_ranges_eq K)).trans
      (MonoidHom.ofInjective (fullNaturalImageAction_injective K)).symm)

theorem modelEquivFolded_intertwines (g:Model CartanMatrix.F₄ K) :
    fullNaturalImageAction K (modelEquivFolded K g)=imageRepresentation realizationData K g := by
  change fullNaturalImageAction K
    ((MonoidHom.ofInjective (fullNaturalImageAction_injective K)).symm
      (MulEquiv.subgroupCongr (full_action_ranges_eq K)
        ((MonoidHom.ofInjective (imageRepresentation_injective K)) g)))=_
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem modelEquivFolded_root (neg:Bool) (i:Fin 4) (t:K) :
    modelEquivFolded K (modelRoot CartanMatrix.F₄ K neg i t)=
      canonicalElementaryRoot realizationData K neg i t := by
  apply fullNaturalImageAction_injective K
  rw [modelEquivFolded_intertwines]
  exact source_root_action_eq_elementary realizationData K (canonicalRoot realizationData K)
    (canonicalRoot_val realizationData K) (canonicalRoot_inv_val realizationData K)
    (baseChange_all_fourth K) neg i t

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalFoldedEquivalence

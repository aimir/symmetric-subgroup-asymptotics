import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoImageKernel
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationImageNoncentral
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryProjectiveCenter

/-! The original simple characteristic-two B projective Serre model is
the actual projective C elementary group. The image kernel is proved
faithful first; no independent C simplicity theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSG.Models.Chevalley CFSGOrthogonalBGenerationImageNoncentral
variable (K : Type) [Field K] [Finite K] [CharP K 2]

def serreProjectiveEquivSymplecticProjective_charTwo (r : ℕ) (hr : 0 < r)
    [IsSimpleGroup (Projective (CartanMatrix.B (r + 1)).transpose K)] :
    Projective (CartanMatrix.B (r + 1)).transpose K ≃*
      CFSGSymplecticSerreMatrices.elementaryProjective K (r + 1) := by
  letI charTwoB_imageProjectiveNontrivial :
      Nontrivial (ActionImage K (r + 1) ⧸ Subgroup.center (ActionImage K (r + 1))) :=
    imageProjective_nontrivial K (r + 1) (by omega)
  let e₀ := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (sourceActionIntoElementaryRange K (r + 1))
    (sourceActionIntoElementaryRange_surjective K (r + 1))
  let e₁ := (elementaryImageActionEquiv_charTwo K r hr).symm.trans
    (CFSGOrthogonalBGenerationCharTwoEquivalence.elementaryEquiv K (r + 1))
  exact e₀.trans (CFSGCenterQuotientEquiv.equiv e₁)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices

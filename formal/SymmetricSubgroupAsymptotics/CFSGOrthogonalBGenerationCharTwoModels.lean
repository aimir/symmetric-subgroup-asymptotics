import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwo
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationImageNoncentral
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleGenerationReduction

/-! Characteristic-two original type-B generation. Descent is through
the ACTUAL original-image action range and that range's centre. No
scalar-centralizer or faithful odd-dimensional natural action is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoModels
open CFSGGeneration CFSGOrthogonalBSerreMatrices
open CFSGOrthogonalBGenerationImageNoncentral
open CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem serre_twoGenerated (r : ℕ) (hr : 3 ≤ r)
    [IsSimpleGroup (Projective (CartanMatrix.B r).transpose K)] :
    TwoGenerated (Projective (CartanMatrix.B r).transpose K) := by
  letI orthogonalBGenerationImageQuotientNontrivial :
      Nontrivial (ActionImage K r ⧸ Subgroup.center (ActionImage K r)) :=
    imageProjective_nontrivial K r (by omega)
  have hnat := CFSGOrthogonalBGenerationCharTwo.elementary_twoGenerated K r hr
  have himage : TwoGenerated (ActionImage K r) :=
    of_surjective (elementaryImageAction K r).rangeRestrict
      (elementaryImageAction K r).rangeRestrict_surjective hnat
  have hquot : TwoGenerated (ActionImage K r ⧸ Subgroup.center (ActionImage K r)) :=
    of_surjective (QuotientGroup.mk' (Subgroup.center (ActionImage K r)))
      (QuotientGroup.mk'_surjective _) himage
  let e := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (sourceActionIntoElementaryRange K r) (sourceActionIntoElementaryRange_surjective K r)
  exact of_mulEquiv e.symm hquot

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoModels

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

theorem typeB_charTwo_twoGenerated (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hq : q.prime = 2) [IsSimpleGroup (CFSG.Models.B r q)] :
    TwoGenerated (CFSG.Models.B r q) := by
  letI orthogonalBGenerationFieldCharTwo : CharP q.Field 2 := by
    rw [← hq]
    infer_instance
  exact CFSGOrthogonalBGenerationCharTwoModels.serre_twoGenerated q.Field r hr

end SymmetricSubgroupAsymptotics.CFSGReduction

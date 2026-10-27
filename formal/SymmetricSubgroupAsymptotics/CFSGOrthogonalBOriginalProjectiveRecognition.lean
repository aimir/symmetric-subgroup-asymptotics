import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalScaledRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSerreFaithfulImageRepresentation

/-! Unconditional odd-field projective recognition of the SAME original
B-transpose Serre model. The source tensor realization is proved faithful;
source simplicity and order/name recognition play no role. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalProjectiveRecognition
open CFSG.Models.Chevalley CFSGOrthogonalBSerreMatrices
variable (K : Type) [Field K] (r : ℕ) (h2 : (2 : K) ≠ 0)

include h2 in
theorem imageRepresentation_injective :
    Function.Injective (orthogonalImageRepresentation K r) :=
  CFSGSerreFaithfulImageRepresentation.imageRepresentation_injective
    (realizationData r) K
    (CFSGOrthogonalBOriginalScaledRealization.baseChange_injective r K h2)

theorem sourceToElementaryProjective_injective :
    Function.Injective (sourceToElementaryProjective K r h2) := by
  intro g h he
  apply imageRepresentation_injective K (r + 1) h2
  have hh := congrArg
    (fun z : elementaryProjective K (r + 1) =>
      ((elementaryProjectiveActionEquiv K r h2) z).val) he
  simpa only [sourceToElementaryProjective, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    sourceActionIntoElementaryRange] using hh

theorem serreToElementaryProjective_injective :
    Function.Injective (serreToElementaryProjective K r h2) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro g h he
  change sourceToElementaryProjective K r h2 g =
    sourceToElementaryProjective K r h2 h at he
  have hh := sourceToElementaryProjective_injective K r h2 he
  exact congrArg (QuotientGroup.mk'
    (Subgroup.center (Model (CartanMatrix.B (r + 1)).transpose K))) hh

def serreProjectiveEquivElementaryProjective :
    Projective (CartanMatrix.B (r + 1)).transpose K ≃*
      elementaryProjective K (r + 1) :=
  MulEquiv.ofBijective (serreToElementaryProjective K r h2)
    ⟨serreToElementaryProjective_injective K r h2,
      serreToElementaryProjective_surjective K r h2⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalProjectiveRecognition

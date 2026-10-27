import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalScaledRealization
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixTensorEquiv
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv

/-! Odd-characteristic identification of the ORIGINAL D Serre projective
model with the independent natural elementary central quotient. Genuine
rational source spanning and integer doubled coordinates supply source
faithfulness. Original root range equality supplies surjectivity. No old
simplicity, classification, model-ID, or faithfulness premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalProjectiveEquivalence
open CFSG.Models.Chevalley CFSGOrthogonalDSerreMatrices

theorem orthogonalBaseChange_injective (K : Type) [Field K] (h2 : (2:K)≠0)
    (r : ℕ) (hr : 4 ≤ r) : Function.Injective (orthogonalBaseChange K r hr) := by
  intro x y he
  apply CFSGOrthogonalDOriginalScaledRealization.baseChange_injective r hr K h2
  apply CFSGIntegerMatrixTensorEquiv.tensorMap_injective K (Index r)
  exact he

theorem imageRepresentation_injective (K : Type) [Field K] (h2 : (2:K)≠0)
    (r : ℕ) (hr : 4 ≤ r) : Function.Injective (orthogonalImageRepresentation K r hr) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply orthogonalBaseChange_injective K h2 r hr
  have hh:=congrArg (fun f : (orthogonalBaseChange K r hr).range≃ₗ[K]
      (orthogonalBaseChange K r hr).range=>
        (f ((orthogonalBaseChange K r hr).rangeRestrict x)).val) he
  simpa only [CFSGSerreSquareZeroMatrix.imageRepresentation_intertwines] using hh

theorem sourceActionIntoElementaryRange_injective (K : Type) [Field K]
    (h2 : (2:K)≠0) (r : ℕ) (hr : 4 ≤ r) :
    Function.Injective (sourceActionIntoElementaryRange K r hr) := by
  intro g h he
  exact imageRepresentation_injective K h2 r hr (congrArg Subtype.val he)

theorem sourceToElementaryProjective_injective (K : Type) [Field K]
    (h2 : (2:K)≠0) (r : ℕ) : Function.Injective (sourceToElementaryProjective K r) := by
  intro g h he
  apply sourceActionIntoElementaryRange_injective K h2 (r+4) (by omega)
  exact (elementaryProjectiveActionEquiv K r).symm.injective he

def sourceEquivElementaryProjective (K : Type) [Field K] (h2 : (2:K)≠0) (r : ℕ) :
    Model (CartanMatrix.D (r+4)) K≃*elementaryProjective K (r+4) :=
  MulEquiv.ofBijective (sourceToElementaryProjective K r)
    ⟨sourceToElementaryProjective_injective K h2 r,
      sourceToElementaryProjective_surjective K r⟩

/-- The literal original projective D carrier, without an old-simple instance. -/
def projectiveEquivElementaryProjective (K : Type) [Field K] (h2 : (2:K)≠0) (r : ℕ) :
    Projective (CartanMatrix.D (r+4)) K≃*elementaryProjective K (r+4) :=
  (CFSGCenterQuotientEquiv.equiv (sourceEquivElementaryProjective K h2 r)).trans
    ((QuotientGroup.quotientMulEquivOfEq (elementaryProjective_center_eq_bot K r)).trans
      QuotientGroup.quotientBot)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalProjectiveEquivalence

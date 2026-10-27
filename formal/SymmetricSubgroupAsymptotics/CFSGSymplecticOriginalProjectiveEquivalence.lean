import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalFirstActionSpan
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixTensorEquiv
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv

/-! The original type-C Serre projective group is the independent natural
elementary symplectic projective group. The actual original source spanning
theorem supplies faithfulness; the existing original-root range theorem
supplies surjectivity. No source simplicity, desired injectivity, field
order, classification, or model-recognition hypothesis is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalProjectiveEquivalence
open CFSG.Models.Chevalley CFSGSymplecticSerreMatrices

theorem symplecticBaseChange_injective (K : Type) [CommRing K] (r : ℕ) :
    Function.Injective (symplecticBaseChange K r) := by
  intro x y he
  apply CFSGSymplecticOriginalFirstActionSpan.baseChange_injective r K
  apply CFSGIntegerMatrixTensorEquiv.tensorMap_injective K (Index r)
  exact he

theorem imageRepresentation_injective (K : Type) [Field K] (r : ℕ) :
    Function.Injective (symplecticImageRepresentation K r) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply symplecticBaseChange_injective K r
  have hh := congrArg (fun f : (symplecticBaseChange K r).range ≃ₗ[K]
      (symplecticBaseChange K r).range =>
        (f ((symplecticBaseChange K r).rangeRestrict x)).val) he
  simpa only [symplecticImageRepresentation_intertwines] using hh

theorem sourceActionIntoElementaryRange_injective (K : Type) [Field K] (r : ℕ) :
    Function.Injective (sourceActionIntoElementaryRange K r) := by
  intro g h he
  exact imageRepresentation_injective K r (congrArg Subtype.val he)

theorem sourceToElementaryProjective_injective (K : Type) [Field K] (r : ℕ) :
    Function.Injective (sourceToElementaryProjective K r) := by
  intro g h he
  apply sourceActionIntoElementaryRange_injective K (r + 1)
  exact (elementaryProjectiveActionEquiv K r).symm.injective he

def sourceEquivElementaryProjective (K : Type) [Field K] (r : ℕ) :
    Model (CartanMatrix.C (r + 1)).transpose K ≃* elementaryProjective K (r + 1) :=
  MulEquiv.ofBijective (sourceToElementaryProjective K r)
    ⟨sourceToElementaryProjective_injective K r,
      sourceToElementaryProjective_surjective K r⟩

/-- This is the literal old `CFSG.Models.C (r+1) q` carrier when K=q.Field. -/
def projectiveEquivElementaryProjective (K : Type) [Field K] (r : ℕ) :
    Projective (CartanMatrix.C (r + 1)).transpose K ≃*
      elementaryProjective K (r + 1) :=
  (CFSGCenterQuotientEquiv.equiv (sourceEquivElementaryProjective K r)).trans
    ((QuotientGroup.quotientMulEquivOfEq (elementaryProjective_center_eq_bot K r)).trans
      QuotientGroup.quotientBot)

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalProjectiveEquivalence

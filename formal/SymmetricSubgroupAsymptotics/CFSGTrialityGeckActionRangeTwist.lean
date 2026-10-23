import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceActionCovariance
import SymmetricSubgroupAsymptotics.CFSGGeneratedActionRange

/-! A genuine twist automorphism of the common actual action range, and
the original fixed-subgroup action into its fixed elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckActionRangeTwist
open CFSGTrialityGeckSourceActionCovariance CFSGTrialityGeckMatrixActionCovariance
open CFSGTrialityGeckImageSemilinearTwist CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckOriginalFixedSections
open CFSGTrialityGeckDiagramCovariance CFSGSerreQuadraticMatrix CFSGSerreModelRootGeneration
open CFSG.Models.Chevalley CFSGSerreFixedRootElements CFSGSerreOrdinaryTwists
open CFSGTrialityTripleFixedRoots

abbrev ActionRange (K : Type) [Field K] := (matrixAction K).range

theorem actionRange_twist_map (K : Type) [Field K] (σ : K ≃+* K) :
    (ActionRange K).map (imageAmbientTwist K σ).toMonoidHom = ActionRange K := by
  apply le_antisymm
  · rintro y ⟨z,⟨g,rfl⟩,rfl⟩
    exact ⟨matrixGroupTwist K σ g,(matrix_action_covariance K σ g).symm⟩
  · rintro y ⟨g,rfl⟩
    refine ⟨matrixAction K ((matrixGroupTwist K σ).symm g),
      ⟨(matrixGroupTwist K σ).symm g,rfl⟩,?_⟩
    change imageAmbientTwist K σ (matrixAction K ((matrixGroupTwist K σ).symm g)) = matrixAction K g
    rw [matrix_action_covariance,MulEquiv.apply_symm_apply]

def actionRangeTwist (K : Type) [Field K] (σ : K ≃+* K) : MulAut (ActionRange K) :=
  ((imageAmbientTwist K σ).subgroupMap (ActionRange K)).trans
    (MulEquiv.subgroupCongr (actionRange_twist_map K σ))

theorem actionRangeTwist_val (K : Type) [Field K] (σ : K ≃+* K) (g : ActionRange K) :
    (actionRangeTwist K σ g).val = imageAmbientTwist K σ g.val := rfl

def matrixRangeProjection (K : Type) [Field K] : MatrixGroup K →* ActionRange K :=
  (matrixAction K).rangeRestrict

theorem matrixRangeProjection_surjective (K : Type) [Field K] :
    Function.Surjective (matrixRangeProjection K) := (matrixAction K).rangeRestrict_surjective

theorem matrixRangeProjection_twist (K : Type) [Field K] (σ : K ≃+* K) (g : MatrixGroup K) :
    matrixRangeProjection K (matrixGroupTwist K σ g) =
      actionRangeTwist K σ (matrixRangeProjection K g) := by
  apply Subtype.ext
  exact (matrix_action_covariance K σ g).symm

theorem source_action_range_le (K : Type) [Field K] :
    (imageRepresentation data K).range ≤ ActionRange K := by
  apply CFSGGeneratedActionRange.range_le_of_generators (rootSet (CartanMatrix.D 4) K)
    (rootSet_generate (CartanMatrix.D 4) K) (imageRepresentation data K) (ActionRange K)
  rintro g ⟨neg,i,t,rfl⟩
  exact ⟨canonicalElementaryRoot rawData K neg i t,(source_root_action K neg i t).symm⟩

def sourceRangeAction (K : Type) [Field K] : Model (CartanMatrix.D 4) K →* ActionRange K :=
  (imageRepresentation data K).codRestrict (ActionRange K)
    (fun g => source_action_range_le K ⟨g,rfl⟩)

def originalFixedRangeAction (q : CFSG.PrimePower) : Fixed q →* ActionRange (q.Extension 3) :=
  (sourceRangeAction (q.Extension 3)).comp
    (fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality (fun _ => q.order))

theorem originalFixedRangeAction_val (q : CFSG.PrimePower) (g : Fixed q) :
    (originalFixedRangeAction q g).val = fixedImageAction q g := rfl

theorem originalFixedRangeAction_fixed (q : CFSG.PrimePower) (g : Fixed q) :
    actionRangeTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (originalFixedRangeAction q g) = originalFixedRangeAction q g := by
  apply Subtype.ext
  exact original_fixed_action_twist q g

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckActionRangeTwist

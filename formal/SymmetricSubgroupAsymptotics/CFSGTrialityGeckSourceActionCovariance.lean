import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixActionCovariance
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalFixedSections

/-! The entire ORIGINAL D4 model action intertwines the actual
diagram-field image twist.  In particular genuine elements of the
pinned original fixed subgroup have twist-fixed actions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceActionCovariance
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreLocalNilpotence
open CFSGTrialityGeckImageSemilinearTwist CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMatrixActionCovariance CFSGSerreQuadraticMatrix CFSGSerreDiagram
open CFSGSerreOrdinaryTwists CFSGTrialityTripleFixedRoots CFSGSerreFixedRootElements
open CFSGTrialityGeckOriginalFixedSections

def sourceModelTwist (K : Type) [Field K] (σ : K ≃+* K) : MulAut (Model (CartanMatrix.D 4) K) :=
  CFSGSerreFieldDiagram.modelAutomorphism (CartanMatrix.D 4) K
    trialityPermutation triality_preserves σ

theorem sourceModelTwist_root (K : Type) [Field K] (σ : K ≃+* K)
    (neg : Bool) (i : Fin 4) (t : K) :
    sourceModelTwist K σ (modelRoot (CartanMatrix.D 4) K neg i t) =
      modelRoot (CartanMatrix.D 4) K neg (trialityPermutation i) (σ t) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact CFSGSerreFieldDiagram.ambientAutomorphism_isRootElement
    (CartanMatrix.D 4) K trialityPermutation triality_preserves σ neg i t
      (rootEquiv (CartanMatrix.D 4) K neg i t)
      (rootEquiv_isRootElement (CartanMatrix.D 4) K neg i t)

theorem source_action_covariance_hom (K : Type) [Field K] (σ : K ≃+* K) :
    (imageAmbientTwist K σ).toMonoidHom.comp (imageRepresentation data K) =
      (imageRepresentation data K).comp (sourceModelTwist K σ).toMonoidHom := by
  have hroot : Set.EqOn
      ((imageAmbientTwist K σ).toMonoidHom.comp (imageRepresentation data K))
      ((imageRepresentation data K).comp (sourceModelTwist K σ).toMonoidHom)
      (rootSet (CartanMatrix.D 4) K) := by
    rintro g ⟨neg,i,t,rfl⟩
    change imageAmbientTwist K σ (imageRepresentation data K (modelRoot (CartanMatrix.D 4) K neg i t)) =
      imageRepresentation data K (sourceModelTwist K σ (modelRoot (CartanMatrix.D 4) K neg i t))
    rw [sourceModelTwist_root,source_root_action,source_root_action,
      matrix_action_covariance,matrixGroupTwist_root]
  have htop := MonoidHom.eqOn_closure hroot
  rw [rootSet_generate] at htop
  exact MonoidHom.eq_of_eqOn_top htop

theorem source_action_covariance (K : Type) [Field K] (σ : K ≃+* K)
    (g : Model (CartanMatrix.D 4) K) :
    imageAmbientTwist K σ (imageRepresentation data K g) =
      imageRepresentation data K (sourceModelTwist K σ g) :=
  DFunLike.congr_fun (source_action_covariance_hom K σ) g

theorem original_fixed_model_twist (q : CFSG.PrimePower) (g : Fixed q) :
    sourceModelTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
        (fun _ => q.order) g) =
      fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
        (fun _ => q.order) g := by
  apply Subtype.ext
  have hg : (g.val,g.val) ∈ twistGraph (CartanMatrix.D 4) (q.Extension 3)
      CFSG.Models.triality (fun _ => q.order) := g.property.2
  exact ((triality_mem_twistGraph_iff q (g.val,g.val)).mp hg).2.symm

theorem original_fixed_action_twist (q : CFSG.PrimePower) (g : Fixed q) :
    imageAmbientTwist (q.Extension 3) (definingFieldAutomorphism q 3) (fixedImageAction q g) =
      fixedImageAction q g := by
  change imageAmbientTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (imageRepresentation data (q.Extension 3)
        (fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
          (fun _ => q.order) g)) = _
  rw [source_action_covariance,original_fixed_model_twist]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceActionCovariance

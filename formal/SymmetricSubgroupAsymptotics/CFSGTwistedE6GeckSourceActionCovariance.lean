import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMatrixActionCovariance
import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2

/-! The entire ORIGINAL E6 model action intertwines the actual
diagram-field image twist.  In particular genuine elements of the
pinned original fixed subgroup have twist-fixed actions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceActionCovariance
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreLocalNilpotence
open CFSGTwistedE6GeckImageSemilinearTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckMatrixActionCovariance CFSGSerreQuadraticMatrix CFSGSerreDiagram
open CFSGSerreOrdinaryTwists CFSGSerreFixedRootElements
open CFSGTwistedE6FixedA2

theorem matrixGroupTwist_root (K : Type) [Field K] (sigma : K≃+*K)
    (neg : Bool) (i : Fin 6) (t : K) :
    matrixGroupTwist K sigma (canonicalElementaryRoot rawData K neg i t)=
      canonicalElementaryRoot rawData K neg (e6Permutation i) (sigma t) := by
  apply Subtype.ext
  change unitTwist K sigma (canonicalRoot rawData K neg i t)=_
  exact unitTwist_root K sigma neg i t

def sourceModelTwist (K : Type) [Field K] (σ : K ≃+* K) : MulAut (Model CartanMatrix.E₆ K) :=
  CFSGSerreFieldDiagram.modelAutomorphism CartanMatrix.E₆ K
    e6Permutation e6_preserves σ

theorem sourceModelTwist_root (K : Type) [Field K] (σ : K ≃+* K)
    (neg : Bool) (i : Fin 6) (t : K) :
    sourceModelTwist K σ (modelRoot CartanMatrix.E₆ K neg i t) =
      modelRoot CartanMatrix.E₆ K neg (e6Permutation i) (σ t) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact CFSGSerreFieldDiagram.ambientAutomorphism_isRootElement
    CartanMatrix.E₆ K e6Permutation e6_preserves σ neg i t
      (rootEquiv CartanMatrix.E₆ K neg i t)
      (rootEquiv_isRootElement CartanMatrix.E₆ K neg i t)

theorem source_action_covariance_hom (K : Type) [Field K] (σ : K ≃+* K) :
    (imageAmbientTwist K σ).toMonoidHom.comp (imageRepresentation data K) =
      (imageRepresentation data K).comp (sourceModelTwist K σ).toMonoidHom := by
  have hroot : Set.EqOn
      ((imageAmbientTwist K σ).toMonoidHom.comp (imageRepresentation data K))
      ((imageRepresentation data K).comp (sourceModelTwist K σ).toMonoidHom)
      (rootSet CartanMatrix.E₆ K) := by
    rintro g ⟨neg,i,t,rfl⟩
    change imageAmbientTwist K σ (imageRepresentation data K (modelRoot CartanMatrix.E₆ K neg i t)) =
      imageRepresentation data K (sourceModelTwist K σ (modelRoot CartanMatrix.E₆ K neg i t))
    rw [sourceModelTwist_root,source_root_action,source_root_action,
      matrix_action_covariance,matrixGroupTwist_root]
  have htop := MonoidHom.eqOn_closure hroot
  rw [rootSet_generate] at htop
  exact MonoidHom.eq_of_eqOn_top htop

theorem source_action_covariance (K : Type) [Field K] (σ : K ≃+* K)
    (g : Model CartanMatrix.E₆ K) :
    imageAmbientTwist K σ (imageRepresentation data K g) =
      imageRepresentation data K (sourceModelTwist K σ g) :=
  DFunLike.congr_fun (source_action_covariance_hom K σ) g

theorem original_fixed_model_twist (q : CFSG.PrimePower) (g : Fixed q) :
    sourceModelTwist (q.Extension 2) (definingFieldAutomorphism q 2)
      (fixedToModel CartanMatrix.E₆ (q.Extension 2) CFSG.Models.e6Twist
        (fun _ => q.order) g) =
      fixedToModel CartanMatrix.E₆ (q.Extension 2) CFSG.Models.e6Twist
        (fun _ => q.order) g := by
  apply Subtype.ext
  have hg : (g.val,g.val) ∈ twistGraph CartanMatrix.E₆ (q.Extension 2)
      CFSG.Models.e6Twist (fun _ => q.order) := g.property.2
  exact ((e6_mem_twistGraph_iff q (g.val,g.val)).mp hg).2.symm

theorem original_fixed_action_twist (q : CFSG.PrimePower) (g : Fixed q) :
    imageAmbientTwist (q.Extension 2) (definingFieldAutomorphism q 2) (imageAction q g) =
      imageAction q g := by
  change imageAmbientTwist (q.Extension 2) (definingFieldAutomorphism q 2)
      (imageRepresentation data (q.Extension 2)
        (fixedToModel CartanMatrix.E₆ (q.Extension 2) CFSG.Models.e6Twist
          (fun _ => q.order) g)) = _
  rw [source_action_covariance,original_fixed_model_twist]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceActionCovariance

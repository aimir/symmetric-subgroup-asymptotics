import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFieldCovariance
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMatrixTwist
import SymmetricSubgroupAsymptotics.CFSGMatrixSemilinearImageTwist

/-! The literal E6 diagram--field intertwiner restricts to the SAME
original tensor image. Bijectivity uses the two actual source equivalences;
no surjectivity on fixed points is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckImageSemilinearTwist
open CFSG.Models.Chevalley CFSGSerreDiagram
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckFieldCovariance
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckMatrixTwist

local instance imageTwistInvPair (K : Type) [Field K] (sigma : K≃+*K) :
    RingHomInvPair sigma.toRingHom sigma.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv sigma
local instance imageTwistSymmInvPair (K : Type) [Field K] (sigma : K≃+*K) :
    RingHomInvPair sigma.symm.toRingHom sigma.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm sigma

def sourceTransform (K : Type) [Field K] (sigma : K≃+*K) :
    Space CartanMatrix.E₆ K→Space CartanMatrix.E₆ K := fun x =>
  spaceEquiv CartanMatrix.E₆ K e6Permutation e6_preserves
    (CFSGSerreField.semilinearEquiv CartanMatrix.E₆ K sigma x)

theorem sourceTransform_surjective (K : Type) [Field K] (sigma : K≃+*K) :
    Function.Surjective (sourceTransform K sigma) :=
  (spaceEquiv CartanMatrix.E₆ K e6Permutation e6_preserves).surjective.comp
    (CFSGSerreField.semilinearEquiv CartanMatrix.E₆ K sigma).surjective

theorem sourceTransform_covariance (K : Type) [Field K] (sigma : K≃+*K)
    (x : Space CartanMatrix.E₆ K) :
    CFSGSerreQuadraticMatrix.baseChange data K (sourceTransform K sigma x)=
      matrixTwist K sigma (CFSGSerreQuadraticMatrix.baseChange data K x) :=
  field_diagram_covariance K sigma x

abbrev imageSemilinearEquiv (K : Type) [Field K] (sigma : K≃+*K) :
    Image K≃ₛₗ[sigma.toRingHom]Image K :=
  CFSGMatrixSemilinearImageTwist.imageSemilinearEquiv
    (CFSGSerreQuadraticMatrix.baseChange data K) diagramIndex sigma
    (sourceTransform K sigma) (sourceTransform_surjective K sigma)
    (sourceTransform_covariance K sigma)

theorem imageSemilinearEquiv_val (K : Type) [Field K] (sigma : K≃+*K) (y : Image K) :
    (imageSemilinearEquiv K sigma y).val=matrixTwist K sigma y.val := rfl

abbrev imageAmbientTwist (K : Type) [Field K] (sigma : K≃+*K) :
    MulAut (Image K≃ₗ[K]Image K) :=
  CFSGMatrixSemilinearImageTwist.imageAmbientTwist
    (CFSGSerreQuadraticMatrix.baseChange data K) diagramIndex sigma
    (sourceTransform K sigma) (sourceTransform_surjective K sigma)
    (sourceTransform_covariance K sigma)

theorem imageAmbientTwist_apply (K : Type) [Field K] (sigma : K≃+*K)
    (g : Image K≃ₗ[K]Image K) (y : Image K) :
    imageAmbientTwist K sigma g y=imageSemilinearEquiv K sigma
      (g ((imageSemilinearEquiv K sigma).symm y)) := rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckImageSemilinearTwist

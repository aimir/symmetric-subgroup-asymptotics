import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceWordAction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFieldCovariance

/-! The actual diagram-field matrix twist restricts to a semilinear
equivalence of the SAME original integral image.  Range invariance is
proved from original tensor covariance and its inverse, not assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckImageSemilinearTwist
open CFSG.Models.Chevalley CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckFieldCovariance CFSGSerreQuadraticMatrix CFSGSerreDiagram

local instance imageTwistInvPair (K : Type) [Field K] (σ : K ≃+* K) :
    RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ

local instance imageTwistSymmInvPair (K : Type) [Field K] (σ : K ≃+* K) :
    RingHomInvPair σ.symm.toRingHom σ.toRingHom := RingHomInvPair.of_ringEquiv_symm σ

private theorem image_preserved (K : Type) [Field K] (σ : K ≃+* K)
    (y : Matrix GeckIndex GeckIndex K) (hy : y ∈ (baseChange data K).range) :
    matrixTwist K σ y ∈ (baseChange data K).range := by
  obtain ⟨x,rfl⟩ := hy
  refine ⟨spaceEquiv (CartanMatrix.D 4) K trialityPermutation triality_preserves
    (CFSGSerreField.semilinearEquiv (CartanMatrix.D 4) K σ x),?_⟩
  exact field_diagram_covariance K σ x

def imageSemilinearMap (K : Type) [Field K] (σ : K ≃+* K) :
    Image K →ₛₗ[σ.toRingHom] Image K where
  toFun y := ⟨matrixTwist K σ y.val,image_preserved K σ y.val y.property⟩
  map_add' x y := Subtype.ext (map_add (matrixTwist K σ) x.val y.val)
  map_smul' a y := by
    apply Subtype.ext
    ext i j
    change σ (a*y.val (trialityIndex.symm i) (trialityIndex.symm j)) =
      σ a * σ (y.val (trialityIndex.symm i) (trialityIndex.symm j))
    exact map_mul σ _ _

theorem imageSemilinearMap_val (K : Type) [Field K] (σ : K ≃+* K) (y : Image K) :
    (imageSemilinearMap K σ y).val = matrixTwist K σ y.val := rfl

theorem imageSemilinearMap_bijective (K : Type) [Field K] (σ : K ≃+* K) :
    Function.Bijective (imageSemilinearMap K σ) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact (matrixTwist K σ).injective (congrArg Subtype.val he)
  · rintro ⟨y,⟨x,rfl⟩⟩
    let p : Space (CartanMatrix.D 4) K :=
      (CFSGSerreField.semilinearEquiv (CartanMatrix.D 4) K σ).symm
        ((spaceEquiv (CartanMatrix.D 4) K trialityPermutation triality_preserves).symm x)
    refine ⟨(baseChange data K).rangeRestrict p,?_⟩
    apply Subtype.ext
    change matrixTwist K σ (baseChange data K p) = baseChange data K x
    have he := field_diagram_covariance K σ p
    have hp : spaceEquiv (CartanMatrix.D 4) K trialityPermutation triality_preserves
        (CFSGSerreField.semilinearEquiv (CartanMatrix.D 4) K σ p) = x := by
      dsimp only [p]
      rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    rw [hp] at he
    exact he.symm

def imageSemilinearEquiv (K : Type) [Field K] (σ : K ≃+* K) :
    Image K ≃ₛₗ[σ.toRingHom] Image K :=
  LinearEquiv.ofBijective (imageSemilinearMap K σ) (imageSemilinearMap_bijective K σ)

theorem imageSemilinearEquiv_val (K : Type) [Field K] (σ : K ≃+* K) (y : Image K) :
    (imageSemilinearEquiv K σ y).val = matrixTwist K σ y.val := rfl

def imageAmbientTwist (K : Type) [Field K] (σ : K ≃+* K) :
    MulAut (Image K ≃ₗ[K] Image K) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Image K)).symm.trans
    (LinearMap.GeneralLinearGroup.congrLinearEquiv (imageSemilinearEquiv K σ))).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Image K))

theorem imageAmbientTwist_apply (K : Type) [Field K] (σ : K ≃+* K)
    (g : Image K ≃ₗ[K] Image K) (y : Image K) :
    imageAmbientTwist K σ g y = imageSemilinearEquiv K σ
      (g ((imageSemilinearEquiv K σ).symm y)) := rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckImageSemilinearTwist

import SymmetricSubgroupAsymptotics.InvariantBilinearFormCentralizer
import SymmetricSubgroupAsymptotics.BilinearAdjointStarRing
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! The relative operator of two nondegenerate forms is an actual unit.
Symmetry makes it selfadjoint, common invariance retains the original
centralizer, and an actual isometry has adjoint equal to its inverse. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BilinearRelativeUnit
open InvariantBilinearFormCentralizer BilinearAdjointStarRing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)

def relativeUnit (C : LinearMap.BilinForm K V) (hC : C.Nondegenerate) :
    (Module.End K V)ˣ :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.ofBijective
    (operatorEquiv B hB C) ((nondegenerate_iff_bijective B hB C).mp hC))

theorem relativeUnit_val (C : LinearMap.BilinForm K V) (hC : C.Nondegenerate) :
    (relativeUnit B hB C hC : Module.End K V) = operatorEquiv B hB C := rfl

theorem relativeUnit_selfadjoint (hSymm : B.IsSymm)
    (C : LinearMap.BilinForm K V) (hC : C.Nondegenerate) (hCs : C.IsSymm) :
    letI := adjointStarRing B hB hSymm
    star (relativeUnit B hB C hC : Module.End K V) = relativeUnit B hB C hC := by
  letI := adjointStarRing B hB hSymm
  apply LinearMap.ext
  intro x
  apply (B.toDual hB).injective
  apply LinearMap.ext
  intro y
  change B (B.leftAdjointOfNondegenerate hB (operatorEquiv B hB C) x) y =
    B (operatorEquiv B hB C x) y
  calc
    _ = B x (operatorEquiv B hB C y) := adjoint_apply B hB _ x y
    _ = B (operatorEquiv B hB C y) x := hSymm.eq _ _
    _ = C y x := operatorEquiv_apply B hB C y x
    _ = C x y := hCs.eq _ _
    _ = _ := (operatorEquiv_apply B hB C x y).symm

theorem relativeUnit_commutes (C : LinearMap.BilinForm K V) (hC : C.Nondegenerate)
    (A : V ≃ₗ[K] V) (hA : ∀ x y : V, B (A x) (A y) = B x y)
    (hCA : ∀ x y : V, C (A x) (A y) = C x y) :
    Commute (relativeUnit B hB C hC : Module.End K V) A.toLinearMap :=
  (invariant_iff_commute B hB A hA C).mp hCA

theorem isometry_adjoint_inverse (hSymm : B.IsSymm)
    (A : V ≃ₗ[K] V) (hA : ∀ x y : V, B (A x) (A y) = B x y) :
    letI := adjointStarRing B hB hSymm
    star (LinearMap.GeneralLinearGroup.ofLinearEquiv A : Module.End K V) =
      (↑((LinearMap.GeneralLinearGroup.ofLinearEquiv A)⁻¹) : Module.End K V) := by
  letI := adjointStarRing B hB hSymm
  apply LinearMap.ext
  intro x
  apply (B.toDual hB).injective
  apply LinearMap.ext
  intro y
  change B (B.leftAdjointOfNondegenerate hB A.toLinearMap x) y = B (A.symm x) y
  calc
    _ = B x (A y) := adjoint_apply B hB _ x y
    _ = _ := by simpa only [A.apply_symm_apply] using hA (A.symm x) y

end SymmetricSubgroupAsymptotics.BilinearRelativeUnit

import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! The actual adjoint for a symmetric nondegenerate bilinear form
defines an involutive star ring on its endomorphisms. The algebra is
built from the checked unique adjoint, with no adjoint or norm axiom. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BilinearAdjointStarRing
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)

theorem adjoint_apply (T : Module.End K V) (x y : V) :
    B (B.leftAdjointOfNondegenerate hB T x) y = B x (T y) :=
  B.isAdjointPairLeftAdjointOfNondegenerate hB T x y

theorem adjoint_mul (S T : Module.End K V) :
    B.leftAdjointOfNondegenerate hB (S*T) =
      B.leftAdjointOfNondegenerate hB T * B.leftAdjointOfNondegenerate hB S := by
  apply LinearMap.ext
  intro x
  apply (B.toDual hB).injective
  apply LinearMap.ext
  intro y
  change B (B.leftAdjointOfNondegenerate hB (S*T) x) y =
    B (B.leftAdjointOfNondegenerate hB T (B.leftAdjointOfNondegenerate hB S x)) y
  rw [adjoint_apply, adjoint_apply, adjoint_apply]
  rfl

theorem adjoint_add (S T : Module.End K V) :
    B.leftAdjointOfNondegenerate hB (S+T) =
      B.leftAdjointOfNondegenerate hB S + B.leftAdjointOfNondegenerate hB T := by
  apply LinearMap.ext
  intro x
  apply (B.toDual hB).injective
  apply LinearMap.ext
  intro y
  change B (B.leftAdjointOfNondegenerate hB (S+T) x) y =
    B (B.leftAdjointOfNondegenerate hB S x+B.leftAdjointOfNondegenerate hB T x) y
  rw [adjoint_apply]
  change B x (S y+T y) =
    B (B.leftAdjointOfNondegenerate hB S x+B.leftAdjointOfNondegenerate hB T x) y
  rw [(B x).map_add, B.map_add, LinearMap.add_apply, adjoint_apply, adjoint_apply]

theorem adjoint_involutive (hSymm : B.IsSymm) :
    Function.Involutive (B.leftAdjointOfNondegenerate hB) := by
  intro T
  apply LinearMap.ext
  intro x
  apply (B.toDual hB).injective
  apply LinearMap.ext
  intro y
  change B (B.leftAdjointOfNondegenerate hB (B.leftAdjointOfNondegenerate hB T) x) y =
    B (T x) y
  calc
    _ = B x (B.leftAdjointOfNondegenerate hB T y) := adjoint_apply B hB _ x y
    _ = B (B.leftAdjointOfNondegenerate hB T y) x := hSymm.eq _ _
    _ = B y (T x) := adjoint_apply B hB T y x
    _ = _ := hSymm.eq _ _

abbrev adjointStarRing (hSymm : B.IsSymm) : StarRing (Module.End K V) where
  star := B.leftAdjointOfNondegenerate hB
  star_involutive := adjoint_involutive B hB hSymm
  star_mul := adjoint_mul B hB
  star_add := adjoint_add B hB

end SymmetricSubgroupAsymptotics.BilinearAdjointStarRing

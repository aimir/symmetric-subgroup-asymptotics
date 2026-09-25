import SymmetricSubgroupAsymptotics.MinimalNormalSubdirect
import SymmetricSubgroupAsymptotics.LocalChiefQuotientCoordinates
import SymmetricSubgroupAsymptotics.ChiefTernaryFiltration

/-! Nonabelian actual local chief factors install zero ternary steps.
Their original ambient-normal coordinate ranges are proved to vanish or
fill the local chief factor; proper subdirect pair cores are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A R : Type} [Group A] [Finite A] [Group R] [Finite R]
variable (N H : Subgroup A) [N.Normal] (θ : N→*R) (β : H→*R)
variable (hθ : ∀ (h:H) (n:N),θ (MulAut.conjNormal (h:A) n)=β h*θ n*(β h)⁻¹)
variable (hβ : Function.Surjective β)
variable (B L : Subgroup R) [B.Normal] [L.Normal]
variable (hmin : ∀ K : Subgroup (R⧸B),K.Normal → K≤normalChainQuotient B L →
  K=⊥ ∨ K=normalChainQuotient B L)
variable (hnc : ¬IsMulCommutative (normalChainQuotient B L))
include hθ hβ hmin hnc

theorem actualNonabelianChiefIntersection_perfect :
    Group.IsPerfect (localChiefSourceSection N θ B L) := by
  classical
  letI := Fintype.ofFinite A
  exact perfect_of_normal_coordinate_ranges (normalChainQuotient B L) hmin hnc
    (localChiefQuotientCoordinate N θ B L)
    (localChiefQuotientCoordinate_image_normal N θ B L H β hθ hβ)
    (localChiefQuotientCoordinates_separate N θ B L)

theorem actualNonabelianChiefIntersectionStep (hBL:B≤L) :
    TernaryChiefStep (localChiefIntersection N θ B) (localChiefIntersection N θ L) H 0 :=
  .perfect (localChiefIntersection_mono N θ hBL)
    (actualNonabelianChiefIntersection_perfect N H θ β hθ hβ B L hmin hnc)

end SymmetricSubgroupAsymptotics

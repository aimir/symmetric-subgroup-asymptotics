import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceCardinality
import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceLineIncidence

/-! An actual polar point/plane equivalence restricts on every original
singular subspace to a projective line-incidence equivalence. This is
derived from literal submodule maps, before choosing coordinates. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (B : LinearMap.BilinForm K V)

def projectiveInside (W : Subspaces B) : ℙ K W.val ≃ PointsInside B W :=
  (Projectivization.equivSubmodule K W.val).trans (pointsInsideEquiv B W).symm

theorem projectiveInside_submodule (W : Subspaces B) (p : ℙ K W.val) :
    (projectiveInside B W p).val.val=p.submodule.map W.val.subtype := rfl

theorem projectiveInside_line (W : Subspaces B) (p q r : ℙ K W.val) :
    (projectiveInside B W p).val.val ≤
      (projectiveInside B W q).val.val ⊔ (projectiveInside B W r).val.val ↔
      p.submodule ≤ q.submodule⊔r.submodule := by
  rw [projectiveInside_submodule,projectiveInside_submodule,projectiveInside_submodule,
    ←Submodule.map_sup]
  exact Submodule.map_le_map_iff_of_injective W.val.subtype_injective _ _

variable (f : Points B≃Points B) (l : Planes B≃Planes B)
    (hinc : ∀P L,(f P).val ≤ (l L).val ↔ P.val ≤ L.val)
    (horth : ∀P Q,ZeroOn B (f P).val (f Q).val ↔ ZeroOn B P.val Q.val)

def projectiveRestriction (W : Subspaces B) :
    ℙ K W.val ≃ ℙ K (imageSubspace B f l hinc horth W).val :=
  (projectiveInside B W).trans ((imagePointsEquiv B f l hinc horth W).trans
    (projectiveInside B (imageSubspace B f l hinc horth W)).symm)

theorem projectiveRestriction_point (W : Subspaces B) (p : ℙ K W.val) :
    (projectiveInside B (imageSubspace B f l hinc horth W)
      (projectiveRestriction B f l hinc horth W p)).val=
      f (projectiveInside B W p).val := by
  simp only [projectiveRestriction,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl

theorem projectiveRestriction_line (W : Subspaces B) (p q r : ℙ K W.val) :
    (projectiveRestriction B f l hinc horth W p).submodule ≤
      (projectiveRestriction B f l hinc horth W q).submodule ⊔
      (projectiveRestriction B f l hinc horth W r).submodule ↔
      p.submodule ≤ q.submodule⊔r.submodule := by
  rw [←projectiveInside_line B (imageSubspace B f l hinc horth W),
    projectiveRestriction_point,projectiveRestriction_point,projectiveRestriction_point]
  exact (preserves_point_join_incidence B f l hinc horth W
    (projectiveInside B W q).val (projectiveInside B W r).val (projectiveInside B W p).val
    (projectiveInside B W q).property (projectiveInside B W r).property).trans
      (projectiveInside_line B W p q r)

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints

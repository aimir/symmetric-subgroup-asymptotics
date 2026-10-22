import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspaceCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspaceLineIncidence

/-! The literal Q-singular point/plane map restricts to an actual
projective line-incidence equivalence on every Q-singular subspace. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

def projectiveInside (W : Subspaces Q) : ℙ K W.val ≃ PointsInside Q W :=
  (Projectivization.equivSubmodule K W.val).trans (pointsInsideEquiv Q W).symm

theorem projectiveInside_submodule (W : Subspaces Q) (p : ℙ K W.val) :
    (projectiveInside Q W p).val.val = p.submodule.map W.val.subtype := rfl

theorem projectiveInside_line (W : Subspaces Q) (p q r : ℙ K W.val) :
    (projectiveInside Q W p).val.val ≤
      (projectiveInside Q W q).val.val ⊔ (projectiveInside Q W r).val.val ↔
      p.submodule ≤ q.submodule ⊔ r.submodule := by
  rw [projectiveInside_submodule, projectiveInside_submodule, projectiveInside_submodule,
    ← Submodule.map_sup]
  exact Submodule.map_le_map_iff_of_injective W.val.subtype_injective _ _

variable (f : Points Q ≃ Points Q) (l : Planes Q ≃ Planes Q)
    (hinc : ∀ P L, (f P).val ≤ (l L).val ↔ P.val ≤ L.val)

def projectiveRestriction (W : Subspaces Q) :
    ℙ K W.val ≃ ℙ K (imageSubspace Q f l hinc W).val :=
  (projectiveInside Q W).trans ((imagePointsEquiv Q f l hinc W).trans
    (projectiveInside Q (imageSubspace Q f l hinc W)).symm)

theorem projectiveRestriction_point (W : Subspaces Q) (p : ℙ K W.val) :
    (projectiveInside Q (imageSubspace Q f l hinc W)
      (projectiveRestriction Q f l hinc W p)).val = f (projectiveInside Q W p).val := by
  simp only [projectiveRestriction, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem projectiveRestriction_line (W : Subspaces Q) (p q r : ℙ K W.val) :
    (projectiveRestriction Q f l hinc W p).submodule ≤
      (projectiveRestriction Q f l hinc W q).submodule ⊔
      (projectiveRestriction Q f l hinc W r).submodule ↔
      p.submodule ≤ q.submodule ⊔ r.submodule := by
  rw [← projectiveInside_line Q (imageSubspace Q f l hinc W),
    projectiveRestriction_point, projectiveRestriction_point, projectiveRestriction_point]
  exact (preserves_point_join_incidence Q f l hinc W
    (projectiveInside Q W q).val (projectiveInside Q W r).val (projectiveInside Q W p).val
    (projectiveInside Q W q).property (projectiveInside Q W r).property).trans
      (projectiveInside_line Q W p q r)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints

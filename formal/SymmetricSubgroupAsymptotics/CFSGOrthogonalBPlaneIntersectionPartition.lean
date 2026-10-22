import SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionPartition
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootPlaneAdjacency
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPlaneAction

/-! The exact original-carrier partition of distinct nonadjacent B
singular two-planes: disjoint, or meeting in a point with nonsingular sum.
No distance-two census or common-neighbour count is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBIntrinsicLongRoots
variable {K : Type} [Field K] [Finite K]

def IntersectingNonadjacent (s : ℕ) (P Q : SingularPlanes (K := K) s) : Prop :=
  Module.finrank K (P.val ⊓ Q.val : Submodule K (Index (s + 3) → K)) = 1 ∧
    ¬IsTotallySingular (K := K) s (P.val ⊔ Q.val)

theorem distinct_nonadjacent_partition (s : ℕ) (P Q : SingularPlanes (K := K) s)
    (hne : P ≠ Q) (hn : ¬PlaneAdjacent s P.val Q.val) :
    Disjoint P.val Q.val ∨ IntersectingNonadjacent s P Q := by
  have hpq : P.val ≠ Q.val := fun he => hne (Subtype.ext he)
  rcases CFSGTwoPlaneIntersectionPartition.disjoint_or_inf_finrank_eq_one
    P.val Q.val P.property.1 Q.property.1 hpq with hd | hi
  · exact Or.inl hd
  · exact Or.inr ⟨hi, fun hs => hn ⟨hpq, hi, hs⟩⟩

theorem intersectingNonadjacent_ne (s : ℕ) (P Q : SingularPlanes (K := K) s)
    (h : IntersectingNonadjacent s P Q) : P ≠ Q := by
  intro he
  subst Q
  exact h.2 (by simpa only [sup_idem] using P.property.2)

theorem intersectingNonadjacent_not_adjacent (s : ℕ) (P Q : SingularPlanes (K := K) s)
    (h : IntersectingNonadjacent s P Q) : ¬PlaneAdjacent s P.val Q.val :=
  fun ha => h.2 ha.2.2

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction

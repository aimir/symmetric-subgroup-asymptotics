import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPointOrthogonality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneActionFaithful

/-! The actual original projective D automorphism group acts faithfully
on the original quadratic singular points in ranks>=5, preserving
their polar relation. No automorphism lift, semilinear realization,
point-recognition callback or triality claim is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDSerreMatrices CFSGIncidenceStarReconstruction
variable (K : Type) [Field K]

def planeRelationAction [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ) :
    MulAut (elementaryProjective K (s + 5)) →*
      relationAut (IntersectingNonadjacent K (s + 1)) :=
  (singularActionHom K p (s + 1)).codRestrict _
    (fun f => singularAction_preserves_intersectingNonadjacent K p s f)

def polarPointAction (s : ℕ) : relationAut (IntersectingNonadjacent K (s + 1)) →*
    relationAut (PointOrthogonal K s) :=
  (pointAction (pointStarGeometry K s)).codRestrict _
    (fun f => pointStarAction_preserves_orthogonal K s f)

theorem polarPointAction_injective (s : ℕ) : Function.Injective (polarPointAction K s) := by
  intro f g h
  apply pointStarAction_injective K s
  exact congrArg Subtype.val h

def originalPointAction [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ) :
    MulAut (elementaryProjective K (s + 5)) →* relationAut (PointOrthogonal K s) :=
  (polarPointAction K s).comp (planeRelationAction K p s)

theorem originalPointAction_incidence [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : ℕ) (f : MulAut (elementaryProjective K (s + 5)))
    (U : SingularPoints K s) (P : SingularPlanes K (s + 1)) :
    ((originalPointAction K p s f).val U).val ≤ (singularActionHom K p (s + 1) f P).val ↔
      U.val ≤ P.val :=
  pointAction_incidence (pointStarGeometry K s) (planeRelationAction K p s f) U P

theorem originalPointAction_injective [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : ℕ) [IsSimpleGroup (elementaryProjective K (s + 5))] :
    Function.Injective (originalPointAction K p s) := by
  have hi : Function.Injective (planeRelationAction K p s) := by
    intro f g h
    apply singularActionHom_injective K p (s + 1)
    exact congrArg Subtype.val h
  exact (polarPointAction_injective K s).comp hi

theorem originalPointAction_preserves_orthogonal [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : ℕ) (f : MulAut (elementaryProjective K (s + 5))) (U V : SingularPoints K s) :
    PointOrthogonal K s ((originalPointAction K p s f).val U)
      ((originalPointAction K p s f).val V) ↔ PointOrthogonal K s U V :=
  (originalPointAction K p s f).property U V

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction

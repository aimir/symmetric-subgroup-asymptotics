import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointOrthogonality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntersectionRecognition

/-! The exact bridge from the explicit R11 common-neighbour count to
the actual original projective-group action on singular points. The
count remains an explicit local argument here; this adapter does not
claim the count or a semilinear/outer-automorphism bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGIncidenceStarReconstruction
variable {K : Type} [Field K] [Finite K]

def planeRelationActionOfCount (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ)
    (hlarge : ∀P Q : SingularPlanes (K:=K) s,IntersectingNonadjacent s P Q →
      intersectionRecognitionBound (K:=K) s<Nat.card (CommonNeighbours s P Q)) :
    MulAut (elementaryProjective K (s+3)) →* relationAut (IntersectingNonadjacent (K:=K) s) :=
  (singularActionHom p h2 s).codRestrict _
    (fun f=>singularAction_preserves_intersectingNonadjacent p h2 s hlarge f)

def polarPointAction (h2 : (2 : K) ≠ 0) (s : ℕ) :
    relationAut (IntersectingNonadjacent (K:=K) s) →*
      relationAut (PointOrthogonal (K:=K) s) :=
  (pointAction (pointStarGeometry h2 s)).codRestrict _
    (fun f=>pointStarAction_preserves_orthogonal h2 s f)

theorem polarPointAction_injective (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Function.Injective (polarPointAction (K:=K) h2 s) := by
  intro f g h
  apply pointStarAction_injective h2 s
  exact congrArg Subtype.val h

def originalPointActionOfCount (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ)
    (hlarge : ∀P Q : SingularPlanes (K:=K) s,IntersectingNonadjacent s P Q →
      intersectionRecognitionBound (K:=K) s<Nat.card (CommonNeighbours s P Q)) :
    MulAut (elementaryProjective K (s+3)) →* relationAut (PointOrthogonal (K:=K) s) :=
  (polarPointAction h2 s).comp (planeRelationActionOfCount p h2 s hlarge)

theorem originalPointActionOfCount_incidence (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ)
    (hlarge : ∀P Q : SingularPlanes (K:=K) s,IntersectingNonadjacent s P Q →
      intersectionRecognitionBound (K:=K) s<Nat.card (CommonNeighbours s P Q))
    (f : MulAut (elementaryProjective K (s+3)))
    (U : SingularPoints (K:=K) s) (P : SingularPlanes (K:=K) s) :
    ((originalPointActionOfCount p h2 s hlarge f).val U).val≤
      (singularActionHom p h2 s f P).val ↔ U.val≤P.val :=
  pointAction_incidence (pointStarGeometry h2 s) (planeRelationActionOfCount p h2 s hlarge f) U P

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction

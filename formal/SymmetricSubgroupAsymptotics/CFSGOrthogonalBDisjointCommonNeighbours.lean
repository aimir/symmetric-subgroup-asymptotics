import SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootPlaneAdjacency
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPlaneAction

/-! All disjoint original B singular planes have at most (q+1)^2
common Gamma01 neighbours. No R02/R12 classification or full group
recognition is used; the two actual intersection points determine R. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIntrinsicLongRoots
open CFSGTwoPlaneIntersectionCoordinates
variable {K : Type} [Field K] [Finite K]

abbrev CommonNeighbours (s : ℕ) (P Q : SingularPlanes (K := K) s) :=
  {R : SingularPlanes (K := K) s // PlaneAdjacent s P.val R.val ∧ PlaneAdjacent s Q.val R.val}

def commonNeighbourCrossing (s : ℕ) (P Q : SingularPlanes (K := K) s)
    (R : CommonNeighbours s P Q) : Crossing P.val Q.val :=
  ⟨R.val.val, R.val.property.1, R.property.1.2.1, R.property.2.2.1⟩

theorem commonNeighbourCrossing_injective (s : ℕ) (P Q : SingularPlanes (K := K) s) :
    Function.Injective (commonNeighbourCrossing s P Q) := by
  intro R S he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun T : Crossing P.val Q.val => T.val) he

theorem disjoint_common_neighbours_card_le (s : ℕ) (P Q : SingularPlanes (K := K) s)
    (hd : Disjoint P.val Q.val) :
    Nat.card (CommonNeighbours s P Q) ≤ (Nat.card K + 1) ^ 2 := by
  letI := crossing_finite P.val Q.val hd
  exact (Nat.card_le_card_of_injective (commonNeighbourCrossing s P Q)
    (commonNeighbourCrossing_injective s P Q)).trans
      (crossing_card_le P.val Q.val P.property.1 Q.property.1 hd)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction

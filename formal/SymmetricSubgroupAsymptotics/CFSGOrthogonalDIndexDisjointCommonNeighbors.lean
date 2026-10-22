import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualNeighborCount
import SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionCoordinates

/-! Disjoint original D two-planes have at most (q+1)^2 common
quadratic-adjacency neighbours. The two actual intersection points
determine each neighbour; no orthogonal-group recognition is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexDisjointCommonNeighbors
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexResidualNeighborCount
open CFSGTwoPlaneIntersectionCoordinates
variable (K : Type) [Field K] [Finite K]

def commonNeighborCrossing (r : ℕ) (P Q : Submodule K (Index r → K))
    (R : CommonNeighborPlanes K r P Q) : Crossing P Q :=
  ⟨R.val, R.property.1, R.property.2.2.1.2.1, R.property.2.2.2.2.1⟩

theorem commonNeighborCrossing_injective (r : ℕ) (P Q : Submodule K (Index r → K)) :
    Function.Injective (commonNeighborCrossing K r P Q) := by
  intro R S he
  exact Subtype.ext (congrArg (fun T : Crossing P Q => T.val) he)

theorem disjoint_common_neighbors_card_le (r : ℕ) (P Q : Submodule K (Index r → K))
    (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2) (hd : Disjoint P Q) :
    Nat.card (CommonNeighborPlanes K r P Q) ≤ (Nat.card K + 1) ^ 2 := by
  letI := crossing_finite P Q hd
  exact (Nat.card_le_card_of_injective (commonNeighborCrossing K r P Q)
    (commonNeighborCrossing_injective K r P Q)).trans (crossing_card_le P Q hP hQ hd)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexDisjointCommonNeighbors

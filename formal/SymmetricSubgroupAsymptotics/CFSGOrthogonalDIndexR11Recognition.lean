import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexR11LowerCount
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexDisjointCommonNeighbors
import SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionPartition

/-! For the actual original quadratic D plane geometry in rank>=5,
the R11 relation is recognized by nonadjacency and the proved common-
neighbour count. Rank four remains outside this theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexR11Recognition
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexResidualNeighborCount CFSGOrthogonalDIndexR11LowerCount
open CFSGOrthogonalDIndexDisjointCommonNeighbors CFSGTwoPlaneIntersectionPartition
variable (K : Type) [Field K] [Finite K]

theorem R11_iff_large_common_neighbors (s : ℕ)
    (P Q : Submodule K (Index (s + 5) → K))
    (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2)
    (hPs : ∀ x ∈ P, splitQuadraticForm K (s + 5) x = 0)
    (hQs : ∀ x ∈ Q, splitQuadraticForm K (s + 5) x = 0) :
    (Module.finrank K ↥(P ⊓ Q) = 1 ∧ ¬∀ x ∈ P ⊔ Q, splitQuadraticForm K (s + 5) x = 0) ↔
      (P ≠ Q ∧ ¬QuadraticAdjacent K (s + 5) P Q ∧
        (Nat.card K + 1) ^ 2 < Nat.card (CommonNeighborPlanes K (s + 5) P Q)) := by
  constructor
  · rintro ⟨hd, hn⟩
    have hne : P ≠ Q := by
      intro he
      rw [he, inf_idem, hQ] at hd
      omega
    exact ⟨hne, fun ha => hn ha.2.2,
      R11_common_neighbors_gt_disjoint_bound K s P Q hP hQ hPs hQs hd hn⟩
  · rintro ⟨hne, hn, hc⟩
    rcases disjoint_or_inf_finrank_eq_one P Q hP hQ hne with hd | hi
    · exact False.elim ((Nat.not_lt_of_ge (disjoint_common_neighbors_card_le K (s + 5) P Q hP hQ hd)) hc)
    · exact ⟨hi, fun hs => hn ⟨hne, hi, hs⟩⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexR11Recognition

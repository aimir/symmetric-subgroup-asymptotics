import SymmetricSubgroupAsymptotics.CFSGPolarCommonNeighbourUnique
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootPlaneAdjacency
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPlaneAction
import Mathlib.SetTheory.Cardinal.Finite

/-! The disjoint rank-one cross-pairing case has at most one common
Gamma01 neighbour on the SAME actual B singular two-planes. No finite
count/classification input or rank-three exclusion is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBIntrinsicLongRoots
variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
private theorem cross_of_adjacent (s : ℕ) (P R : Submodule K (Index (s + 3) → K))
    (h : PlaneAdjacent s P R) : ∀ p ∈ P, ∀ r ∈ R, (gram K (s + 3)).toBilin' p r = 0 := by
  have hP : P ≤ P ⊔ R := le_sup_left
  have hR : R ≤ P ⊔ R := le_sup_right
  intro p hp r hr
  exact h.2.2 p (hP hp) r (hR hr)

theorem at_most_one_common_neighbour (s : ℕ) (P Q R S : SingularPlanes (K := K) s)
    (hPQ : Disjoint P.val Q.val)
    (hPa : Module.finrank K (P.val ⊓ (gram K (s + 3)).toBilin'.orthogonal Q.val :
      Submodule K (Index (s + 3) → K)) = 1)
    (hQa : Module.finrank K (Q.val ⊓ (gram K (s + 3)).toBilin'.orthogonal P.val :
      Submodule K (Index (s + 3) → K)) = 1)
    (hPR : PlaneAdjacent s P.val R.val) (hQR : PlaneAdjacent s Q.val R.val)
    (hPS : PlaneAdjacent s P.val S.val) (hQS : PlaneAdjacent s Q.val S.val) : R = S := by
  apply Subtype.ext
  have hR := CFSGPolarCommonNeighbourUnique.common_neighbour_eq_forced_sum
    (gram K (s + 3)).toBilin' P.val Q.val R.val hPQ hPa hQa R.property.1
    hPR.2.1 hQR.2.1 (cross_of_adjacent s P.val R.val hPR) (cross_of_adjacent s Q.val R.val hQR)
  have hS := CFSGPolarCommonNeighbourUnique.common_neighbour_eq_forced_sum
    (gram K (s + 3)).toBilin' P.val Q.val S.val hPQ hPa hQa S.property.1
    hPS.2.1 hQS.2.1 (cross_of_adjacent s P.val S.val hPS) (cross_of_adjacent s Q.val S.val hQS)
  exact hR.trans hS.symm

theorem common_neighbours_subsingleton (s : ℕ) (P Q : SingularPlanes (K := K) s)
    (hPQ : Disjoint P.val Q.val)
    (hPa : Module.finrank K (P.val ⊓ (gram K (s + 3)).toBilin'.orthogonal Q.val :
      Submodule K (Index (s + 3) → K)) = 1)
    (hQa : Module.finrank K (Q.val ⊓ (gram K (s + 3)).toBilin'.orthogonal P.val :
      Submodule K (Index (s + 3) → K)) = 1) :
    Subsingleton {R : SingularPlanes (K := K) s //
      PlaneAdjacent s P.val R.val ∧ PlaneAdjacent s Q.val R.val} := by
  constructor
  intro R S
  apply Subtype.ext
  exact at_most_one_common_neighbour s P Q R.val S.val hPQ hPa hQa
    R.property.1 R.property.2 S.property.1 S.property.2

theorem common_neighbours_card_le_one (s : ℕ) (P Q : SingularPlanes (K := K) s)
    (hPQ : Disjoint P.val Q.val)
    (hPa : Module.finrank K (P.val ⊓ (gram K (s + 3)).toBilin'.orthogonal Q.val :
      Submodule K (Index (s + 3) → K)) = 1)
    (hQa : Module.finrank K (Q.val ⊓ (gram K (s + 3)).toBilin'.orthogonal P.val :
      Submodule K (Index (s + 3) → K)) = 1) :
    Nat.card {R : SingularPlanes (K := K) s //
      PlaneAdjacent s P.val R.val ∧ PlaneAdjacent s Q.val R.val} ≤ 1 := by
  letI := common_neighbours_subsingleton s P Q hPQ hPa hQa
  let f : {R : SingularPlanes (K := K) s //
    PlaneAdjacent s P.val R.val ∧ PlaneAdjacent s Q.val R.val} → Fin 1 := fun _ => 0
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction

import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualNeighborData

/-! A concrete q^4 lower bound for the actual normalized R11 common-
neighbour set in every split D rank>=5. Only a small explicit chart is
counted; no full singular-vector census or classical-group order occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualNeighborCount
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexResidualChart CFSGOrthogonalDIndexResidualPlaneFamily
open CFSGOrthogonalDIndexResidualNeighborData
variable (K : Type) [Field K]

def QuadraticAdjacent (r : ℕ) (P R : Submodule K (Index r → K)) : Prop :=
  P ≠ R ∧ Module.finrank K ↥(P ⊓ R) = 1 ∧ ∀ z ∈ P ⊔ R, splitQuadraticForm K r z = 0

def CommonNeighborPlanes (r : ℕ) (P Q : Submodule K (Index r → K)) : Type :=
  {R : Submodule K (Index r → K) // Module.finrank K R = 2 ∧
    (∀ z ∈ R, splitQuadraticForm K r z = 0) ∧ QuadraticAdjacent K r P R ∧ QuadraticAdjacent K r Q R}

instance orthogonalDCommonNeighborFinite [Finite K] (r : ℕ)
    (P Q : Submodule K (Index r → K)) : Finite (CommonNeighborPlanes K r P Q) :=
  Finite.of_injective (fun R : CommonNeighborPlanes K r P Q => (R.val : Set (Index r → K)))
    (fun R S he => Subtype.ext (SetLike.coe_injective he))

theorem fourth_power_le_normalized_common_neighbors [Finite K] (s : ℕ)
    (w : Index (s + 5) → K) (hws : splitQuadraticForm K (s + 5) w = 0)
    (hwu : (splitQuadraticForm K (s + 5)).polarBilin w (axis0 K s) = 0)
    (hw : (splitQuadraticForm K (s + 5)).polarBilin w (axis1 K s) ≠ 0) :
    Nat.card K ^ 4 ≤ Nat.card (CommonNeighborPlanes K (s + 5) (leftPlane K s) (rightPlane K s w)) := by
  let f : (Fin 4 → K) → CommonNeighborPlanes K (s + 5) (leftPlane K s) (rightPlane K s w) :=
    fun p => ⟨residualPlane K s w p, residualPlane_finrank K s w p,
      residualPlane_singular K s w p, residualPlane_common_neighbor_data K s w hws hwu hw p⟩
  have hi : Function.Injective f := by
    intro p q he
    exact residualPlane_injective K s w (congrArg Subtype.val he)
  calc
    Nat.card K ^ 4 = Nat.card (Fin 4 → K) := (parameter_card K).symm
    _ ≤ Nat.card (CommonNeighborPlanes K (s + 5) (leftPlane K s) (rightPlane K s w)) :=
      Nat.card_le_card_of_injective f hi

theorem normalized_common_neighbors_gt_disjoint_bound [Finite K] (s : ℕ)
    (w : Index (s + 5) → K) (hws : splitQuadraticForm K (s + 5) w = 0)
    (hwu : (splitQuadraticForm K (s + 5)).polarBilin w (axis0 K s) = 0)
    (hw : (splitQuadraticForm K (s + 5)).polarBilin w (axis1 K s) ≠ 0) :
    (Nat.card K + 1) ^ 2 <
      Nat.card (CommonNeighborPlanes K (s + 5) (leftPlane K s) (rightPlane K s w)) := by
  have htwo : 2 ≤ Nat.card K :=
    Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  exact (fourth_power_gt_disjoint_bound (Nat.card K) htwo).trans_le
    (fourth_power_le_normalized_common_neighbors K s w hws hwu hw)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualNeighborCount

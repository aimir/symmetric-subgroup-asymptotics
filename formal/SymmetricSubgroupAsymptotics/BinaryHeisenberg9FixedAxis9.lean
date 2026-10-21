import SymmetricSubgroupAsymptotics.BinaryHeisenbergCoordinateTemplate
import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds

/-! Selected K13 zero-axis sparse pilot. No original lift choice is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg9FixedAxis9
open BinaryHeisenbergEightNaturalHeads
open BinaryRegularEightNaturalRegistry (chart21 chart23)
def fixed : BinaryCoordinateSpace 8 2 :=
  binaryCoordinateSpaceOfMasks 8 2 (![102,153]) (![64,128]) (by decide +kernel)
def factorMasks : Fin 8 → ℕ := ![0,0,0,0,0,0,0,0]
def factor : (Fin 5 → Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) := {
  toFun := fun z i => ∑ j : Fin 5, ∑ k : Fin 8,
    (if (factorMasks i).testBit (8*j.val+k.val) then 1 else 0) * z j k
  map_add' := by intro x y; ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intro c x; ext i; simp [Finset.mul_sum, mul_left_comm] }

theorem complete_fixed (v : V) : v ∈ fixed.space ↔
    v ∈ chart21.space ∧ ∀ j, rho (generators j) v - v ∈ chart21.space := by
  apply binaryCoordinate_fixed_of_factor chart21 chart21 fixed rho generators factor
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem top_count : Fintype.card {i : Fin 32 // ∀ j : Fin 2,
    rho (BinaryEightOriginalRowActions.heisenbergRow i) (chart21.inclusion (Pi.single j 1)) -
      chart21.inclusion (Pi.single j 1) ∈ chart21.space} = 32 := by
  decide +kernel

theorem central_top_count : Fintype.card {i : Fin 32 //
    (BinaryHeisenbergTopCentralCore.PointEq (BinaryEightOriginalRowActions.heisenbergRow i) 1 ∨
     BinaryHeisenbergTopCentralCore.PointEq (BinaryEightOriginalRowActions.heisenbergRow i) BinaryHeisenbergTopCentralCore.z) ∧
    ∀ j : Fin 2,
      rho (BinaryEightOriginalRowActions.heisenbergRow i) (chart21.inclusion (Pi.single j 1)) -
        chart21.inclusion (Pi.single j 1) ∈ chart21.space} = 2 := by
  decide +kernel


theorem coordinate_envelope : BinaryHeisenbergCoordinateTemplate.JointAxisEnvelope
    chart21.space chart23.space chart21.space 2 := by
  have hf := BinaryHeisenbergCoordinateTemplate.fixed_card_le chart21 chart21 fixed complete_fixed
  have ht := BinaryHeisenbergCoordinateTemplate.top_card_le chart21 chart21 32 top_count
  have hz := BinaryHeisenbergCoordinateTemplate.central_top_card_le chart21 chart21 2 central_top_count
  have hi : chart23.space ≤ chart21.space := chart23.le_of_basis_mem _ (by decide +kernel)
  refine ⟨0, 1, ?_, ?_, by decide, by decide, ?_⟩
  · rw [inf_eq_right.mpr hi, chart23.card]
    decide
  · exact (Nat.mul_le_mul hf hz).trans (by rw [chart21.card]; decide)
  · exact Or.inl (chart23.le_of_basis_mem _ (by decide +kernel))

end SymmetricSubgroupAsymptotics.BinaryHeisenberg9FixedAxis9

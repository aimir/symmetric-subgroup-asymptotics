import SymmetricSubgroupAsymptotics.BinaryHeisenbergCoordinateTemplate
import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds

/-! Selected K13 zero-axis sparse pilot. No original lift choice is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg8FixedAxis6
open BinaryHeisenbergEightNaturalHeads
open BinaryRegularEightNaturalRegistry (chart13 chart46 chart40)
def fixed : BinaryCoordinateSpace 8 3 :=
  binaryCoordinateSpaceOfMasks 8 3 (![30,102,135]) (![16,64,128]) (by decide +kernel)
def factorMasks : Fin 8 → ℕ := ![274877906944,0,274877906944,274877906944,0,274877906944,0,0]
def factor : (Fin 5 → Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) := {
  toFun := fun z i => ∑ j : Fin 5, ∑ k : Fin 8,
    (if (factorMasks i).testBit (8*j.val+k.val) then 1 else 0) * z j k
  map_add' := by intro x y; ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intro c x; ext i; simp [Finset.mul_sum, mul_left_comm] }

theorem complete_fixed (v : V) : v ∈ fixed.space ↔
    v ∈ chart46.space ∧ ∀ j, rho (generators j) v - v ∈ chart13.space := by
  apply binaryCoordinate_fixed_of_factor chart46 chart13 fixed rho generators factor
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem top_count : Fintype.card {i : Fin 32 // ∀ j : Fin 4,
    rho (BinaryEightOriginalRowActions.heisenbergRow i) (chart46.inclusion (Pi.single j 1)) -
      chart46.inclusion (Pi.single j 1) ∈ chart13.space} = 16 := by
  decide +kernel

theorem central_top_count : Fintype.card {i : Fin 32 //
    (BinaryHeisenbergTopCentralCore.PointEq (BinaryEightOriginalRowActions.heisenbergRow i) 1 ∨
     BinaryHeisenbergTopCentralCore.PointEq (BinaryEightOriginalRowActions.heisenbergRow i) BinaryHeisenbergTopCentralCore.z) ∧
    ∀ j : Fin 4,
      rho (BinaryEightOriginalRowActions.heisenbergRow i) (chart46.inclusion (Pi.single j 1)) -
        chart46.inclusion (Pi.single j 1) ∈ chart13.space} = 2 := by
  decide +kernel


theorem coordinate_envelope : BinaryHeisenbergCoordinateTemplate.JointAxisEnvelope
    chart46.space chart40.space chart13.space 8 := by
  have hf := BinaryHeisenbergCoordinateTemplate.fixed_card_le chart46 chart13 fixed complete_fixed
  have ht := BinaryHeisenbergCoordinateTemplate.top_card_le chart46 chart13 16 top_count
  have hz := BinaryHeisenbergCoordinateTemplate.central_top_card_le chart46 chart13 2 central_top_count
  have hi : chart13.space ≤ chart40.space := chart13.le_of_basis_mem _ (by decide +kernel)
  refine ⟨1, 2, ?_, ?_, by decide, by decide, ?_⟩
  · rw [inf_eq_left.mpr hi, chart13.card]
    decide
  · exact (Nat.mul_le_mul hf hz).trans (by rw [chart13.card]; decide)
  · exact Or.inr ⟨4, (Nat.mul_le_mul hf ht).trans (by rw [chart13.card]; decide), by decide, by decide⟩

end SymmetricSubgroupAsymptotics.BinaryHeisenberg8FixedAxis6

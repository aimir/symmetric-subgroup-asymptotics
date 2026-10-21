import SymmetricSubgroupAsymptotics.BinaryHeisenbergCoordinateTemplate
import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds

/-! Selected K13 zero-axis sparse pilot. No original lift choice is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis7
open BinaryHeisenbergEightNaturalHeads
open BinaryRegularEightNaturalRegistry (chart15 chart1 chart45)
def fixed : BinaryCoordinateSpace 8 5 :=
  binaryCoordinateSpaceOfMasks 8 5 (![6,24,43,75,129]) (![4,16,32,64,128]) (by decide +kernel)
def factorMasks : Fin 8 → ℕ := ![67633152,17179869184,0,17246978048,0,0,0,0]
def factor : (Fin 5 → Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) := {
  toFun := fun z i => ∑ j : Fin 5, ∑ k : Fin 8,
    (if (factorMasks i).testBit (8*j.val+k.val) then 1 else 0) * z j k
  map_add' := by intro x y; ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intro c x; ext i; simp [Finset.mul_sum, mul_left_comm] }

theorem complete_fixed (v : V) : v ∈ fixed.space ↔
    v ∈ chart1.space ∧ ∀ j, rho (generators j) v - v ∈ chart15.space := by
  apply binaryCoordinate_fixed_of_factor chart1 chart15 fixed rho generators factor
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem top_count : Fintype.card {i : Fin 32 // ∀ j : Fin 8,
    rho (BinaryEightOriginalRowActions.heisenbergRow i) (chart1.inclusion (Pi.single j 1)) -
      chart1.inclusion (Pi.single j 1) ∈ chart15.space} = 1 := by
  decide +kernel

theorem central_top_count : Fintype.card {i : Fin 32 //
    (BinaryHeisenbergTopCentralCore.PointEq (BinaryEightOriginalRowActions.heisenbergRow i) 1 ∨
     BinaryHeisenbergTopCentralCore.PointEq (BinaryEightOriginalRowActions.heisenbergRow i) BinaryHeisenbergTopCentralCore.z) ∧
    ∀ j : Fin 8,
      rho (BinaryEightOriginalRowActions.heisenbergRow i) (chart1.inclusion (Pi.single j 1)) -
        chart1.inclusion (Pi.single j 1) ∈ chart15.space} = 1 := by
  decide +kernel


theorem coordinate_envelope : BinaryHeisenbergCoordinateTemplate.JointAxisEnvelope
    chart1.space chart45.space chart15.space 128 := by
  have hf := BinaryHeisenbergCoordinateTemplate.fixed_card_le chart1 chart15 fixed complete_fixed
  have ht := BinaryHeisenbergCoordinateTemplate.top_card_le chart1 chart15 1 top_count
  have hz := BinaryHeisenbergCoordinateTemplate.central_top_card_le chart1 chart15 1 central_top_count
  have hi : chart15.space ≤ chart45.space := chart15.le_of_basis_mem _ (by decide +kernel)
  refine ⟨3, 1, ?_, ?_, by decide, by decide, ?_⟩
  · rw [inf_eq_left.mpr hi, chart15.card]
    decide
  · exact (Nat.mul_le_mul hf hz).trans (by rw [chart15.card]; decide)
  · exact Or.inr ⟨0, (Nat.mul_le_mul hf ht).trans (by rw [chart15.card]; decide), by decide, by decide⟩

end SymmetricSubgroupAsymptotics.BinaryHeisenberg1FixedAxis7

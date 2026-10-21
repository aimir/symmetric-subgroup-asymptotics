import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds
import SymmetricSubgroupAsymptotics.BinaryRegularEightTopEnumeration
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedFactor

/-! Selected sparse pilot for the original regular-eight K25 action.
The complete fixed preimage modulo zero is certified on retained bases. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25Axis13Center
open BinaryRegularEightNaturalRegistry
def fixed : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (![30,45,75,135]) (![16,32,64,128]) (by decide +kernel)
def factorMasks : Fin 8 → ℕ := ![2097152,6291456,0,4194304,0,0,0,0]

def factor : (Fin 3 → Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) := {
  toFun := fun z i => ∑ j : Fin 3, ∑ k : Fin 8,
    (if (factorMasks i).testBit (8*j.val+k.val) then 1 else 0) * z j k
  map_add' := by intro x y; ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intro c x; ext i; simp [Finset.mul_sum, mul_left_comm] }
theorem complete_fixed (v : V) : v ∈ fixed.space ↔
    v ∈ chart25.space ∧ ∀ j, rho (generators j) v - v ∈ chart13.space := by
  apply binaryCoordinate_fixed_of_factor chart25 chart13 fixed rho generators factor
  · decide +kernel
  · decide +kernel
  · decide +kernel


theorem top_count : Fintype.card {i : Fin 8 // ∀ j : Fin 6,
    rho (groupElement i) (chart25.inclusion (Pi.single j 1)) -
      chart25.inclusion (Pi.single j 1) ∈ chart13.space} = 1 := by
  decide +kernel

theorem coordinate_capacity :
    Nat.card {v : V // v ∈ chart25.space ∧ ∀ t : H, rho t v-v ∈ chart13.space} *
      Nat.card {t : H // ∀ v, v ∈ chart25.space → rho t v-v ∈ chart13.space} ≤
      16 * Nat.card chart13.space := by
  have hf := BinaryCoordinateFixedTopCardBounds.fixed_card_le rho chart25 chart13 fixed generators complete_fixed
  have ht : Nat.card {t : H // ∀ v, v ∈ chart25.space → rho t v-v ∈ chart13.space} ≤ 1 := by
    simpa only [true_and] using
      BinaryCoordinateFixedTopCardBounds.top_card_le rho chart25 chart13 topRowEquiv (fun _ => True) 1
        (by simpa only [Nat.card_eq_fintype_card,true_and] using top_count)
  have hc := Nat.mul_le_mul hf ht
  exact hc.trans (by rw [chart13.card]; decide)

end SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25Axis13Center

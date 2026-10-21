import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds
import SymmetricSubgroupAsymptotics.BinaryRegularEightTopEnumeration
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedFactor

/-! Selected sparse pilot for the original regular-eight K24 action.
The complete fixed preimage modulo zero is certified on retained bases. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK24Axis22Center
open BinaryRegularEightNaturalRegistry
def fixed : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (![30,45,75,135]) (![16,32,64,128]) (by decide +kernel)
def factorMasks : Fin 8 → ℕ := ![2097152,1048576,3145728,0,0,0,0,0]

def factor : (Fin 3 → Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) := {
  toFun := fun z i => ∑ j : Fin 3, ∑ k : Fin 8,
    (if (factorMasks i).testBit (8*j.val+k.val) then 1 else 0) * z j k
  map_add' := by intro x y; ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intro c x; ext i; simp [Finset.mul_sum, mul_left_comm] }
theorem complete_fixed (v : V) : v ∈ fixed.space ↔
    v ∈ chart24.space ∧ ∀ j, rho (generators j) v - v ∈ chart22.space := by
  apply binaryCoordinate_fixed_of_factor chart24 chart22 fixed rho generators factor
  · decide +kernel
  · decide +kernel
  · decide +kernel


theorem top_count : Fintype.card {i : Fin 8 // ∀ j : Fin 6,
    rho (groupElement i) (chart24.inclusion (Pi.single j 1)) -
      chart24.inclusion (Pi.single j 1) ∈ chart22.space} = 4 := by
  decide +kernel

theorem coordinate_capacity :
    Nat.card {v : V // v ∈ chart24.space ∧ ∀ t : H, rho t v-v ∈ chart22.space} *
      Nat.card {t : H // ∀ v, v ∈ chart24.space → rho t v-v ∈ chart22.space} ≤
      16 * Nat.card chart22.space := by
  have hf := BinaryCoordinateFixedTopCardBounds.fixed_card_le rho chart24 chart22 fixed generators complete_fixed
  have ht : Nat.card {t : H // ∀ v, v ∈ chart24.space → rho t v-v ∈ chart22.space} ≤ 4 := by
    simpa only [true_and] using
      BinaryCoordinateFixedTopCardBounds.top_card_le rho chart24 chart22 topRowEquiv (fun _ => True) 4
        (by simpa only [Nat.card_eq_fintype_card,true_and] using top_count)
  have hc := Nat.mul_le_mul hf ht
  exact hc.trans (by rw [chart22.card]; decide)

end SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK24Axis22Center

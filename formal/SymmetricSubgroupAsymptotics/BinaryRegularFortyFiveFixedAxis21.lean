import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveCoordinateTemplate
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedFactor

/-! Selected sparse pilot for the original regular-eight K45 action.
The complete fixed preimage modulo zero is certified on retained bases. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis21
open BinaryRegularEightNaturalRegistry
def fixed : BinaryCoordinateSpace 8 4 :=
  binaryCoordinateSpaceOfMasks 8 4
    (![30,45,75,135]) (![16,32,64,128]) (by decide +kernel)
def factorMasks : Fin 8 → ℕ := ![2105344,4096,2101248,8192,0,0,0,0]

def factor : (Fin 3 → Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) := {
  toFun := fun z i => ∑ j : Fin 3, ∑ k : Fin 8,
    (if (factorMasks i).testBit (8*j.val+k.val) then 1 else 0) * z j k
  map_add' := by intro x y; ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intro c x; ext i; simp [Finset.mul_sum, mul_left_comm] }
theorem complete_fixed (v : V) : v ∈ fixed.space ↔
    v ∈ chart45.space ∧ ∀ j, rho (generators j) v - v ∈ chart21.space := by
  apply binaryCoordinate_fixed_of_factor chart45 chart21 fixed rho generators factor
  · decide +kernel
  · decide +kernel
  · decide +kernel


theorem top_count : Fintype.card {i : Fin 8 // ∀ j : Fin 7,
    rho (groupElement i) (chart45.inclusion (Pi.single j 1)) -
      chart45.inclusion (Pi.single j 1) ∈ chart21.space} = 1 := by
  decide +kernel

theorem coordinate_capacity :
    Nat.card {v : V // BinaryRegularFortyFiveCoordinateTemplate.fixedPredicate chart21 v} *
      Nat.card {t : H // BinaryRegularFortyFiveCoordinateTemplate.topPredicate chart21 t} ≤
      8 * Nat.card chart21.space := by
  have hf := BinaryRegularFortyFiveCoordinateTemplate.fixed_card_le chart21 fixed complete_fixed
  have ht := BinaryRegularFortyFiveCoordinateTemplate.top_card_le chart21 1
    (by rw [Nat.card_eq_fintype_card]; exact top_count)
  have hc := Nat.mul_le_mul hf ht
  exact hc.trans (by rw [chart21.card]; decide)

end SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis21

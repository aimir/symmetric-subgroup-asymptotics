import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14LinearRelations

/-! Literal binary linear generators for rows3/6/9. Their cyclic normal
subgroups are witnessed by two conjugation identities in the original
four-bit coordinates. No group or normal-subgroup census is used. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations

open BinaryFourProjectiveSpread
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev a3 := PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14LinearRelations.a12
abbrev a9 := a3

/-- Row6 generator one is the cyclic normal generator. -/
def a6 : LinearGroup where
  toFun v := ![v 2, v 0 + v 1, v 1 + v 3, v 0]
  invFun v := ![v 3, v 1 + v 3, v 0, v 1 + v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

/-- Row6 generator zero inverts one factor of the cyclic subgroup. -/
def b6 : LinearGroup where
  toFun v := ![v 0, v 0 + v 2, v 0 + v 1, v 0 + v 3]
  invFun v := ![v 0, v 0 + v 2, v 0 + v 1, v 0 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def b9 : LinearGroup where
  toFun v := ![v 0 + v 1, v 0 + v 2, v 0, v 0 + v 1 + v 3]
  invFun v := ![v 2, v 0 + v 2, v 1 + v 2, v 3 + v 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

theorem a3_original : BinaryFourAffineImage.linearPerm a3 =
    DegreeTwoPrimitiveSixteenInterfaces.row3Generators 0 := by
  apply Equiv.ext; intro x; revert x; decide +kernel
theorem a6_original : BinaryFourAffineImage.linearPerm a6 =
    DegreeTwoPrimitiveSixteenInterfaces.row6Generators 1 := by
  apply Equiv.ext; intro x; revert x; decide +kernel
theorem b6_original : BinaryFourAffineImage.linearPerm b6 =
    DegreeTwoPrimitiveSixteenInterfaces.row6Generators 0 := by
  apply Equiv.ext; intro x; revert x; decide +kernel
theorem a9_original : BinaryFourAffineImage.linearPerm a9 =
    DegreeTwoPrimitiveSixteenInterfaces.row9Generators 0 := by
  apply Equiv.ext; intro x; revert x; decide +kernel
theorem b9_original : BinaryFourAffineImage.linearPerm b9 =
    DegreeTwoPrimitiveSixteenInterfaces.row9Generators 1 := by
  apply Equiv.ext; intro x; revert x; decide +kernel

theorem b6_conj_a6 : b6 * a6 * b6⁻¹ = a6 ^ 4 := by
  apply LinearEquiv.ext; intro v; revert v; decide +kernel
theorem b6_inv_conj_a6 : b6⁻¹ * a6 * b6 = a6 ^ 4 := by
  apply LinearEquiv.ext; intro v; revert v; decide +kernel
theorem b9_conj_a9 : b9 * a9 * b9⁻¹ = a9 ^ 2 := by
  apply LinearEquiv.ext; intro v; revert v; decide +kernel
theorem b9_inv_conj_a9 : b9⁻¹ * a9 * b9 = a9 ^ 8 := by
  apply LinearEquiv.ext; intro v; revert v; decide +kernel

theorem a3_orbit : ∀ x : Vector, x ≠ 0 → ∀ y : Vector, y ≠ 0 →
    ∃ k : Fin 15, (a3 ^ k.val) x = y :=
  PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14LinearRelations.a12_orbit

theorem a6_orbit : ∀ x : Vector, x ≠ 0 → ∀ y : Vector, y ≠ 0 →
    ∃ k : Fin 15, (a6 ^ k.val) x = y := by decide +kernel

end PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations
end SymmetricSubgroupAsymptotics

end

import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles

/-!
# Shared literal linear relations for primitive-sixteen rows eight and ten

The two order-three generators are commuting tensor factors. The row-ten
involutions invert one factor and interchange the factors. Their product
is exactly row eight's third generator. All comparisons below concern
the actual four-bit linear maps and original sixteen-point permutations.

This file supplies action relations, not a quotient-socle conclusion.
The affine-model range and irreducibility bindings remain separate work.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10LinearRelations

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Vector := AffineModel.V 2 4
abbrev LinearGroup := AffineModel.GLV 2 4
abbrev linearPerm := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearPerm

def a : LinearGroup where
  toFun v := ![v 0 + v 1, v 0, v 2 + v 3, v 2]
  invFun v := ![v 1, v 0 + v 1, v 3, v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def b : LinearGroup where
  toFun v := ![v 0 + v 2, v 1 + v 3, v 0, v 1]
  invFun v := ![v 2, v 3, v 0 + v 2, v 1 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def s : LinearGroup where
  toFun v := ![v 0, v 1, v 0 + v 2, v 1 + v 3]
  invFun v := ![v 0, v 1, v 0 + v 2, v 1 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def t : LinearGroup where
  toFun v := ![v 0, v 2, v 1, v 3]
  invFun v := ![v 0, v 2, v 1, v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def c : LinearGroup := t * s

theorem a_cube : a ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem b_cube : b ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem a_b_commute : a * b = b * a := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem s_square : s ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem t_square : t ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem c_fourth : c ^ 4 = 1 := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem s_conj_a : s * a * s⁻¹ = a := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem s_conj_b : s * b * s⁻¹ = b⁻¹ := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem t_conj_a : t * a * t⁻¹ = b := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem t_conj_b : t * b * t⁻¹ = a := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem c_conj_a : c * a * c⁻¹ = b := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem c_conj_b : c * b * c⁻¹ = a⁻¹ := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem linearPerm_a_row8 :
    linearPerm a = DegreeTwoPrimitiveSixteenInterfaces.row8Generators 0 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem linearPerm_b_row8 :
    linearPerm b = DegreeTwoPrimitiveSixteenInterfaces.row8Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem linearPerm_c_row8 :
    linearPerm c = DegreeTwoPrimitiveSixteenInterfaces.row8Generators 2 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem linearPerm_a_row10 :
    linearPerm a = DegreeTwoPrimitiveSixteenInterfaces.row10Generators 0 :=
  linearPerm_a_row8

theorem linearPerm_b_row10 :
    linearPerm b = DegreeTwoPrimitiveSixteenInterfaces.row10Generators 1 :=
  linearPerm_b_row8

theorem linearPerm_s_row10 :
    linearPerm s = DegreeTwoPrimitiveSixteenInterfaces.row10Generators 2 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem linearPerm_t_row10 :
    linearPerm t = DegreeTwoPrimitiveSixteenInterfaces.row10Generators 3 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

/-- The retained row-eight generator is this exact word in row ten. -/
theorem row8_third_eq_row10_word :
    DegreeTwoPrimitiveSixteenInterfaces.row8Generators 2 =
      DegreeTwoPrimitiveSixteenInterfaces.row10Generators 3 *
        DegreeTwoPrimitiveSixteenInterfaces.row10Generators 2 := by
  rw [← linearPerm_c_row8, c, map_mul, linearPerm_t_row10, linearPerm_s_row10]

theorem row8_le_row10 : DegreeTwoPrimitiveSixteenInterfaces.row8.top ≤
    DegreeTwoPrimitiveSixteenInterfaces.row10.top := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨1, rfl⟩
  · change DegreeTwoPrimitiveSixteenInterfaces.row8Generators 2 ∈ _
    rw [row8_third_eq_row10_word]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_range_self 3))
      (Subgroup.subset_closure (Set.mem_range_self 2))
  · exact Subgroup.subset_closure ⟨4, rfl⟩

end PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10LinearRelations
end SymmetricSubgroupAsymptotics

end

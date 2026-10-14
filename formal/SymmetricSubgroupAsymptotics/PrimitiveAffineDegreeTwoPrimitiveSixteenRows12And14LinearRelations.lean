import SymmetricSubgroupAsymptotics.BinaryFourProjectiveSpread
import SymmetricSubgroupAsymptotics.BinaryFiveFrameRepresentation
import SymmetricSubgroupAsymptotics.AlternatingGeneratorBridge

/-! Exact original linear maps and projective spread charts for rows12/14.
Only the displayed four-bit actions and their five-label images are checked.
The first generator in each row cycles all fifteen nonzero vectors. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14LinearRelations

open BinaryFourProjectiveSpread
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev alpha := BinaryFiveFrameRepresentation.cycle
def beta12 : Equiv.Perm (Fin 5) := Equiv.swap 3 4
def beta14 : Equiv.Perm (Fin 5) :=
  alpha⁻¹ * BinaryFiveFrameRepresentation.transposition * alpha *
    BinaryFiveFrameRepresentation.transposition

/-- Columns [1,6,9,3] put the row12 planes in the canonical label order. -/
def chart12 : LinearGroup where
  toFun v := ![v 0 + v 2 + v 3, v 1 + v 3, v 1, v 2]
  invFun v := ![v 0 + v 1 + v 2 + v 3, v 2, v 3, v 1 + v 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

/-- Columns [1,12,6,5] give the same five projective labels for row14. -/
def chart14 : LinearGroup where
  toFun v := ![v 0 + v 3, v 2, v 1 + v 2 + v 3, v 1]
  invFun v := ![v 0 + v 1 + v 2 + v 3, v 3, v 1, v 1 + v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def a12 : LinearGroup where
  toFun v := ![v 0 + v 1, v 2, v 3, v 0]
  invFun v := ![v 3, v 0 + v 3, v 1, v 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def b12 : LinearGroup where
  toFun v := ![v 0 + v 1, v 1, v 2, v 1 + v 2 + v 3]
  invFun v := ![v 0 + v 1, v 1, v 2, v 1 + v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def a14 : LinearGroup where
  toFun v := ![v 1 + v 2, v 0 + v 1, v 0 + v 1 + v 3, v 1]
  invFun v := ![v 1 + v 3, v 3, v 0 + v 3, v 1 + v 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def b14 : LinearGroup where
  toFun v := ![v 0 + v 2, v 1 + v 3, v 0, v 1]
  invFun v := ![v 2, v 3, v 0 + v 2, v 1 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

theorem a12_original : BinaryFourAffineImage.linearPerm a12 =
    DegreeTwoPrimitiveSixteenInterfaces.row12Generators 0 := by
  apply Equiv.ext; intro x; revert x; decide +kernel
theorem b12_original : BinaryFourAffineImage.linearPerm b12 =
    DegreeTwoPrimitiveSixteenInterfaces.row12Generators 1 := by
  apply Equiv.ext; intro x; revert x; decide +kernel
theorem a14_original : BinaryFourAffineImage.linearPerm a14 =
    DegreeTwoPrimitiveSixteenInterfaces.row14Generators 0 := by
  apply Equiv.ext; intro x; revert x; decide +kernel
theorem b14_original : BinaryFourAffineImage.linearPerm b14 =
    DegreeTwoPrimitiveSixteenInterfaces.row14Generators 1 := by
  apply Equiv.ext; intro x; revert x; decide +kernel

theorem a12_spread : ∀ i, planeAction a12 (spread chart12 i) = spread chart12 (alpha i) := by
  decide +kernel
theorem b12_spread : ∀ i, planeAction b12 (spread chart12 i) = spread chart12 (beta12 i) := by
  decide +kernel
theorem a14_spread : ∀ i, planeAction a14 (spread chart14 i) = spread chart14 (alpha i) := by
  decide +kernel
theorem b14_spread : ∀ i, planeAction b14 (spread chart14 i) = spread chart14 (beta14 i) := by
  decide +kernel

theorem a12_orbit : ∀ x : Vector, x ≠ 0 → ∀ y : Vector, y ≠ 0 →
    ∃ k : Fin 15, (a12 ^ k.val) x = y := by decide +kernel

theorem a14_orbit : ∀ x : Vector, x ≠ 0 → ∀ y : Vector, y ≠ 0 →
    ∃ k : Fin 15, (a14 ^ k.val) x = y := by decide +kernel

/-- A transitive nonzero cyclic orbit proves irreducibility of any actual
linear subgroup containing that generator. -/
theorem irreducible_of_nonzero_orbit (R : Subgroup LinearGroup)
    (a : LinearGroup) (ha : a ∈ R) {n : ℕ}
    (horbit : ∀ x : Vector, x ≠ 0 → ∀ y : Vector, y ≠ 0 →
      ∃ k : Fin n, (a ^ k.val) x = y) : AffineModel.Irreducible R := by
  intro S hS
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  have hx : ∃ x ∈ S, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hbot
    apply le_antisymm _ bot_le
    intro x hx
    exact AddSubgroup.mem_bot.mpr (h x hx)
  obtain ⟨x, hx, hx0⟩ := hx
  apply top_unique
  intro y _hy
  by_cases hy0 : y = 0
  · rw [hy0]; exact S.zero_mem
  obtain ⟨k, hk⟩ := horbit x hx0 y hy0
  rw [← hk]
  exact hS (a ^ k.val) (R.pow_mem ha k.val) x hx

theorem symmetric_generators :
    Subgroup.closure ({alpha, beta12} : Set (Equiv.Perm (Fin 5))) = ⊤ := by
  simpa only [show finRotate 5 (3 : Fin 5) = 4 from rfl] using
    Equiv.Perm.closure_cycle_adjacent_swap
      (isCycle_finRotate_of_le (by decide : 2 ≤ 5))
      (support_finRotate_of_le (by decide : 2 ≤ 5)) (3 : Fin 5)

theorem alpha_even : alpha ∈ alternatingGroup (Fin 5) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  norm_num [BinaryFiveFrameRepresentation.cycle, sign_finRotate]

theorem alternating_generators :
    Subgroup.closure ({alpha, beta14} : Set (Equiv.Perm (Fin 5))) = alternatingGroup (Fin 5) := by
  apply involutionCommutatorClosure_eq_alternating (by norm_num)
    alpha BinaryFiveFrameRepresentation.transposition (Equiv.swap_inv _ _)
  · simpa only [show finRotate 5 (0 : Fin 5) = 1 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide : 2 ≤ 5))
        (support_finRotate_of_le (by decide : 2 ≤ 5)) (0 : Fin 5)
  · exact alpha_even
  · intro h
    have hh := congrArg (fun p : Equiv.Perm (Fin 5) => p 0) h
    change (1 : Fin 5) = 0 at hh
    exact (by decide : (1 : Fin 5) ≠ 0) hh

theorem beta14_even : beta14 ∈ alternatingGroup (Fin 5) := by
  rw [← alternating_generators]
  exact Subgroup.subset_closure (by simp)

end PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14LinearRelations
end SymmetricSubgroupAsymptotics

end

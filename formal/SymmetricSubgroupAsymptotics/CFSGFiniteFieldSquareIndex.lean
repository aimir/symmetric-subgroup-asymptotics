import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The actual square subgroup of the finite field's unit group has
index at most two. No order/model-identification input is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareIndex

theorem squares_index_le_two (K : Type*) [Field K] [Finite K] :
    (powMonoidHom 2 : Kˣ →* Kˣ).range.index ≤ 2 := by
  letI : Fintype K := Fintype.ofFinite K
  rw [IsCyclic.index_powMonoidHom_range]
  exact Nat.gcd_le_right _ (by decide)

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareIndex

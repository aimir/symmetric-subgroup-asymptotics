import SymmetricSubgroupAsymptotics.GeneralThreeTwoRowGenerators
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Push

/-! One selected actual matrix generator of the checked order-twenty-one
complement acts cyclically on the seven nonzero binary vectors. Its
irreducibility follows from this literal action, not a freely supplied
extension-field scalar structure. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoTwentyOneSinger

abbrev Vector := Fin 3 → ZMod 2

def singer : GeneralThreeTwoMatrixEncoding.Ambient :=
  GeneralThreeTwoRowGenerators.generators 14 0

def operator (v : Vector) : Vector := singer.val *ᵥ v

/-- The sole finite pilot concerns eight literal vectors and the first
seven iterates of one specified matrix. -/
theorem nonzero_orbit : ∀ x y : Vector, x ≠ 0 → y ≠ 0 →
    ∃ j : Fin 7, (operator^[j.val]) x = y := by
  decide +kernel

theorem invariantAddSubgroup_eq_bot_or_top (S : AddSubgroup Vector)
    (hstable : ∀ v ∈ S, operator v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  have hx : ∃ x ∈ S, x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hbot
    apply le_antisymm ?_ bot_le
    intro x hx
    exact AddSubgroup.mem_bot.mpr (h x hx)
  obtain ⟨x,hx,hx0⟩ := hx
  have hiter : ∀ n : ℕ, ∀ v ∈ S, (operator^[n]) v ∈ S := by
    intro n
    induction n with
    | zero =>
      intro v hv
      exact hv
    | succ n ih =>
      intro v hv
      rw [Function.iterate_succ_apply']
      exact hstable _ (ih v hv)
  apply top_le_iff.mp
  intro y _
  by_cases hy0 : y = 0
  · simpa only [hy0] using S.zero_mem
  obtain ⟨j,hj⟩ := nonzero_orbit x y hx0 hy0
  rw [← hj]
  exact hiter j.val x hx

end SymmetricSubgroupAsymptotics.GeneralThreeTwoTwentyOneSinger

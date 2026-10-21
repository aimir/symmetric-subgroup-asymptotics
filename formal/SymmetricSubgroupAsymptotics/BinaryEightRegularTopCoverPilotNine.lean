import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T3
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T9

/-! One bounded literal subgroup-cover pilot. Only three generator
identities on eight original points are reflected. This does not assert
coverage of other transitive tops or normality of the regular subgroup. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightRegularTopCoverPilotNine

private def firstThree (j : Fin 3) : Fin 4 :=
  ⟨j.val, Nat.lt_trans j.isLt (by decide : 3 < 4)⟩

private theorem generator_binding : ∀ j : Fin 3,
    BinaryMenuCayley8T3.generators j = BinaryMenuCayley8T9.generators (firstThree j) := by
  decide +kernel

/-- The SAME literal regular-eight subgroup occurs in the original 8T9
point action. No abstract group-order substitute is used. -/
theorem regular_le :
    Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) ≤
      Subgroup.closure (Set.range BinaryMenuCayley8T9.generators) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  rw [generator_binding j]
  exact Subgroup.subset_closure ⟨firstThree j, rfl⟩

end SymmetricSubgroupAsymptotics.BinaryEightRegularTopCoverPilotNine

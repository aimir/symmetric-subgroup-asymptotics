import SymmetricSubgroupAsymptotics.BinaryEightRegularTopCoverPilotNine
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T18
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T19
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T29

/-! Three further exact original-point inclusions after the selected9
pilot. Every proof binds only the three literal regular generators.
No assertion is made for11/21/30/31 or for all transitive eight-point tops. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightRegularTopCoverDirect

private theorem closure_le_of_generator_binding
    {G : Type} [Group G] {ι κ : Type} (a : ι → G) (b : κ → G)
    (f : ι → κ) (h : ∀ j, a j = b (f j)) :
    Subgroup.closure (Set.range a) ≤ Subgroup.closure (Set.range b) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  rw [h j]
  exact Subgroup.subset_closure ⟨f j, rfl⟩

private def firstThreeFour (j : Fin 3) : Fin 4 :=
  ⟨j.val, Nat.lt_trans j.isLt (by decide : 3 < 4)⟩
private def firstThreeFive (j : Fin 3) : Fin 5 :=
  ⟨j.val, Nat.lt_trans j.isLt (by decide : 3 < 5)⟩

/-- Literal E8 is contained in the original18 action. -/
theorem regular_le_eighteen :
    Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) ≤
      Subgroup.closure (Set.range BinaryMenuCayley8T18.generators) :=
  closure_le_of_generator_binding _ _ firstThreeFive (by decide +kernel)

/-- Literal E8 is contained in the original19 action. -/
theorem regular_le_nineteen :
    Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) ≤
      Subgroup.closure (Set.range BinaryMenuCayley8T19.generators) :=
  closure_le_of_generator_binding _ _ firstThreeFour (by decide +kernel)

/-- Literal E8 is contained in the original29 action. -/
theorem regular_le_twentyNine :
    Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) ≤
      Subgroup.closure (Set.range BinaryMenuCayley8T29.generators) :=
  closure_le_of_generator_binding _ _ firstThreeFive (by decide +kernel)

end SymmetricSubgroupAsymptotics.BinaryEightRegularTopCoverDirect

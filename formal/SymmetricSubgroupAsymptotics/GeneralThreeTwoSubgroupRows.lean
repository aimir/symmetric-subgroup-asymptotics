import SymmetricSubgroupAsymptotics.GeneralThreeTwoCayley
import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionWords

/-! Fifteen literal subgroups in the selected actual GL(3,2) row model.
Local adjunction equations, proved separately, establish their coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupRows
open GeneralThreeTwoCayley
local instance : Group Source := group
def generators (i : Fin 15) (j : Fin 3) : Source :=
  ((if i.val < 7 then (if i.val < 3 then (if i.val < 1 then ![⟨76⟩, ⟨76⟩, ⟨76⟩] else (if i.val < 2 then ![⟨0⟩, ⟨76⟩, ⟨76⟩] else ![⟨102⟩, ⟨76⟩, ⟨76⟩])) else (if i.val < 5 then (if i.val < 4 then ![⟨71⟩, ⟨76⟩, ⟨76⟩] else ![⟨6⟩, ⟨76⟩, ⟨76⟩]) else (if i.val < 6 then ![⟨102⟩, ⟨0⟩, ⟨76⟩] else ![⟨52⟩, ⟨0⟩, ⟨76⟩]))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then ![⟨66⟩, ⟨0⟩, ⟨76⟩] else ![⟨94⟩, ⟨104⟩, ⟨76⟩]) else (if i.val < 10 then ![⟨62⟩, ⟨0⟩, ⟨76⟩] else ![⟨22⟩, ⟨0⟩, ⟨76⟩])) else (if i.val < 13 then (if i.val < 12 then ![⟨126⟩, ⟨148⟩, ⟨76⟩] else ![⟨164⟩, ⟨0⟩, ⟨76⟩]) else (if i.val < 14 then ![⟨54⟩, ⟨0⟩, ⟨76⟩] else ![⟨161⟩, ⟨102⟩, ⟨76⟩]))))) j

def rows (i : Fin 15) : Subgroup Source :=
  Subgroup.closure (Set.range (generators i))

theorem row_zero : rows 0 = ⊥ := by
  apply le_antisymm _ bot_le
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  change generators 0 j = 1
  fin_cases j <;> decide +kernel

end SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupRows
end
